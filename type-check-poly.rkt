#lang racket
(require "utilities.rkt")
(require "type-check-Lwhile.rkt")

(provide type-check-poly type-check-poly-class)

(define type-check-poly-class
  (class type-check-Lwhile-class
    (super-new)
    (inherit check-type-equal?)

    ;; This is slow. Should instead convert to de Bruijn
    ;; or add a parameter for the environment. -Jeremy
    (define/override (type-equal? t1 t2)
      (match* (t1 t2)
        ;; 处理泛型的定义
        [(`(All ,xs ,T1) `(All ,ys ,T2))
         (define env (map cons xs ys))
         (type-equal? (subst-type env T1) T2)]
        [(other wise)
         (super type-equal? t1 t2)]))

    ;; 参数的类型和实际的类型
    (define/public (match-types env pat1 t2)
      (verbose 'type-check "match-types" env pat1 t2)
      (define result
        (match* (pat1 t2)
          [('Integer 'Integer) env]
          [('Boolean 'Boolean) env]
          [('Void 'Void) env]
          [('Any 'Any) env]
          [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))
           (for/fold ([env^ env]) ([pat1 ts1] [t2 ts2])
             (match-types env^ pat1 t2))]
          [(`(,ts1 ... -> ,rt1) `(,ts2 ... -> ,rt2))
           (define env^ (match-types env rt1 rt2))
           (for/fold ([env^^ env^]) ([pat1 ts1] [t2 ts2])
             (match-types env^^ pat1 t2))]
          ;; 泛型类型
          [(`(All ,xs1 ,t1) `(All ,xs2 ,t2))
           (define env^ (append (map cons xs1 xs2) env))
           (match-types env^ t1 t2)]
          
          [((? symbol? x) t)
           (match (dict-ref env x (lambda () #f))
             [#f
              (error 'type-check "undefined type variable ~a" x)]
             ['Type
              (cons (cons x t) env)]
             [t^
              (check-type-equal? t t^ 'matching) env])]
          
          [(other wise)
           (error 'type-check "mismatch ~a != a" pat1 t2)]))
      (copious 'match-types "done" pat1 t2 result)
      result)

    (define/public (subst-type env pat1)
      (verbose 'type-check "subst" env pat1)
      (match pat1
        ['Integer 'Integer]
        ['Boolean 'Boolean]
        ['Void 'Void]
        ['Any 'Any]
        [`(Vector ,ts ...)
         `(Vector ,@(for/list ([t ts]) (subst-type env t)))]
        [`(,ts ... -> ,rt)
         `(,@(for/list ([t ts]) (subst-type env t)) -> ,(subst-type env rt))]
        ;; 泛型
        [`(All ,xs ,t)
         `(All ,xs ,(subst-type (append (map cons xs xs) env) t))]
        [(? symbol? x)
         (dict-ref env x)]
        [else (error 'type-check "expected a type not ~a" pat1)]))
    
    (define/override (fun-def-type d)
      (match d
        ;; 普通函数
        [(Def f (list `[,xs : ,ps] ...) rt info body)
         `(,@ps -> ,rt)]
        ;; 泛型函数
        [(Poly ts (Def f (list `[,xs : ,ps] ...) rt info body))
         `(All ,ts (,@ps -> ,rt))]
        [else
         (error 'fun-def-type "expected function definition, not ~a" d)]))

    (define/public (def-name d)
      (match d
        [(Def f params rt info body)
         f]
        ;; 兼容Poly的类型
        [(Poly ts (Def f params rt info body))
         f]))
    
    (define/public ((check-well-formed env) ty)
      (match ty
        ['Integer (void)]
        ['Boolean (void)]
        ['Void (void)]
        ['Any (void)]
        
        [(? symbol? a)
         (match (dict-ref env a (lambda () #f))
           ['Type
            (void)]
           [else
            (error 'type-check "undefined type variable ~a" a)])]
        
        [`(Vector ,ts ...)
         (for ([t ts]) ((check-well-formed env) t))]
        
        [`(,ts ... -> ,t)
         (for ([t ts]) ((check-well-formed env) t))
         ((check-well-formed env) t)]
        
        [`(All ,xs ,t)
         ;; 给所有的类型赋值为Type，扩充env
         (define env^ (append (for/list ([x xs]) (cons x 'Type)) env))
         ((check-well-formed env^) t)]
        [else (error 'type-check "unrecognized type ~a" ty)]))

    ;; 将泛型声明和函数合并到一起，变成Poly
    (define/public (combine-decls-defs ds)
      (match ds
        ['() '()]
        ;; 新的函数声明的语法，注意ds^的位置
        [`(,(Decl name type) . (,(Def f params _ info body) . ,ds^))
         (unless (equal? name f)
           (error 'type-check "name mismatch, ~a != ~a" name f))
         (match type
           ;; xs为类型的参数
           [`(All ,xs (,ps ... -> ,rt))
            ;; 参数与类型
            (define params^ (for/list ([x params] [T ps]) `[,x : ,T]))
            ;; 构建Poly
            (cons (Poly xs (Def name params^ rt info body))
                  (combine-decls-defs ds^))]
           ;; 普通类型函数？非泛型函数
           [`(,ps ... -> ,rt)
            (define params^ (for/list ([x params] [T ps]) `[,x : ,T]))
            (cons (Def name params^ rt info body) (combine-decls-defs ds^))]
           [else (error 'type-check "expected a function type, not ~a" type) ])]
        ;; 普通函数
        [`(,(Def f params rt info body) . ,ds^)
         (cons (Def f params rt info body) (combine-decls-defs ds^))]))

    (define/override (type-check-apply env e1 es)
      ;; e1 为 op
      (define-values (e^ ty) ((type-check-exp env) e1))
      ;; es 为 参数
      (define-values (es^ ty*) (for/lists (es^ ty*) ([e (in-list es)])
                                ((type-check-exp env) e)))
      (match ty
        ;; 如果op为函数
        [`(,ty^* ... -> ,rt)
         (for ([arg-ty ty*] [param-ty ty^*])
           ;; 参数的类型和实际的类型需要一致
           (check-type-equal? arg-ty param-ty (Apply e1 es)))
         (values e^ es^ rt)]
        ;; 处理泛型的情况，需要推断参数的类型，泛型函数
        [`(All ,xs (,tys ... -> ,rt))
         ;; 将x的类型设置为Type
         (define env^ (append (for/list ([x xs]) (cons x 'Type)) env))
         (define env^^ (for/fold ([env^^ env^]) ([arg-ty ty*] [param-ty tys])
                         ;; 推断参数的类型
                         ;; 第一次，推断类型，不是第一次，查询类型
                         (match-types env^^ param-ty arg-ty)))
         (debug 'type-check "match result" env^^)
         (define targs
           (for/list ([x xs])
             (match (dict-ref env^^ x (lambda () #f))
               [#f (error 'type-check "type variable ~a not deduced\nin ~v"
                          x (Apply e1 es))]
               [ty ty])))
         ;; 返回类型为推断出来的类型
         (values (Inst e^ ty targs) es^ (subst-type env^^ rt))]
        [else (error 'type-check "expected a function, not ~a" ty)]))
    
    (define/override ((type-check-exp env) e)
      (verbose 'type-check "poly/exp begin" e env)
      (define-values (e^ ty)
        (match e
          ;; 闭包
          [(Lambda `([,xs : ,Ts] ...) rT body)
           (for ([T Ts]) ((check-well-formed env) T))
           ((check-well-formed env) rT)
           ;; 
           ((super type-check-exp env) e)]
          
          [(HasType e1 ty)
           ((check-well-formed env) ty)
           ((super type-check-exp env) e)]
          
          [else ((super type-check-exp env) e)]))
      (verbose 'type-check "poly/exp end" e e^ ty)
      (values e^ ty))
    
    (define/override ((type-check-def env) d)
      (verbose 'type-check "poly/def" d)
      (match d
        ;; 泛型函数
        [(Poly ts (Def f (and p:t* (list `[,xs : ,ps] ...)) rt info body))
         ;; 将泛型的类型设置成Type
         (define ts-env (for/list ([t ts]) (cons t 'Type)))
         ;; 处理函数的实际参数类型，实际参数里面会有泛型
         (for ([p ps]) ((check-well-formed ts-env) p))
         ;; 返回值里面可能也有泛型
         ((check-well-formed ts-env) rt)
         ;; 
         (define new-env (append ts-env (map cons xs ps) env))
         ;; 
         (define-values (body^ ty^) ((type-check-exp new-env) body))
         (check-type-equal? ty^ rt body)
         (Poly ts (Def f p:t* rt info body^))]
        ;; 普通函数
        [else ((super type-check-def env) d)]))

    (define/override (type-check-program p)
      (verbose 'type-check "poly/program" p)
      (match p
        [(Program info body)
         (type-check-program (ProgramDefsExp info '() body))]
        
        [(ProgramDefsExp info ds body)
         (define ds^ (combine-decls-defs ds))
         (define new-env (for/list ([d ds^])
                           (cons (def-name d) (fun-def-type d))))
         (define ds^^ (for/list ([d ds^]) ((type-check-def new-env) d)))
         (define-values (body^ ty) ((type-check-exp new-env) body))
         (check-type-equal? ty 'Integer body)
         (ProgramDefsExp info ds^^ body^)]))
    
    ))

(define (type-check-poly p)
  (send (new type-check-poly-class) type-check-program p))


;; The grammar for types is extended to include the type of a generic (All) and type variables.


;; (All (T) ((T -> T) (Vector T T) -> (Vector T T)))
;; All (T) 代表为泛型，T为All类型的参数，BNF中的var，type ::= (All (var...) type) | var
;; (T -> T) (Vector T T) 为map的入参，一个是函数，一个是vector
;; (Vector T T)代表map的出参
;; (T -> T) (Vector T T) -> (Vector T T) 代表map为一个函数
;; (All (T) (...))代表T的范围


;(: map (All (T) ((T -> T) (Vector T T) -> (Vector T T)))) ;;map的类型
;(define (map f v) ;; map函数
;  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
;(define (inc [x : Integer]) : Integer (+ x 1))
;(vector-ref (map inc (vector 0 41)) 1)

;; inst中记录T和Integer的对应关系
;; instantiation中，map的
(vector-ref ((inst map (All (T) ((T -> T) (Vector T T) -> (Vector T T)))
                   ;; 这个的Integer是如何实现的？
                   (Integer))
             inc (vector 0 41)) 1)

;; dynamically typed language
;; primitive operators require their arguments to be projected from Any and their results to be injected into Any

;; An inst node records the mapping of type parameters to type arguments.


;; 类型擦除是如何实现的？
;; 原始的表达式
(: map (All (T) ((T -> T) (Vector T T) -> (Vector T T))))
(define (map f v)
  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
(define (inc [x : Integer]) : Integer (+ x 1))
(vector-ref (map inc (vector 0 41)) 1)
;; resolve后的结果
(poly (T) (define (map [f : (T -> T)] [v : (Vector T T)]) : (Vector T T)
            (vector (f (vector-ref v 0)) (f (vector-ref v 1)))))
(define (inc [x : Integer]) : Integer (+ x 1))
(vector-ref ((inst map (All (T) ((T -> T) (Vector T T) -> (Vector T T)))
                   (Integer))
             inc (vector 0 41)) 1)
;; 类型擦除后的结果
;; map的类型已经没有了，即(: map (All (T) ((T -> T) (Vector T T) -> (Vector T T))))这一行已经没有了
;; T被替换成了Any
(define (map [f : (Any -> Any)] [v : (Vector Any Any)])
  : (Vector Any Any)
  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
(define (inc [x : Integer]) : Integer (+ x 1))
(vector-ref ((cast map
                   ((Any -> Any) (Vector Any Any) -> (Vector Any Any))
                   ((Integer -> Integer) (Vector Integer Integer)
                                         -> (Vector Integer Integer)))
             inc (vector 0 41)) 1)



