#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require data/queue)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;To create the s-expression for the Vector type,
;we use the unquote-splicing operator ,@ to insert the list t* without its usual start and end parentheses.


;(Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;  (Int 42)))


;(define (type-check-exp env e)
;  (match e
;    [(Var x)
;     (define type (match-alist x env))
;     (values (HasType (Var x) type) type)]
;    ...
;    [(Prim 'vector-set! (list vect (Int i) val))
;     (define-values (vect-exp vect-type) (type-check-exp env vect))
;     (define-values (i-exp i-type) (type-check-exp env (Int i)))
;     (define-values (val-exp val-type) (type-check-exp env val))
;     (if (not (eq? i-type 'Integer))
;         (error "The type of index for vector-set! must be an Integer")
;         ;; 可参考上面的例子，类型为(Vector Integer Integer)
;         (if (not (eq? (car vect-type) 'Vector))
;             (error "Vector set got a non vector")
;             (if (not (equal? (list-ref vect-type (add1 i)) val-type))
;                 (error (format "Changing vector types is not supported got ~a ~a" 
;                     (list-ref vect-type (add1 i)) val-type))
;                 (values (HasType (Prim 'vector-set! (list vect-exp i-exp val-exp))
;                                  'Void) 'Void))))]
;    ...))


;; 想一想环境中保存的是什么
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(SetBang x rhs)
       (SetBang (dict-ref env x) ((uniquify-exp env) rhs))]
      [(Begin es body)
       (Begin (for/list ([e es]) ((uniquify-exp env) e))
              ((uniquify-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(HasType e type)
       (HasType ((uniquify-exp env) e) type)]
      [(Let x e body)
       (let* ([new-sym (gensym x)]
              [new-env (dict-set env x new-sym)])
         (Let new-sym ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp '()) e))]))

;(uniquify
;(Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;  (Int 42))))

;; ------------------------------------------------------------

(define shrink-exp
  (lambda (e)
    (match e
      [(Prim 'and (list e1 e2))
       (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
      [(Prim 'or (list e1 e2))
       (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
      [(Prim op (list e1))
       (Prim op (list (shrink-exp e1)))]
      [(Prim op (list e1 e2))
       (Prim op (list (shrink-exp e1) (shrink-exp e2)))]
      [(Let x e1 body)
       (Let x (shrink-exp e1) (shrink-exp body))]
      [(If cnd thn els)
       (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
      [else e])))
      
      
(define shrink
  (lambda (p)
    (match p
      [(Program info e)
       (Program info (shrink-exp e))])))

;;--------------------------------------------------------------------------------------

;; 将exp的具体信息显现expose出来
;; type check 之后 会变成(HasType e type)的类型
;; (vector a b)是一种运算，运算的结果是一种数据类型，其他的数据类型，如int，var，bool，void都为基本类型
; This version of the type checker places a special AST node of the form (HasType e type) around each tuple creation.
;(define (expose-exp e)
;  (match e
;    ;; 创建vector   
;    [(HasType (Prim 'vector es) type)
;     (let* ([len (length es)] 
;            [bytes (* 8 len)]
;            [vect (gensym 'vec)] 
;            [vars (generate-n-vars len)])
;       (printf "vect is ~a, vars is ~a\n" vect vars)
;       (expand-into-lets vars (for/list ([e es]) (expose-exp e)) ;; 递归要将子exp的信息显现expose出来
;          (do-allocate vect len bytes
;              (bulk-vector-set (HasType (Var vect) type) vars type) 
;              type)
;          type)
;;       (define bulk-vector-set-r (bulk-vector-set (HasType (Var vect) type) vars type))
;;       (printf "bulk-vector-set-r is ~a \n" bulk-vector-set-r)
;;       (expand-into-lets vars (for/list ([e es]) (expose-exp e)) ;; 递归要将子exp的信息显现expose出来
;;          (do-allocate vect len bytes
;;                       bulk-vector-set-r
;;              ;(bulk-vector-set (HasType (Var vect) type) vars type) 
;;              type)
;;          type)
;       )]
;    [else e]
;    ;; 其他类型
;    ))

;; 全部转为临时变量
;; for/list, range
;(define (generate-n-vars n)
;  (if (zero? n) '()
;      (cons (gensym 'tmp) (generate-n-vars (sub1 n)))))

;(HasType (Let var exp
;              (HasType (Let var exp
;                            ...
;                            (HasType (Let var exp base) base-type)
;                            ...)
;                       base-type))
;         base-type)
;; 将表达式和变量转换为let的形式，let用hastype包围着
;(define (expand-into-lets vars exps base base-type)
;  (if (empty? exps) base
;    (HasType
;      (Let (car vars) (car exps) 
;           (expand-into-lets (cdr vars) (cdr exps) base base-type))
;      base-type)))

;; ommitting the HasType's for readability
;; base是什么?
;(define (do-allocate vect len bytes base type)
;    (Let '_ (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
;                                 (GlobalValue 'fromspace_end)))
;                (Void)
;                (Collect bytes))
;    (Let vect (Allocate len type) base)))

;(HasType (Let '_ (Prim vector-set! ((HasType (Var vec950052) (Vector Integer Integer)) (Int 0) (Var tmp950053)))
;              (HasType (Let '_ (Prim vector-set! ((HasType (Var vec950052) (Vector Integer Integer)) (Int 1) (Var tmp950054)))
;                            ;; 最终的值
;                            (HasType (Var vec950052) (Vector Integer Integer)))
;                       (Vector Integer Integer)))
;         (Vector Integer Integer))

;; vect is (HasType (Var vec262750) (Vector Integer Integer))
;; vars is (tmp262751 tmp262752)
;; ('_ '_)
;(define (bulk-vector-set vect vars types)
;  ;(printf "make-vector-set-exps is ~a \n" (make-vector-set-exps vect 0 vars (cdr types)))
;  (expand-into-lets (duplicate '_ (length vars))
;    ;(make-vector-set-exps vect 0 vars (cdr types)) vect types))
;    (make-vector-set-exps vect 0 vars) vect types))

;; use Racket's make-list instead, for/list
;(define (duplicate x n) 
;  (if (zero? n) '()
;      (cons x (duplicate x (sub1 n)))))

;; 创建vect中的表达式
; list中有两个元素
;(
;#<Prim: vector-set! (#<HasType: #<Var: vec371399> (Vector Integer Integer)> #<Int: 0> #<Var: tmp371400>)>
;#<Prim: vector-set! (#<HasType: #<Var: vec371399> (Vector Integer Integer)> #<Int: 1> #<Var: tmp371401>)>
;) 
;; for/list
;(define (make-vector-set-exps vect accum vars types)
;  (if (empty? vars) '()
;      (cons (Prim 'vector-set! (list vect (Int accum) (Var (car vars))))
;            (make-vector-set-exps vect (add1 accum) (cdr vars) (cdr types)))))

;(define (make-vector-set-exps vect accum vars)
;  (if (empty? vars) '()
;      (cons (Prim 'vector-set! (list vect (Int accum) (Var (car vars))))
;            (make-vector-set-exps vect (add1 accum) (cdr vars)))))



;(expose-exp
;   (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer)))
;(HasType
; (Let
;  'tmp212848
;  (Int 1)
;  (HasType
;   (Let
;    'tmp212849
;    (Int 2)
;    (Let
;     '_
;     (If
;      (Prim
;       '<
;       (list
;        (Prim '+ (list (GlobalValue 'free_ptr) (Int 16)))
;        (GlobalValue 'fromspace_end)))
;      (Void)
;      (collect 16))
;     (Let
;      'vec212847
;      (allocate 2 (Vector Integer Integer))
;      (HasType
;       (Let
;        '_
;        (Prim
;         'vector-set!
;         (list
;          (HasType (Var 'vec212847) '(Vector Integer Integer))
;          (Int 0)
;          (Var 'tmp212848)))
;        (HasType
;         (Let
;          '_
;          (Prim
;           'vector-set!
;           (list
;            (HasType (Var 'vec212847) '(Vector Integer Integer))
;            (Int 1)
;            (Var 'tmp212849)))
;          (HasType (Var 'vec212847) '(Vector Integer Integer)))
;         '(Vector Integer Integer)))
;       '(Vector Integer Integer)))))
;   '(Vector Integer Integer)))
; '(Vector Integer Integer))


(define (expose-exp e)
  (match e
    [(HasType (Prim 'vector es) type)
     (let* ([len (length es)]
            [bytes (* 8 len)]
            ;; vector的变量名
            [vect (gensym 'vec)]
            ;; 生成n个变量
            [vars (generate-n-vars len)])
       ;; 只形成第一部分的let,其余的嵌在其中的do-allocate中
       ;; do-allocate中嵌入let-set的部分
       ;; let-set的中间嵌入最终的值(HasType (Var vect) type)
       (expend-into-lets vars ;; 该参数和对应的exps,形成部分1, a sequence of temporary variable bindings for the initializing expressions,
                         ;;vars 对应的 exps
                         ;; 想想sicp中的name,命名
                         (for/list ([e es]) (expose-exp e)) 
                         ;;部分2  a conditional call to collect,
                         (do-allocate vect len bytes ;;vector的变量名
                                      ;; the initialization of the tuple. 各种set
                                      (bulk-vector-set
                                       ;; 最终的返回值
                                       (HasType (Var vect) type)
                                       ;; 与第一部分let中对应的变量
                                       vars type)
                                      type)
                         type))]
    [(Let x v body)
     (Let x (expose-exp v) (expose-exp body))]
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [else e]))
                 
(define (generate-n-vars n)
  (if (zero? n)
      '()
      (cons (gensym 'tmp) (generate-n-vars (sub1 n)))))

;; base改为continuation更合适
(define (expend-into-lets vars exps base base-type)
  (if (empty? exps)
      ;; 嵌入到其中的部分
      ;; 有三次嵌入,分别是allocate和let-set以及最终值
      base
      (HasType (Let (car vars) (car exps)
                    (expend-into-lets (cdr vars) (cdr exps) base base-type))
               base-type)))

;; base改为continuation更合适
(define (do-allocate vect len bytes base type)
  (Let '_ (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                             (GlobalValue 'fromspace_end)))
              (Void)
              (Collect bytes))
       ;;body
       (Let vect (Allocate len type)
            ;; 嵌入其中的let-set
            base)))

;; vect为continuation
(define (bulk-vector-set vect vars type)
  (expend-into-lets (duplicate '_ (length vars)) (make-vector-set-exps vect 0 vars)
                    ;; base 嵌入到let-set中的部分,也就是最终的值
                    vect type))

(define (duplicate x n)
  (if (zero? n)
      '()
      (cons x (duplicate x (sub1 n)))))

(define (make-vector-set-exps vect accum vars) ;; accum 为index
  (if (empty? vars)
      '()
      (cons (Prim 'vector-set! (list vect (Int accum) (Var (car vars))))
            (make-vector-set-exps vect (add1 accum) (cdr vars)))))


(define (expose-p p)
  (match p
    [(Program info e)
     (Program info (expose-exp e))]))

;(expose-p
; (uniquify
;  (Program
;   '()
;   (Let
;    'v
;    (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;    (Int 42)))))

;;----------------------------------------------------------

;We mark each read from a mutable variable with the form get! (GetBang in abstract syntax)

(define (collect-set! e)
  (match e
    [(Var x) (set)]
    [(Int n) (set)]
    [(Let x rhs body)
     (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs)
     (set-union (set var) (collect-set! rhs))]
    [(Prim 'read '()) (set)]
    [(Prim op es)
     (for/fold ([r (set)]) ([e es]) (set-union r (collect-set! e)))]
    [(If cnd thn els)
     (set-union (collect-set! cnd) (collect-set! thn) (collect-set! els))]
    [(Begin es body)
     (define es-set
       (for/fold ([r (set)]) ([e es]) (set-union r (collect-set! e))))
     (set-union es-set (collect-set! body))]
    [(WhileLoop cnd body)
     (set-union (collect-set! cnd) (collect-set! body))]))


;; for 返回值为void
;; for/list 返回值为list
;; for/lists 返回多个list
;; for/fold 返回值为收集的结果

(define ((uncover-get!-exp set!-vars) e)
  (match e
    [(Var x)
     (if (set-member? set!-vars x)
         (GetBang x)
         (Var x))]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x ((uncover-get!-exp set!-vars) rhs) ((uncover-get!-exp set!-vars) body))]
    [(SetBang var rhs)
     (SetBang var ((uncover-get!-exp set!-vars) rhs))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim op es)
     (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
    [(If cnd thn els)
     (If ((uncover-get!-exp set!-vars) cnd)
         ((uncover-get!-exp set!-vars) thn)
         ((uncover-get!-exp set!-vars) els))]
    [(Begin es body)
     (Begin
      (for/list ([e es]) ((uncover-get!-exp set!-vars) e))
      ((uncover-get!-exp set!-vars) body))]
    [(WhileLoop cnd body)
     (WhileLoop ((uncover-get!-exp set!-vars) cnd)
                ((uncover-get!-exp set!-vars) body))]))

(define uncover-get!
  (lambda (exp)
    (match exp
      [(Program info e)
       (define set-coll (collect-set! e))
       (Program info ((uncover-get!-exp set-coll) e))])))    

;;----------------------------------------------------------------

(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

(define (rco-atom e)
  ;(printf "e is ===== ~a \n" e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(HasType e^ type)
     (define new-e (rco-exp e^))
     (values (HasType new-e type) '())]
    [(GlobalValue x)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (GlobalValue x))))]
    [(Collect n) ;`(collect ,n)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (Collect n))))]
    [(Allocate amount type) ;`(allocate ,n ,type)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (Allocate amount type))))]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(Prim op es) 
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Prim op new-es)))))]
    [(If e1 e2 e3)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (match new-es
	    [(list e1 e2 e3)
	     (values (Var tmp)
             (append ss `((,tmp . ,(If e1 e2 e3)))))])]
    [(Void)
     (values (Void) '())]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

(define (rco-exp e)
  ;(printf "exp is =======  ~a \n" e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (Prim op new-es))]
    [(If e1 e2 e3)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (match new-es
	    [(list e1 e2 e3)
	     (make-lets^ (append* sss) (If e1 e2 e3))])]
    [(HasType e^ type)
     (HasType (rco-exp e^) type)]
    [(Void) (Void)]
    [(Allocate amount type)
     e] 
    ))


;(+ 5 (- 10)) 为 (+ atm exp),需要变换为 (+ atm atm) 的形式
;(+ 5 tmp1) 但是不能把(- 10)给丢了,需要将其保存起来,且tmp1代表(- 10)
;(remove-complex-opera*
; (expose-p
;  (uniquify
;   (Program
;    '()
;    (Let
;     'v
;     (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;     (Int 42))))))


;; ------------------------------------------------------------------------

;; explicate-control 思路

(define basic-blocks '())

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

;;------------
(define Explicate-CFG '())

(define (add-to-cfg t)
  (define new-label (gensym "l"))
  (set! Explicate-CFG (cons (cons new-label t) Explicate-CFG))
  new-label)

(define (explicate-tail exp)
  (match  exp
    [(Int n) (values (Return (Int n)) '())]
    [(Var v) (values (Return (Var v)) '())]
    [(Bool bool) (values (Return (Bool bool)) '())]
    [(Prim rator rand) (values (Return (Prim rator rand)) '())]
    [(Let var exp body)
     (let*-values ([(let-body variables1) (explicate-tail body)]
                   [(assigned-tail variables2) (explicate-assign exp var let-body)])
       (values assigned-tail (cons var (append variables1 variables2))))]
    [(If cnd thn els)
     (let*-values ([(thn-tail vars1) (explicate-tail thn)]
                   [(els-tail vars2) (explicate-tail els)])
     (let-values ([(cnd-tail vars3) (explicate-pred cnd thn-tail els-tail)])
       ;; (values cnd-tail (append vars3 vars1 vars2))))]))
       (values cnd-tail (append vars1 vars2 vars3))))]
    [(HasType e type)
     ...]
    [(GlobalValue ...)]
    [(Collect ...)]
    ))

(define (explicate-assign exp var tail)
  (match exp
    [(Int n) (values (Seq (Assign (Var var) (Int n)) tail) '())]
    [(Var v) (values (Seq (Assign (Var var) (Var v)) tail) '())]
    [(Bool bool) (values (Seq (Assign (Var var) (Bool bool)) tail) '())]
    [(Prim rator rand) (values (Seq (Assign (Var var) (Prim rator rand)) tail) '())]
    [(Let var* exp body)
     (let*-values ([(body-tail vars1) (explicate-assign body var tail)]
                   [(exp-tail vars2) (explicate-assign exp var* body-tail)])
       (values exp-tail (cons var* (append vars1 vars2))))]
    [(If cnd thn els)
     (define label (add-to-cfg tail))
     (let*-values ([(thn-tail vars1) (explicate-assign thn var (Goto label))]
                   [(els-tail vars2) (explicate-assign els var (Goto label))]
                   [(cnd-tail vars3) (explicate-pred cnd thn-tail els-tail)])
       ;; 注意变量顺序
       (values cnd-tail (append vars3 vars1 vars2)))]))

(define (explicate-pred e tail1 tail2)
  (match e
    [(Bool bool) (if bool (values tail1 '()) (values tail2 '()))]
    [(Var v)
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (values (IfStmt (Prim 'eq? (list (Var v) (Bool #t))) 
                     (Goto label1) (Goto label2)) 
             '())]
    [(Prim rator (list exp1 exp2))
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (define atm1 (gensym "rator-1-"))
     (define atm2 (gensym "rator-2-"))
     (let*-values ([(atm2-tail vars2) (explicate-assign exp2 atm2 (IfStmt (Prim rator (list (Var atm1) (Var atm2))) (Goto label1) (Goto label2)))]
                    [(atm1-tail vars1) (explicate-assign exp1 atm1 atm2-tail)])
        (values atm1-tail (cons atm1 (cons atm2 (append vars1 vars2)))))]
    [(Prim 'not (list exp))
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (values (IfStmt (Prim 'eq? (list exp (Bool #t))) (Goto label2) (Goto label1)) '())]
    [(Let var exp body)
      (define label1 (add-to-cfg tail1))
      (define label2 (add-to-cfg tail2))
      (define t (gensym "let-ec-"))
      (let*-values ([(body-tail vars1) (explicate-assign body t (IfStmt (Prim 'eq? (list (Var t) (Bool #t))) (Goto label1) (Goto label2)))]
                    [(exp-tail vars2) (explicate-assign exp var body-tail)])
        (values exp-tail (cons t (cons var (append vars1 vars2)))))]
    [(If cnd thn els)
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (let*-values ([(thn-block vars2) (explicate-pred thn (Goto label1) (Goto label2))]
                   [(els-block vars3) (explicate-pred els (Goto label1) (Goto label2))]
                   [(thn-label) (add-to-cfg thn-block)]
                   [(els-label) (add-to-cfg els-block)]
                   [(result vars) (explicate-pred cnd (Goto thn-label) (Goto els-label))]
                   )
       (values result (append vars vars2 vars3)))]
    ))

;; 添加副作用 position
;(define (explicate-effect e tail)
;  (match e
;    [(WhileLoop cnd body)
;     (define loop
;     (Goto 


;; 参考Ctup
;; 新添加的stmt变成Seq中的一部分
;; 新添加的exp变成Assign中的一部分
(define (explicate-control p)
  (set! Explicate-CFG '())
  (match p
    [(Program info e)
     (let-values ([(tail vars) (explicate-tail e)])
       (CProgram
        (cons (cons 'locals vars) info)
        (cons (cons 'start tail) Explicate-CFG)))]
    ))

;(Program
; '()
; (Let
;  'v264225
;  (HasType
;   (Let
;    'tmp264227
;    (Int 1)
;    (HasType
;     (Let
;      'tmp264228
;      (Int 2)
;      (Let
;       '_
;       (If
;        (Prim
;         '<
;         (list
;          (Prim '+ (list (GlobalValue 'free_ptr) (Int 16)))
;          (GlobalValue 'fromspace_end)))
;        (Void)
;        (collect 16))
;       (Let
;        'vec264226
;        (allocate 2 (Vector Integer Integer))
;        (HasType
;         (Let
;          '_
;          (Prim
;           'vector-set!
;           (list
;            (HasType (Var 'vec264226) '(Vector Integer Integer))
;            (Int 0)
;            (Var 'tmp264227)))
;          (HasType
;           (Let
;            '_
;            (Prim
;             'vector-set!
;             (list
;              (HasType (Var 'vec264226) '(Vector Integer Integer))
;              (Int 1)
;              (Var 'tmp264228)))
;            (HasType (Var 'vec264226) '(Vector Integer Integer)))
;           '(Vector Integer Integer)))
;         '(Vector Integer Integer)))))
;     '(Vector Integer Integer)))
;   '(Vector Integer Integer))
;  (Int 42)))

;;------------------------------------------------------------------------
(define (uncover-block tail)
  (match tail
    [(Seq (Assign var (HasType x type)) t)
     (cons `(,var . ,type) (uncover-block t))]
    [x '()]))

(define (uncover-locals p)
  (match p
    [(Program info B-list)
     (let ([locals (remove-duplicates
                     (append-map (lambda (x) 
                                    (uncover-block (cdr x))) B-list))])
       (Program `((locals . ,locals)) B-list))]))


;(Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;  (Int 42)))

;;--------------------------------------------------------------

(define (analyze-dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref mapping node)))
                (dict-set! mapping node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)

;;---------



(define (is-trivial? block)
  (match block
    [(Goto label) #t]
    [else #f]))

(define (get-label block)
  (match block
    [(Goto label) label]))

(define (add-to-hash hash src-label goto-label)
  (hash-set! hash src-label goto-label)
  (hash-map hash 
    (lambda (k v) (if (equal? v src-label)
      (hash-set! hash k goto-label)
      (void))))
  hash)

(define (short-cut blocks)
  (define ret (make-hash))
  (for ([(label block) (in-dict blocks)])
          (if (is-trivial? block)
            (add-to-hash ret label (get-label block))
            (hash-set! ret label label)))
  ret)

(define (patch-tail hash tl)
  (match tl
    [(IfStmt cnd thn els) (IfStmt cnd (patch-tail hash thn) (patch-tail hash els))]
    [(Return exp) tl]
    [(Seq stmt tail) (Seq stmt (patch-tail hash tail))]
    [(Goto label) (Goto (hash-ref hash label))]
    ))
;; 消除只有一个goto的label
;; remove the label who has only the goto
(define (patch-gotos short-cuts blocks)   
  (for/list ([(label block) (in-dict blocks)])
        (cons label (patch-tail short-cuts block))))

(define (optimize-jumps p)
  (match p
    [(CProgram info blocks)
      (define short-cuts (short-cut blocks))
      ;(printf "short cuts is ~a \n" short-cuts)
      (define not-short-cut (filter (lambda (b) (or (not (is-trivial? (cdr b)))
                                                    (equal? (car b) 'start))) blocks))
      ;(printf "not short cut is ~a \n" not-short-cut)
      (define patched (patch-gotos short-cuts not-short-cut))
      ;(printf "patched is ~a \n" patched)
      (define ref-graph (block-list->racketgraph patched))
      ;(printf "edges is ~a \n" (get-edges ref-graph))
      ;; what is the effect of this step?
      (define has-neighbors (filter (lambda (b) (or (has-vertex? ref-graph (car b))
                                                    (equal? (car b) 'start))) patched))
      ;(printf "has-neighbors is ~a \n" has-neighbors)
      (CProgram info (patch-gotos short-cuts has-neighbors))]))

;; 最后一步的goto的label，指向当前的label
;; 根据图4.8，tail总共有四种形式
;; (Return exp)
;; (Seq stmt tail)
;; (Goto label)
;; (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))
(define (build-graph-optimize label tail racket-cfg)
  (match tail
    [(Goto target)
     (printf "source is ~a, target is ~a \n " target label)
     (add-directed-edge! racket-cfg target label)]
    [(IfStmt cnd thn els) (begin
                            (build-graph-optimize label thn racket-cfg)
                            (build-graph-optimize label els racket-cfg))]
    [(Seq stmt tl) (build-graph-optimize label tl racket-cfg)]
    [_ (void)]))

(define (block-list->racketgraph blocks)
  (define racket-cfg (directed-graph '()))
     (for ([(label block) (in-dict blocks)])
       (build-graph-optimize label block racket-cfg))
     racket-cfg)



(define (sel-ins-atm c0a)
  (match c0a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Bool b) 
     (match b
      [#t (Imm 1)]
      [#f (Imm 0)])]))

(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(Prim 'read '())
            (list (Callq 'read_int 0)
                  (Instr 'movq (list (Reg 'rax) v)))]
           [(Prim '- (list atm))
            (define x86atm (sel-ins-atm atm))
            (if (equal? x86atm v)
                (list (Instr 'negq (list v)))
                (list (Instr 'movq (list x86atm v))
                      (Instr 'negq (list v))))]
           [(Prim '+ (list atm1 atm2))
            (define x86atm1 (sel-ins-atm atm1))
            (define x86atm2 (sel-ins-atm atm2))
            (cond [(equal? x86atm1 v) (list (Instr 'addq (list x86atm2 v)))]
                  [(equal? x86atm2 v) (list (Instr 'addq (list x86atm1 v)))]
                  [else (list (Instr 'movq (list x86atm1 v))
                              (Instr 'addq (list x86atm2 v)))])]
           [(Prim 'not (list atm))
            (if (eqv? v atm)
                (list (Instr 'xorq (list (Imm 1) v)))
                (list (let ([atm_ (sel-ins-atm atm)])
                        (Instr 'movq (list atm_ v)))
                      (Instr 'xorq (list (Imm 1) v))))]
           [(Prim 'eq? (list atm1 atm2))
            (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'e (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]
           [(Prim '< (list atm1 atm2))
           (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'l (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]))]))

(define (sel-ins-tail c0t)
  (match c0t
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]
    [(Goto label)
     (list (Jmp label))]
    [(IfStmt (Prim 'eq? (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'e label1)
        (Jmp label2)))]
    [(IfStmt (Prim '< (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'l label1)
        (Jmp label2)))]))

(define (select-instructions p)
  (match p
    [(CProgram info es)
     (X86Program info (for/list ([ls es])
                        (cons (car ls) (Block '() (sel-ins-tail (cdr ls))))))]))

;; We then initialize the tag and finally copy the address in r11 to the left-hand side
;; 结果为分配地址的首地址


;;==============================================================
;; live --- interference --- color
;; 47 minutes
;; uncover-live: live-after -> pseudo-x86 -> pseudo-x86*
;; *annotated program with live-after information for each stmt

(define (free-vars arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    ;; 栈 r为rbp i为offset
    [(Deref r i) (set r)]
    [(Imm n) (set)]
    [else (error "free-vars, unhandled" arg)]))

(define (read-vars instr)
  ;(printf "instr is ~a \n" instr)
  (match instr
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity)
    ;; (apply set-union (for/list ([a arity]) (free-vars a)))]
    [(Jmp label) (set)]
    [(JmpIf cc label)
     (set)]
    [(Instr 'movq (list s d)) (free-vars s)]
    [(Instr 'movzbq (list s d))
     (free-vars s)]
    [(Instr name arg*)
     (if (eq? name 'set)
         (set)
         (apply set-union (for/list ([arg arg*]) (free-vars arg))))]
    [else (error "read-vars unmatched" instr)]))

(define (write-vars instr)
  (match instr
    [(Jmp label) (set)]
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity)
    [(JmpIf cc label)
     (set)]
    [(Instr 'movq (list s d)) (free-vars d)]
    [(Instr 'movzbq (list s d))
     (free-vars d)]
    ;;[(Instr name arg*) (free-vars (last arg*))]
    [(Instr name arg*)
     (if (eq? name 'set)
         (set)
         (free-vars (last arg*)))]
    [else (error "write-vars unmatched" instr)]))

(define (uncover-live-instr live-after)
  (lambda (stmt)
    (set-union (set-subtract live-after (write-vars stmt))
               (read-vars stmt))))
                                   
(define (uncover-live-stmts orig-live-after)
  (lambda (orig-ss)
    (let loop ([ss (reverse orig-ss)]
               [live-after orig-live-after]
               [lives (list orig-live-after)])
      (cond [(null? ss) lives]
            [else
             (define new-live-after
               ((uncover-live-instr live-after) (car ss)))
             (loop (cdr ss) new-live-after
                   (cons new-live-after lives))]))))

(define (uncover-live-block ast live-after)
  (match ast
    ;; ss is list statements
    [(Block info ss)
     (define lives ((uncover-live-stmts live-after) ss))
     (define new-info (dict-set info 'lives lives))
     (Block new-info ss)]
    [else
     (error "R1-reg/uncover-live-block unhandled" ast)]))


;;--------------------------------

(define (adjacent-instr s)
  (match s
    [(Jmp label)
     (cond [(string-suffix? (symbol->string label) "conclusion") (set)]
           [else (set label)])]
    [(JmpIf cc label) (set label)]
    [else (set)]))

;; 'start 的adjacent-instrs为 l599654 和 l599655
(define (adjacent-instrs b)
  (match b
    [(Block info ss) ;; ss为指令list
     (for/fold ([outs (set)]) ([s ss]) ;; (set) 为outs的初始值
       (set-union outs (adjacent-instr s)))]
    ))

(define (CFG->graph cfg)
  (define G (directed-graph '()))
  (for ([label (in-dict-keys cfg)])
    ;; label是顶点
    (add-vertex! G label))
  (for ([(s b) (in-dict cfg)])
    (for ([t (adjacent-instrs b)])
      ;; 'start -> t ; t是个set
      (add-directed-edge! G s t)))
  (printf "G edges is ~a \n" (get-edges G))
  G)

(define (live-before label CFG-hash)
  (match (hash-ref CFG-hash label)
    [(Block info ss)
     (car (dict-ref info 'lives))]))

(define (uncover-live-CFG cfg)
  (define G (CFG->graph cfg))
  (define CFG-hash (make-hash))
  (for ([label (tsort (transpose G))])
    (define live-after
      (for/fold ([lives (set)])
                ([lbl (in-neighbors G label)])
        (set-union lives (live-before lbl CFG-hash))))
    (define new-block
      (uncover-live-block (dict-ref cfg label) live-after))
    (hash-set! CFG-hash label new-block)
    )
  (hash->list CFG-hash))

(define (uncover-live ast)
  (verbose "uncover-live " ast)
  (match ast
    [(X86Program info G)
     (X86Program info (uncover-live-CFG G))]
    ))




;;==========
;; 55 minutes
;; build-interference: live-after x graph -> pseudo-x86* -> pseudo-x86*
;; *annotate program with interference graph

(define (build-interference-instr live-after G)
  (lambda (ast)
    (verbose "build-interference-instr " ast live-after)
    (match ast
      [(or (Instr 'movq (list s d)) (Instr 'movzbq (list s d)))
       (for ([v live-after])
         (for ([d (free-vars d)])
           (cond [(equal? (Var v) s)
                  (verbose "same source" s)]
                 [(equal? v d)
                  (verbose "skip self edge on " d)]
                 [else
                  (verbose "adding edge " d v)
                  (add-edge! G d v)])))
       ast]
      [(Callq f arity)
       (for ([v live-after])
         (for ([u (caller-save-for-alloc)])
           (cond [(equal? v u)
                  (verbose "skip self edge on " v)]
                 [else
                  ;; 这个地方为什么要加边？ caller不是可以随便分配吗？
                  (verbose "adding edge " u v)
                  (add-edge! G u v)])))
       ast]
      [else
       (for ([v live-after])
         (for ([d (write-vars ast)])
           (cond [(equal? v d)
                  (verbose "skip self edge on " d)]
                 [else
                  (verbose "adding edge " d v)
                  (add-edge! G d v)])))
       ast])))
                 
  
(define (build-interference-block ast G)
  (match ast
    [(Block info ss)
     (define lives (dict-ref info 'lives))
     ;; put off the live-before of the first instruction
     (define live-afters (cdr lives))
     (define new-ss (for/list ([inst ss] [live-after live-afters])
                      ((build-interference-instr live-after G) inst)))
     (define new-info (dict-remove info 'lives))
     (Block new-info new-ss)]
    [else (error "R1-reg/build-interference-block unhandled" ast)]))

(define (build-interference ast)
  (verbose "build-interference " ast)
  (match ast
    [(X86Program info Blocks)
     (define locals (dict-ref info 'locals))
     (define G (undirected-graph '()))
     (for ([v locals])
       (add-vertex! G v))
     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label (build-interference-block block G))))
     (print-dot G "./interfere.dot")
     (printf "get conflicts edges is ~a \n" (get-edges G))
     (define new-info (dict-set info 'conflicts G))
     (X86Program new-info new-Blocks)]))





(define interference-test
  (lambda (ast)
    (match ast
      [(X86Program info Blocks)
       ;;(printf "~a " info)])))
       (printf "~a \n" (dict-ref info 'locals))
       (printf "block is ~a \n" (dict-ref Blocks 'start))
       (define new-Blocks
         (for/list ([(label block) (in-dict Blocks)])
           (cons label block)))
       (printf "new blocks is ~a \n" new-Blocks)])))


;;===========
;; build-move-graph: pseudo-x86* -> pseudo-x86*
;; *annotate program with move graph

(define use-move-biasing #t)

(define (build-move-graph-instr G)
  (lambda (ast)
    (match ast
      [(Instr 'movq (list (Var s) (Var d)))
       (if use-move-biasing
           (add-edge! G s d)
           '())
       ast]
      [else ast])))

(define (build-move-block ast MG)
  (match ast
    [(Block info ss)
     (define new-ss
       (if use-move-biasing
           (let ([nss (for/list ([inst ss])
                        ((build-move-graph-instr MG) inst))])
             (print-dot MG "./move.dot")
             nss)
           ss))
     (Block info new-ss)]
    [else
     (error "R1-reg/build-move-block unhandled" ast)]))

(define (build-move-graph ast)
  (match ast
    [(X86Program info Blocks)
     ;; (define MG (make-graph (dict-ref iinfo 'locals)))
     (define MG (undirected-graph '()))
     (for ([v (dict-ref info 'locals)])
       (add-vertex! MG v))

     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label (build-move-block block MG))))
     (define new-info (dict-set info 'move-graph MG))
     (X86Program new-info new-Blocks)]))


;; ===========
;; allocate-registers: pseudo-x86 -> pseudo-x86
;; Replaces variables with registers and stack locations
;; using graph coloring based on Suduko heuristics
;; This pass encompasses assign-homes

(use-minimal-set-of-registers! #t)

;; 不在饱和度中的颜色
(define (valid-color c v unavail-colors info)
  (not (set-member? unavail-colors c)))

;; unavail-colors为结点v的饱和度
(define (choose-color v unavail-colors move-related info)
  ;; 3
  (define n (num-registers-for-alloc))
  (define biased-selection
    (for/first ([c move-related]
                #:when (valid-color c v unavail-colors info))
      c))
  (define unbiased-selection    
    ;;(for/list
    (for/first ([c (in-naturals)]
                #:when (valid-color c v unavail-colors info))
      c))
  (cond
    [(and biased-selection
          (or (< biased-selection n) (>= unbiased-selection n)))
     ;;(vomit "move-biased, for ~a chose ~a" v biased-selection)
     biased-selection]
    [else unbiased-selection]))

;; (inherit variable-size)
(define variable-size 8)

;; Take into account space for the callee saved registers
;(define (first-offset num-used-callee)
;  (+ (super first-offset num-used-callee)
;     (* num-used-callee (variable-size))))

(define (first-offset num-used-callee)
 (+ (* 1 variable-size)
     (* num-used-callee variable-size))) 

(define (init-num-spills) 0)

(define (update-num-spills spills c)
  (cond
    [(>= c (num-registers-for-alloc))
     (add1 spills)]
    [else spills]))

;; 1. 初始，冲突图
;; 2. 将图中已经存在的寄存器染色（分配数字），此时变量还没有被染色，更新跟已经存在的寄存器相邻的顶点的饱和度
;; 3. 选择最大饱和度的顶点，选择最小的颜色进行染色，更新跟该顶点相邻的结点的饱和度
;; 4. 重复上一步
;; 5. 根据染色分配寄存器
;; 假设现在只有一个寄存器可以分配rcx
;;--------------------
;; 带move的
;; 1. 初始，冲突图和move图
;; 2. 将图中已经存在的寄存器染色(分配数字)，更新跟已经存在的寄存器相邻的顶点的饱和度
;; 3. 选择最大饱和度的顶点，如果有多个，选择move图中存在的顶点，染跟move相关顶点相同的颜色，更新相邻结点饱和度
;; 4. 重复上一步
;; 5. 根据染色分配寄存器

;; 三个hash
;; 一个指定饱和度
;; 一个指定优先级队列中的node
;; 一个指定相应的颜色

;; IG 冲突图
;; MG move图
(define (color-graph IG MG info) ;; DSATUR algorithm
  (define locals (dict-ref info 'locals))
  (define num-spills (init-num-spills))
  (define unavail-colors (make-hash));; pencil marks
  ;; 不可用的color数，优先级队列
  (define (compare u v);; compare saturation
    (>= (set-count (hash-ref unavail-colors u))
        (set-count (hash-ref unavail-colors v))))
  (define Q (make-pqueue compare))
  (define pq-node (make-hash)) ;; maps vars to priority queue nodes
  (define color (make-hash)) ;; maps vars to colors (natural nums)

  ;; 完成第一步，将图中已经存在的寄存器染色(分配数字),更新跟已经存在的寄存器相邻的顶点的饱和度
  (for ([x locals])
    ;; mark neighboring register colors as unavailable
    ;; 找出冲突图中已经存在的寄存器
    (define adj-reg
      (filter (lambda (u) (set-member? registers u))
              (get-neighbors IG x)))
    ;; 先对已经存在的寄存器进行染色
    (define adj-colors (list->set (map register->color adj-reg)))
    ;; 标注x的饱和度（不可用颜色的集合）
    (hash-set! unavail-colors x adj-colors)
    ;; add variables to priority queue
    (hash-set! pq-node x (pqueue-push! Q x)))

  ;; 染色
  ;; Graph coloring
  (while (> (pqueue-count Q) 0)
         ;; 最大饱和度的？这个地方是否应该找出多个
         (define v (pqueue-pop! Q))
         ;; 找出与v有move关系，且已经染色的，为什么要进行排序？
         (define move-related
           (sort (filter (lambda (x) (>= x 0))
                         (map (lambda (k) (hash-ref color k -1))
                              (get-neighbors MG v)))
                 <))
         ;; 染色
         (define c (choose-color v (hash-ref unavail-colors v)
                                 move-related info))
         (verbose "color of ~a is ~a" v c)
         ;; 统计spill的数量
         (set! num-spills (update-num-spills num-spills c))
         (hash-set! color v c)
         ;; mark this color as unavailable for neighbors
         (for ([u (in-neighbors IG v)])
           (when (not (set-member? registers u))
             (hash-set! unavail-colors u
                        (set-add (hash-ref unavail-colors u) c))
             (pqueue-decrease-key! Q (hash-ref pq-node u)))))
  (values color num-spills))
         
(define (identify-home num-used-callee c)
  (define n (num-registers-for-alloc))
  (cond
    [(< c n)
     (Reg (color->register c))]
    [else
     (Deref 'rbp (- (+ (first-offset num-used-callee)
                       (* (- c n) variable-size))))]))
                       ;;(* (- c n) (variable-size)))))]))

(define (callee-color? c)
  (and (< c (num-registers-for-alloc))
       (set-member? callee-save (color->register c))))

(define (used-callee-reg locals color)
  (for/set ([x locals] #:when (callee-color? (hash-ref color x)))
    (color->register (hash-ref color x))))

(define (num-used-callee locals color)
  (set-count (used-callee-reg locals color)))

(define (assign-block-info homes)
  (lambda (b)
    (match b
      [(Block info ss)
       (define new-info (dict-set info 'assign-homes homes))
       (Block new-info ss)])))
       

(define (allocate-registers ast)
  (match ast
    [(X86Program info Blocks)
     (define locals (dict-ref info 'locals))
     (define IG (dict-ref info 'conflicts))
     (define MG (dict-ref info 'move-graph))
     (define-values (color num-spills) (color-graph IG MG info))
     ;; 分配寄存器or栈
     (define homes
       (for/hash ([x locals])
         (define home (identify-home (num-used-callee locals color)
                                     (hash-ref color x)))
         ;;(vomit "home of ~a is ~a" x home)
         ;;(printf "home of ~a is ~a \n" x home)
         (values x home)))

     ;;(printf "homes is ~a \n" homes)
     
     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label ((assign-block-info homes) block))))
         ;;(cons label block)))     
         ;;(cons label (assign-homes-block homes) block)))

     (define new-info (dict-remove-all
                       (dict-set (dict-set info 'num-spills num-spills)
                                 'used-callee
                                 (used-callee-reg locals color))
                       (list 'locals 'conflicts 'move-graph)))
     (X86Program new-info new-Blocks)]))




;; ------

;; curr-block为label
(define (fix-block instrs cfg removed-blocks all-blocks curr-block)
  (cond
    [(null? instrs) '()]
    [else (let ([instr (car instrs)])
            (match instr
              ;; check if the target has only this edge
              [(Jmp target) #:when (and (not (equal? target 'conclusion))
                                        (equal? (length (get-neighbors cfg target)) 1)
                                        (< (edge-weight cfg target curr-block) 2))
                            (begin
                              (set-add! removed-blocks target)
                              ;; 将指令组合在一起
                              (append
                               (fix-block (Block-instr* (dict-ref all-blocks target)) cfg removed-blocks all-blocks curr-block)
                               (fix-block (cdr instrs) cfg removed-blocks all-blocks curr-block)))]
              [_ (cons instr (fix-block (cdr instrs) cfg removed-blocks all-blocks curr-block))]))]))


(define (remove-jumps p)
  (match p
    [(X86Program info blocks)
     ;; Get cfg
     (define r-cfg (dict-ref info 'r-cfg))
     ;; tsorted vertices
     (define vertices-order (tsort (transpose r-cfg)))
     ;;keep track of new blocks
     (define new-blocks '())
     ;;keep track of removed blocks
     (define removed-blocks (mutable-set))
     ;;remove jumps
     (for ([vert vertices-order])
       (if (not (set-member? removed-blocks vert))
           (let* ([instrs (Block-instr* (dict-ref blocks vert))] ;; 该顶点(label)对应的所有的instrs
                  [block-info (Block-info (dict-ref blocks vert))] ;; label的info
                  [new-instrs (fix-block instrs r-cfg removed-blocks blocks vert)]
                  [new-block (Block block-info new-instrs)])
             (set! new-blocks (cons (cons vert new-block) new-blocks)))
           (void)))
     ;;(display new-blocks)
     (X86Program info new-blocks)]))



;; =====================================================

;; select-instructions : C0 -> pseudo-x86
;(define (select-instructions p)
;  (error "TODO: code goes here (select-instructions)"))

(define (calc-stack-space ls) (* 8 (length ls)))

;; be related to the function 'explicate-tail' let branch (append new-rhs-vars body-vars)
(define (find-index v ls)
  (cond
    ;;[(eq? v (Var-name (car ls))) 1]
    [(eq? v (car ls)) 1]
    [else (add1 (find-index v (cdr ls)))]
    ))

(define (assign-homes-imm i ls)
  (match i
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Var v) (Deref 'rbp (* -8 (find-index v (cdr ls))))]
   ))
   
(define (assign-homes-instr i ls)
  (match i
    [(Instr op (list e1)) 
     (Instr op (list (assign-homes-imm e1 ls)))]
    [(Instr op (list e1 e2))
     (Instr op (list (assign-homes-imm e1 ls) (assign-homes-imm e2 ls)))]
    [else i]
    ))
    
(define (assign-homes-block b ls)
  (match b
    [(Block info es) 
     (Block info (for/list ([e es]) (assign-homes-instr e ls)))]
    ))


;;-----

(define (patch-instructions-instrs instr)
  (match instr
    [(Instr op (list (Deref r1 n1) (Deref r2 n2)))
     (list (Instr 'movq (list (Deref r1 n1) (Reg 'rax)))
           (Instr op (list (Reg 'rax) (Deref r2 n2))))]
    [(Instr 'movq (list (Reg r1) (Reg r2)))
     (cond
       [(equal? r1 r2) '()]
       [else (list instr)])]
    [(Instr 'cmpq (list  arg1 (Imm n)))
     (list (Instr 'movq (list (Imm n) (Reg 'rax)))
           (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [(Instr 'movzbq (list  arg1 (Imm n)))
         (list (Instr 'movq (list (Imm n) (Reg 'rax)))
               (Instr 'mvzbq (list arg1 (Reg 'rax))))]
    [_ (list instr)]))

(define (patch-instructions-block block)
  (match block
    [(Block info instrs)
     (Block info (flatten (for/list ([instr instrs]) 
                            (patch-instructions-instrs instr))))]))

(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (X86Program info (for/list ([block blocks]) 
                          (cons (car block) (patch-instructions-block (cdr block)))))]))



;;--------------
;; 问题
;; 1. main里面的，一条命令里面有两个栈引用，是否需要修改
;; 2. main和conclusion的固定格式的原因是什么？
(define make-prelude
  (lambda ()
    (cons 'main
                (Block '() (list (Instr 'pushq (list (Deref 'rbp 0)))
                                 (Instr 'movq (list (Deref 'rsp 0) (Deref 'rbp 0)))
                                 (Instr 'subq (list (Imm 16) (Deref 'rsp 0)))
                                 (Jmp 'start))))))

(define make-conclusion
  (lambda ()
    (cons 'conclusion
                (Block '() (list (Instr 'addq (list (Imm 16) (Deref 'rsp 0)))
                                 (Instr 'popq (list (Deref 'rbp 0)))
                                 (Retq))))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info `((start . ,bs)))
     (X86Program info (list (make-prelude) `(start . ,bs) (make-conclusion)))]))
;     (X86Program info (map
;                       (lambda (x) `(,(car x) . ,(patch-block (cdr x))))
;                       (list (make-prelude B-list (make-conclusion))))]))
    

;; prelude-and-conclusion : x86 -> x86
;(define (prelude-and-conclusion p)
;  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lwhile ,type-check-Lwhile)
     ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
     ("uncover-get!" ,uncover-get! ,interp-Lwhile ,type-check-Lwhile)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
     ;;("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
     ;;("optimize jumps" ,optimize-jumps ,interp-Cif ,type-check-Cif)
     ;;("instruction selection" ,select-instructions ,interp-x86-1)
     ;;("assign homes" ,assign-homes ,interp-x86-0)
     ;;("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))


