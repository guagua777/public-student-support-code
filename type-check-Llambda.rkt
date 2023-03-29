#lang racket
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(provide type-check-Llambda type-check-Llambda-class typed-vars)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Lambda                                                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-Llambda

(define typed-vars (make-parameter #f))

(define type-check-Llambda-class
  (class type-check-Lfun-class
    (super-new)
    (inherit check-type-equal?)
    (inherit-field max-parameters)
    
    (define/override (type-check-exp env)
      (lambda (e)
        (debug 'type-check-exp "Llambda" e)
        (define recur (type-check-exp env))
        (match e
          [(HasType (Var x) t)
           ((type-check-exp env) (Var x))]
          [(Var x)
           (define t (dict-ref env x))
           (define var (cond [(typed-vars) (HasType (Var x) t)]
                             [else (Var x)]))
           (values var t)]
          [(Closure arity es)
           (define-values (e* t*) (for/lists (e* t*) ([e es])
                                    (recur e)))
           (let ([t `(Vector ,@t*)])
             (values (HasType (Closure arity e*) t) t))]
          [(Prim 'procedure-arity (list e1))
           (define-values (e1^ t) (recur e1))
           (match t
             ;; before closure conversion
             [`(,ts ... -> ,rt)
              (values (Prim 'procedure-arity (list e1^)) 'Integer)]
             ;; after closure conversion
             [`(Vector (,clos ,ts ... -> ,rt) ,ts2 ...)
              (values (Prim 'procedure-arity (list e1^)) 'Integer)]
             [else (error 'type-check
                          "expected a function not ~a\nin ~v" t e)])]
          [(HasType (Closure arity es) t)
           ((type-check-exp env) (Closure arity es))]
          [(AllocateClosure size t arity)
           (values (AllocateClosure size t arity) t)]
          [(FunRef f n)
           (let ([t (dict-ref env f)])
             (values (FunRef f n) t))]
          [(Lambda (and params `([,xs : ,Ts] ...)) rT body)
           (unless (< (length xs) max-parameters)
             (error 'type-check "lambda has too many parameters, max is ~a"
                    max-parameters))
           (define-values (new-body bodyT) 
             ((type-check-exp (append (map cons xs Ts) env)) body))
           (define ty `(,@Ts -> ,rT))
           (check-type-equal? rT bodyT e)
           (values (Lambda params rT new-body) ty)]
          [else ((super type-check-exp env) e)]
          )))

    ))

(define (type-check-Llambda p)
  (send (new type-check-Llambda-class) type-check-program p))


;(type-check-Llambda
; (ProgramDefsExp
; '()
; (list
;  (Def
;   'f
;   '((x : Integer))
;   '(Integer -> Integer)
;   '()
;   (Let
;    'y
;    (Int 4)
;    (Lambda
;     '((z : Integer))
;     'Integer
;     (Prim '+ (list (Var 'x) (Prim '+ (list (Var 'y) (Var 'z)))))))))
; (Let
;  'g
;  (Apply (Var 'f) (list (Int 5)))
;  (Let
;   'h
;   (Apply (Var 'f) (list (Int 3)))
;   (Prim
;    '+
;    (list (Apply (Var 'g) (list (Int 11))) (Apply (Var 'h) (list (Int 15)))))))))


;; 分支步骤
;; 第一步，获取Def的类型，并放入环境中，函数名->函数类型
;; 函数名为f，函数类型为(Integer -> (Integer -> Integer)) 输入是一个整形，返回值为一个函数，并放入环境中
;; 第二步，检查Def的类型，参数名和对应的类型，放入环境中，x->Integer
;; 第三步，检查Def中body的类型，body为一个Let，y->Integer，并放入环境中，检查let的body，也就是Lambda
;; 第四步，检查Lambda的类型，将参数和对应的类型，放入环境中，z->Integer，
;; 第五步，检查Lambda的body的类型，body为(Prim '+ ...)，对应的op类型为((Integer Integer) . Integer)，对应的返回值类型为Integer
;; 对应的lambda的类型为(Integer -> Integer)
;; 第六步，检查Def的类型与Def的body的类型是否相等
;; 第七步，检查ProgramDefsExp的body的类型，并检查body的类型是否等于Integer




