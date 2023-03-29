#lang racket
(require racket/fixnum)
(require "utilities.rkt")
(require "interp-Lfun.rkt")
(provide interp-Llambda interp-Llambda-class)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define interp-Llambda-class
  (class interp-Lfun-class
    (super-new)

    (define/override (interp-op op)
      (verbose "Llambda/interp-op" op)
      (match op
        ['procedure-arity
         (match-lambda
           [(Function xs body lam-env)
            (length xs)]
           [v (error 'interp-op "Llambda/expected a function, not ~a" v)])]
        [else
         (super interp-op op)]))

    (define/override ((interp-exp env) e)
      (define recur (interp-exp env))
      (verbose "Llambda/interp-exp" e)
      ;; env是如何构建的
      ;(printf "env is ~a \n" env)
      (match e
        [(Lambda (list `[,xs : ,Ts] ...) rT body)
         (Function xs body env)]
        [else ((super interp-exp env) e)]))
    ))

(define (interp-Llambda p)
  (send (new interp-Llambda-class) interp-program p))

;(interp-Llambda
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
;
;(printf "-------\n")
;
;(interp-Llambda
;(ProgramDefsExp
; '()
; '()
; (Let
;  'x
;  (Int 0)
;  (Let
;   'y
;   (Int 0)
;   (Let
;    'z
;    (Int 20)
;    (Let
;     'f
;     (Lambda
;      '((a : Integer))
;      'Integer
;      (Prim '+ (list (Var 'a) (Prim '+ (list (Var 'x) (Var 'z))))))
;     (Begin
;      (list (SetBang 'x (Int 10)) (SetBang 'y (Int 12)))
;      (Apply (Var 'f) (list (Var 'y))))))))))

;;分支的步骤
;; 第一步，解释def，只有一个def，返回一个Function，并放入环境中，环境中为函数名和Function的对应
;; 第二步，解释ProgramDefsExp的body，首先解释(Apply (Var 'f) (list (Int 5)))
;; 第三步，解释Apply，首先解释Apply中的fun部分，从环境中根据函数名获取到Function
;; 第四步，解释(list (Int 5))，得到(list 5)
;; 第五步，调用apply-fun，
;; 第六步，将参数名x和实际的参数值5，放入环境中得到新的环境，并用新的环境解释Funciton的body，也就是Let
;; 第七步，解释let，将y的值4放入环境中，解释let的body，也就是Lambda
;; 第八步，解释Lambda，返回一个Funtion，该Function的环境为上述构造的环境，里面含有f->Function，x->5，y->4的对应关系
;; 解释(Apply (Var 'f) (list (Int 3)))
;; ...
;; 最后解释Prim

;; *****重点*****，Funciton中带有env

;; 问题？ 'procedure-arity是什么时候会调用到
;; Equivalent to (lambda (id) (match id clause ...)).


