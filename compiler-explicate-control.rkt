#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

(provide (all-defined-out))

;(let ([x 20])
;  (+ x 10))
;
;=> 变成(Seq stmt tail)的形式
;
;x = 20; -> stmt
;return (+ x 10); -> tail
;
;因此需要一个赋值的操作
;最后将body体return

;program:
;locals:
;'(x139750)
;start:
;    x139750 = 20;
;    return (+ x139750 10);

;; tail position无需记忆，自然就能推出来
;; tail position的递归定义
;1. In (Program () e), expression e is in tail position.
;2. If (Let x e1 e2) is in tail position, then so is e2.


;stmt ::= (Assign (Var var) exp)
;tail ::= (Return exp) | (Seq stmt tail)
;tail是return或者是seq，stmt是一个赋值
;赋值产生的tail是Seq

(define (explicate-control p)
  (match p
    [(Program info body)
     (define-values (tail let-binds) (explicate-tail body))
     (CProgram (cons (cons 'local let-binds) info) (list (cons 'start tail)))]))

(define (explicate-tail exp)
  (match exp
    [(Var x) (values (Return (Var x)) '())]
    [(Int n) (values (Return (Int n)) '())]
    [(Let x v body)
     (define-values (body-tail body-let-binds) (explicate-tail body))
     (define-values (let-tail let-binds) (explicate-assign (Var x) v body-tail))
     (values let-tail (cons x (append let-binds body-let-binds)))] 
     ;;...]
    [(Prim op es)
     (values (Return (Prim op es)) '())]))

; (Seq stmt tail)
;(define explicate-assign
;  (lambda (x v)
;    [match v
;      [(Int n)
;       (values (Seq (Assign x (Int n)) tail ;; tail得传进来

; (Seq stmt tail)
(define explicate-assign
  (lambda (x v tail)
    (match v
      [(Int n)
       (values (Seq (Assign x (Int n)) tail) '())]
      [(Var v^)
       ;;(values (Seq (Assign x (Var v^)) tail) (list v^))]
       (values (Seq (Assign x (Var v^)) tail) '())]
      [(Let x^ v^ body)
       (define-values (let-tail let-binds) (explicate-assign x body tail))
       (define-values (v^-tail v^-let-binds) (explicate-assign (Var x^) v^ let-tail))
       ;;(values v^-tail (append let-binds v^-let-binds))]
       (values v^-tail (cons x^ (append let-binds v^-let-binds)))]
      [(Prim op args)
       (values (Seq (Assign x (Prim op args)) tail) '())])))

(explicate-control
 (Program
 '()
 (Let
  'y247165
  (Let
   'x247166
   (Int 20)
   (Let 'x247167 (Int 22) (Prim '+ (list (Var 'x247166) (Var 'x247167)))))
  (Var 'y247165))))
       

       
             



       
       


       
       


