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
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

(provide (all-defined-out))


(define parse-exp
  (lambda (e)
    (match e
      [(? symbol?) (Var e)]
      [(? fixnum?) (Int e)]
      [(? boolean?) (Bool e)]
      [`(void) (Void)]
      [`(let ([,x ,rhs]) ,body)
       (Let x (parse-exp rhs) (parse-exp body))]
      [`(if ,cnd ,thn ,els)
       (If (parse-exp cnd) (parse-exp thn) (parse-exp els))]
      [`(while ,cnd ,body)
       (WhileLoop (parse-exp cnd) (parse-exp body))]
      [`(set! ,x ,rhs)
       (SetBang x (parse-exp rhs))]
      [`(begin ,es ... ,e)
       (Begin (for/list ([e es])
                (parse-exp e))
              (parse-exp e))]
      [`(,op ,es ...)
       #:when (set-member? src-prim op)
       (Prim op (for/list ([e es])
                  (parse-exp e)))]
      [`(,e ,es ...)
       (Apply (parse-exp e)
              (for/list ([e es])
                (parse-exp e)))])))



