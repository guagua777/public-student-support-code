#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")

(require "priority_queue.rkt")

(provide (all-defined-out))

;; 47 minutes
(define compile-reg-R1
  (class compile-R1
    (super-new)

    (field [use-move-biasing #t])

    (inherit assign-homes-instr assign-homes-block
             print-x86-instr print-x86-block)

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; uncover-live: ....

    (define/public (free-vars arg)
      (match arg
        ...))


    ))



