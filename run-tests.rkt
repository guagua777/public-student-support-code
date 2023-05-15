#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "interp-Lvecof.rkt")
(require "interp-Cvecof.rkt")
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "interp-Llambda.rkt")
(require "interp-Clambda.rkt")
(require "interp-Ldyn.rkt")
(require "interp-Lany.rkt")
;(require "interp-Lcast.rkt")
(require "interp.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Lvecof.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Llambda.rkt")
(require "type-check-Lany.rkt")
;(require "type-check-gradual.rkt")
(require "compiler.rkt")
(debug-level 4)
;(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

;;(interp-tests "var" #f compiler-passes interp-Lvar "var_test" (tests-for "var"))

;(interp-tests "if" type-check-Lif '() interp-Lif "cond_test" (tests-for "cond"))
;(interp-tests "if" type-check-Lif compiler-passes interp-Lif "cond_test" (tests-for "cond"))

;(interp-tests "while" type-check-Lwhile '() interp-Lwhile "while_test" (tests-for "while"))
;(interp-tests "while" type-check-Lwhile compiler-passes interp-Lwhile "while_test" (tests-for "while"))
;(interp-tests "vector" type-check-Lvec '() interp-Lvec "vectors_test" (tests-for "vectors"))
;(interp-tests "vector" type-check-Lvec compiler-passes interp-Lvec "vectors_test" (tests-for "vectors"))

;(interp-tests "function" type-check-Lfun '() interp-Lfun "functions_test" (tests-for "functions"))
;(interp-tests "function" type-check-Lfun compiler-passes interp-Lfun "functions_test" (tests-for "functions"))

;(interp-tests "lambda" type-check-Llambda '() interp-Llambda "lambda_test" (tests-for "lambda"))
;(interp-tests "lambda" type-check-Llambda compiler-passes interp-Llambda "lambda_test" (tests-for "lambda"))


;(interp-tests "dynamic" type-check-Lany '() interp-Ldyn "dynamic_test" (tests-for "dynamic"))

(interp-tests "any" type-check-Lany '() interp-Lany "dynamic_test" (tests-for "dynamic"))

;(interp-tests "any" type-check-Lany '() interp-Lany "gradual_test" (tests-for "gradual"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
;; (compiler-tests "var" #f compiler-passes "var_test" (tests-for "var"))

