#lang racket
(require racket/fixnum)
(require "utilities.rkt")

;; P154

(define (f6 x7)
  (let ([y8 4])
    (lambda (z9)
      (+ x7 (+ y8 z9)))))

(define (main)
  (let ([g0 ((fun-ref f6 1) 5)])
    (let ([h1 ((fun-ref f6 1) 3)])
      (+ (g0 11) (h1 15)))))

;; fun-ref 就是struct (FunRef fname n)






 
