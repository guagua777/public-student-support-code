#lang racket
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lwhile.rkt")
(provide type-check-Lvec type-check-Lvec-class)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Tuples (aka Vectors)                                                      ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-Lvec

(define type-check-Lvec-class
  (class type-check-Lwhile-class
    (super-new)
    (inherit check-type-equal?)

    (define/override (type-equal? t1 t2)
      (debug 'type-equal? "lenient" t1 t2)
      (match* (t1 t2)
        [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))
         (for/and ([t1 ts1] [t2 ts2])
           (type-equal? t1 t2))]
        [(other wise) (super type-equal? t1 t2)]))
    
    (define/override (type-check-exp env)
      (lambda (e)
        (define recur (type-check-exp env))
        (match e
          [(Prim 'vector es)
           (unless (<= (length es) 50)
             (error 'type-check "vector too large ~a, max is 50" (length es)))
           (define-values (e* t*) (for/lists (e* t*) ([e es]) (recur e)))
           ;(printf "e* is ~a \n t* is ~a \n" e* t*)
           (define t `(Vector ,@t*))
           (values (HasType (Prim 'vector e*) t)  t)]
          [(Prim 'vector-ref (list e1 (Int i)))
           ;; 获取vector的类型
           (define-values (e1^ t) (recur e1))
           (match t
             [`(Vector ,ts ...)
              (unless (and (0 . <= . i) (i . < . (length ts)))
                (error 'type-check "index ~a out of bounds\nin ~v" i e))
              (values (Prim 'vector-ref (list e1^ (Int i)))  (list-ref ts i))]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t e)])]
          [(Prim 'vector-set! (list e1 (Int i) arg) )
           (define-values (e-vec t-vec) (recur e1))
           (define-values (e-arg^ t-arg) (recur arg))
           (match t-vec
             [`(Vector ,ts ...)
              (unless (and (0 . <= . i) (i . < . (length ts)))
                (error 'type-check "index ~a out of bounds\nin ~v" i e))
              (check-type-equal? (list-ref ts i) t-arg e)
              (values (Prim 'vector-set! (list e-vec (Int i) e-arg^))  'Void)]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t-vec e)])]
          [(Prim 'vector-length (list e))
           (define-values (e^ t) (recur e))
           (match t
             [`(Vector ,ts ...)
              (values (Prim 'vector-length (list e^))  'Integer)]
             [else (error 'type-check "expect Vector, not ~a\nin ~v" t e)])]
          [(Prim 'eq? (list arg1 arg2))
           (define-values (e1 t1) (recur arg1))
           (define-values (e2 t2) (recur arg2))
           (match* (t1 t2)
             [(`(Vector ,ts1 ...)  `(Vector ,ts2 ...))  (void)]
             [(other wise)  (check-type-equal? t1 t2 e)])
           (values (Prim 'eq? (list e1 e2)) 'Boolean)]
          [(HasType (Prim 'vector es) t)
           ((type-check-exp env) (Prim 'vector es))]
          [(HasType e1 t)
           (define-values (e1^ t^) (recur e1))
           (check-type-equal? t t^ e)
           (values (HasType e1^ t) t)]
          [(GlobalValue name)
           (values (GlobalValue name) 'Integer)]
          [(Allocate size t)
           (values (Allocate size t) t)]
          [(Collect size)
           (values (Collect size) 'Void)]
          [else ((super type-check-exp env) e)]
          )))
    ))

(define (type-check-Lvec p)
  (send (new type-check-Lvec-class) type-check-program p))

;(type-check-Lvec
;   (Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;  (Int 42))))

; (type-check-Lvec (Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 20) (Int 22))) '(Vector Integer Integer))
;  (Prim
;   '+
;   (list
;    (Prim 'vector-ref (list (Var 'v) (Int 0)))
;    (Prim 'vector-ref (list (Var 'v) (Int 1))))))))

#;(define (type-check-exp env)
  (send (new type-check-Lvec-class) type-check-exp env))

#;(define (type-equal? t1 t2)
  (send (new type-check-Lvec-class) type-equal? t1 t2))

