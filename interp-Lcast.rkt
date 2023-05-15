#lang racket
;(require racket/fixnum)
(require "utilities.rkt")
(require "interp-Lany.rkt")
(provide interp-Lcast interp-Lcast-class)

(define interp-Lcast-class
  (class interp-Lany-class
    (super-new)
    (inherit apply-fun apply-inject apply-project)

    (define (guarded-vector-ref vec i)
      (match vec
        [`(vector-proxy ,proxy)
         (define val (guarded-vector-ref (vector-ref proxy 0) i))
         (define rd (vector-ref (vector-ref proxy 1) i))
         (apply-fun rd (list val) 'guarded-vector-ref)]
        [else (vector-ref vec i)]))

    (define (guarded-vector-set! vec i arg)
      (match vec
        [`(vector-proxy ,proxy)
         (define wr (vector-ref (vector-ref proxy 2) i))
         (define arg^ (apply-fun wr (list arg) 'guarded-vector-set!))
         (guarded-vector-set! (vector-ref proxy 0) i arg^)]
        [else (vector-set! vec i arg)]))

    (define (guarded-vector-length vec)
      (match vec
        [`(vector-proxy ,proxy)
         (guarded-vector-length (vector-ref proxy 0))]
        [else (vector-length vec)]))

    (define/override (interp-op op)
      (verbose "Lcast/interp-op" op)
      (match op
        ['vector-length guarded-vector-length]
        ['vector-ref guarded-vector-ref]
        ['vector-set! guarded-vector-set!]
        ['any-vector-ref (lambda (v i)
                           (match v [(Tagged v^ tg)
                                     (guarded-vector-ref v^ i)]))]
        ['any-vector-set! (lambda (v i a)
                            (match v [(Tagged v^ tg)
                                      (guarded-vector-set! v^ i a)]))]
        ['any-vector-length (lambda (v)
                              (match v [(Tagged v^ tg)
                                        (guarded-vector-length v^)]))]
        [else (super interp-op op)]
        ))

    (define/public (apply-cast v s t)
      (match* (s t)
        [(t1 t2) #:when (equal? t1 t2) v]
        [('Any t2) 
         (match t2
           [`(,ts ... -> ,rt)
            (define any->any `(,@(for/list ([t ts]) 'Any) -> Any))
            (define v^ (apply-project v any->any))
            (apply-cast v^ any->any `(,@ts -> ,rt))]
           [`(Vector ,ts ...)
            (define vec-any `(Vector ,@(for/list ([t ts]) 'Any)))
            (define v^ (apply-project v vec-any))
            (apply-cast v^ vec-any `(Vector ,@ts))]
           [else (apply-project v t2)])]
        [(t1 'Any) 
         (match t1
           [`(,ts ... -> ,rt)
            (define any->any `(,@(for/list ([t ts]) 'Any) -> Any))
            (define v^ (apply-cast v `(,@ts -> ,rt) any->any))
            (apply-inject v^ (any-tag any->any))]
           [`(Vector ,ts ...)
            (define vec-any `(Vector ,@(for/list ([t ts]) 'Any)))
            (define v^ (apply-cast v `(Vector ,@ts) vec-any))
            (apply-inject v^ (any-tag vec-any))]
           [else (apply-inject v (any-tag t1))])]
        [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))
         (define x (gensym 'x))
         (define cast-reads (for/list ([t1 ts1] [t2 ts2])
                              (Function (list x) (Cast (Var x) t1 t2) '())))
         (define cast-writes
           (for/list ([t1 ts1] [t2 ts2])
             (Function (list x) (Cast (Var x) t2 t1) '())))
         `(vector-proxy ,(vector v (apply vector cast-reads)
                                 (apply vector cast-writes)))]
        [(`(,ts1 ... -> ,rt1) `(,ts2 ... -> ,rt2))
         (define xs (for/list ([t2 ts2]) (gensym 'x)))
         (Function xs (Cast
                       (Apply (Value v)
                              (for/list ([x xs][t1 ts1][t2 ts2])
                                (Cast (Var x) t2 t1)))
                       rt1 rt2)
                   '())]
        ))
    
    (define/override ((interp-exp env) e)
      (define (recur e) ((interp-exp env) e))
      (verbose "Lcast/interp-exp" e)
      (define result
        (match e
          [(Value v) v]
          [(Cast e src tgt)
           (apply-cast (recur e) src tgt)]
          [else ((super interp-exp env) e)]))
      (verbose "Lcast/interp-exp" e result)
      result)
    
    ))

(define (interp-Lcast p)
  (send (new interp-Lcast-class) interp-program p))




;; =====================================================

;
;(define (consistent? t1 t2)
;  (match* (t1 t2)
;    [('Integer 'Integer) #t]
;    [('Boolean 'Boolean) #t]
;    [('Void 'Void) #t]
;    [('Any t2) #t]
;    [(t1 'Any) #t]
;    [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))
;     (for/and ([t1 ts1] [t2 ts2]) (consistent? t1 t2))]
;    [(`(,ts1 ... -> ,rt1) `(,ts2 ... -> ,rt2))
;     (and (for/and ([t1 ts1] [t2 ts2]) (consistent? t1 t2))
;          (consistent? rt1 rt2))]
;    [(other wise) #f]))
;
;
;(consistent? '(Any -> Any) '(Integer -> Integer))
;
;
;(define (map [f : (Integer -> Integer)] ;; f的类型为Integer -> Integer
;             [v : (Vector Integer Integer)])
;  : (Vector Integer Integer)
;  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
;
;;; 类型为 Any -> Any
;(define (inc x) (+ x 1))
;
;(vector-ref (map inc (vector 0 41)) 1)
;
;;;=========
;
;(define (map [f : (Integer -> Integer)] ;; f的类型为Integer -> Integer
;             [v : (Vector Integer Integer)])
;  : (Vector Integer Integer)
;  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
;
;;; 类型为 Any -> Any
;(define (inc x) (+ x 1))
;;; 类型为 -> Boolean
;(define (true)
;  #t)
;;; Running this program with input 1 triggers an error
;;; 输入为1的时候，触发error
;;; 类型为 Any -> 
;(define (maybe_inc x)
;  (if (eq? 0 (read))
;      ;; Integer
;      (inc x)
;      ;; Boolean
;      (true)))
;
;(vector-ref (map maybe_inc (vector 0 41)) 0)
;
;
;;;============
;;The idea is that Cast is inserted every time the type checker encounters
;;two types that are consistent but not equal.
;
;
;(define (map [f : (Integer -> Integer)] ;; Integer -> Integer
;             [v : (Vector Integer Integer)])
;  : (Vector Integer Integer)
;  (vector (f (vector-ref v 0)) (f (vector-ref v 1))))
;
;;; Any -> Any
;(define (inc [x : Any]) : Any
;  ;; Any 转 Integer ,然后 Integer 转 Any
;  (cast (+ (cast x Any Integer) 1) Integer Any))
;
;;; -> Any
;(define (true) : Any
;  ;; Boolane 转 Any
;  (cast #t Boolean Any))
;;; Any -> Any
;;; 这个为什么没有cast
;
;;When the maybe_inc function flows through this cast at runtime,
;;we don’t know whether it will return an integer,
;;because that depends on the input from the user.
;
;;The LCast interpreter therefore delays the checking of the cast until
;;the function is applied. To do so it wraps maybe_inc in a new function
;;that casts its parameter from Integer to Any,
;;applies maybe_inc, and then casts the return value from Any to Integer
;(define (maybe_inc [x : Any]) : Any
;  (if (eq? 0 (read))
;      (inc x)
;      (true)))
;;;;;;;;;;;;;;;;;;; Any -> Any 转 Integer -> Integer
;(vector-ref (map (cast maybe_inc (Any -> Any) (Integer -> Integer))
;                 (vector 0 41)) 0)
;
;;;==============================
;;; 原地map 10.11
;
;;; 一种方式是在内部创建一个新的tuple
;;; 一种方式是创建一个代理
;;; Instead the interpreter needs to create a new kind of value,
;;; a proxy, that intercepts every tuple operation.
;;; 该代理， 读的时候如何处理，写的时候如何处理
;;; 读的时候应用cast，此处将0 Integer 转为 Any
;;; 写的时候应用cast，此处将带Tagged的Any转为Integer，（因为此处tagged的类型为Integer）
;(define (map_inplace [f : (Any -> Any)]
;                     [v : (Vector Any Any)]) : Void
;  (begin
;    (vector-set! v 0 (f (vector-ref v 0)))
;    (vector-set! v 1 (f (vector-ref v 1)))))
;
;(define (inc x)
;  (+ x 1))
;
;(let ([v (vector 0 41)])
;  ;; We apply map_inplace to a tuple of integers
;  ;; so the type checker inserts a cast from
;  ;; (Vector Integer Integer) to (Vector Any Any).
;  (begin (map_inplace inc v) (vector-ref v 1)))
;
;;;=====================================
;; 10.12
;
;(define (map_inplace [f : (Any -> Any)] v) : Void
;  (begin
;    (vector-set! v 0 (f (vector-ref v 0)))
;    (vector-set! v 1 (f (vector-ref v 1)))))
;
;(define (inc x)
;  (+ x 1))
;
;(let ([v (vector 0 41)]) ;; v的类型为 (Vector Integer Integer)
;  ;; 插入一个cast
;  ;; so the type checker inserts a cast to Any.
;  ;; A first thought is to use Inject, but that doesn’t work
;  ;; because (Vector Integer Integer) is not a flat type.
;  ;; Instead, we must first cast to (Vector Any Any), which is flat, and then inject to Any.
;  (begin (map_inplace inc v) (vector-ref v 1)))
;
;

