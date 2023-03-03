#lang racket
;(HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
(HasType
 (Let
  'tmp212848
  (Int 1)
  (HasType
   (Let
    'tmp212849
    (Int 2)

    (Let
     '_
     (If
      (Prim
       '<
       (list
        (Prim '+ (list (GlobalValue 'free_ptr) (Int 16)))
        (GlobalValue 'fromspace_end)))
      (Void)
      (collect 16))
     (Let
      'vec212847
      (allocate 2 (Vector Integer Integer))
      ;; (HasType (Let var exp body) type)
      ;; 其中body可以为新的HasType
      (HasType
       (Let
        '_
        (Prim
         'vector-set!
         (list
          (HasType (Var 'vec212847) '(Vector Integer Integer))
          (Int 0)
          (Var 'tmp212848)))
        
        (HasType
         (Let
          '_
          (Prim
           'vector-set!
           (list
            (HasType (Var 'vec212847) '(Vector Integer Integer))
            (Int 1)
            (Var 'tmp212849)))
          (HasType (Var 'vec212847) '(Vector Integer Integer)))
         '(Vector Integer Integer))
        )
       '(Vector Integer Integer))

      ))
    )
   '(Vector Integer Integer)))
 '(Vector Integer Integer))


(let ([x0 e0])
  ...
    (let ([xn-1 en-1]) ;; 部分1 
      (let ([_ (if (< (+ (global-value free_ptr) bytes)
                      (global_value fromspace_end))
                   (void)
                   ;; bytes 是需要的字节数 = 8 + len*8
                   (collect bytes))]) 
        ;; len 是成员个数
        (let ([v (allocate len type)]);; 部分2
          (let ([_ (vector-set! v 0 x0)])
            ...
              (let ([_ (vector-set! v (- n 1) xn-1)]) ;; 部分3
                ;; 返回v
                ;; 一直嵌套到最里层
                v))))));; 部分4,也就是v

;The following shows the transformation of tuple creation into
;(1) a sequence of temporary variable bindings for the initializing expressions,
;(2) a conditional call to collect,
;(3) a call to allocate, and
;(4) the initialization of the tuple.
(let ([x0 e0])
  (let ([x1 e1]) ;; (1)
    (let ([_ (if (< ...)
                 (void)
                 (collect bytes))]) ;; (2)
      (let ([v (allocate len type)]) ;; (3)
        (let ([_ (vector-set! v 0 x0)])
          (let ([_ (vector-set! v 1 x1)])
            v)) ;; (4)
        ))))

