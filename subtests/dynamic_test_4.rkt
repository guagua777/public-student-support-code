(let ([x (vector 42 10 20)])
  (if (eq? (read) 1)
      ((lambda (x)
         (+ (- (vector-ref x 2)) 84)) x)
      (if (and
           (eq? #t #f)
           (eq? (vector-ref x 0) (vector-ref x 1)))
          (vector-set! x 0 100)
          (void))))
