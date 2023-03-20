(define (map [f : (Integer -> Integer)]
             [v1 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v2 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v3 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v4 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v5 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v6 : (Vector Integer Integer Integer Integer Integer Integer Integer)]
             [v7 : (Vector Integer Integer Integer Integer Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer Integer)
  (vector (f (vector-ref v1 0))
          (f (vector-ref v2 1))
          (f (vector-ref v3 2))
          (f (vector-ref v4 3))
          (f (vector-ref v5 4))
          (f (vector-ref v6 5))
          (f (vector-ref v7 6))
          ))
(define (inc [x : Integer]) : Integer
  (+ x 1))
(vector-ref (map inc
                 (vector 1 2 3 4 5 6 7)
                 (vector 11 22 33 44 55 66 77)
                 (vector 111 222 333 444 555 666 777)
                 (vector 1111 2222 3333 4444 5555 6666 7777)
                 (vector 11111 22222 33333 44444 55555 66666 77777)
                 (vector 111111 222222 333333 444444 555555 666666 777777)
                 (vector 1111111 2222222 3333333 4444444 5555555 6666666 7777777)
                 (vector 11111111 22222222 33333333 44444444 55555555 66666666 77777777)) 5)
