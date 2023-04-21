#lang racket
(require racket/fixnum)
(require "utilities.rkt" (prefix-in runtime-config: "runtime-config.rkt"))
(provide interp-Ldyn interp-Ldyn-prog)

;; Note to maintainers of this code:
;;   A copy of this interpreter is in the book and should be
;;   kept in sync with this code.

(define (interp-op op)
  (match op
    ['+ fx+]
    ['- fx-]
    ['read read-fixnum]
    ['not (lambda (v) (match v [#t #f] [#f #t]))]
    ['< (lambda (v1 v2)
	  (cond [(and (fixnum? v1) (fixnum? v2))
		 (< v1 v2)]))]
    ['<= (lambda (v1 v2)
	   (cond [(and (fixnum? v1) (fixnum? v2))
		  (<= v1 v2)]))]
    ['> (lambda (v1 v2)
	  (cond [(and (fixnum? v1) (fixnum? v2))
		 (> v1 v2)]))]
    ['>= (lambda (v1 v2)
	   (cond [(and (fixnum? v1) (fixnum? v2))
		  (>= v1 v2)]))]
    ['boolean? boolean?]
    ['integer? fixnum?]
    ['void? void?]
    ['vector? vector?]
    ['vector-length vector-length]
    ['procedure? (match-lambda [(Function xs body env) #t]
                               [else #f])]
    [else (error 'interp-op "unknown operator ~a" op)]))

(define (op-tags op)
  (match op
    ['+ '((Integer Integer))]
    ['- '((Integer Integer) (Integer))]
    ['read '(())]
    ['not '((Boolean))]
    ['< '((Integer Integer))]
    ['<= '((Integer Integer))]
    ['> '((Integer Integer))]
    ['>= '((Integer Integer))]
    ['vector-length '((Vector))]
    ))

(define type-predicates
  (set 'boolean? 'integer? 'vector? 'procedure? 'void?))

(define (tag-value v)
  (cond [(boolean? v) (Tagged v 'Boolean)]
        [(fixnum? v) (Tagged v 'Integer)]
        [(procedure? v) (Tagged v 'Procedure)]
        [(vector? v) (Tagged v 'Vector)]
        [(void? v) (Tagged v 'Void)]
        [else (error 'tag-value "unidentified value ~a" v)]))

(define (check-tag val expected ast)
  (define tag (Tagged-tag val))
  (unless (eq? tag expected)
    (error 'trapped-error "expected ~a tag, not ~a\nin ~v" expected tag ast)))

(define ((interp-Ldyn-exp env) ast)
  (verbose 'interp-Ldyn "start" ast)
  (define recur (interp-Ldyn-exp env))
  (define result
    (match ast ;; 为什么没有Closure
      [(Void)
       ;(Tagged void 'Void)]
       ;(tag-value ast)]
       (Tagged 0 'Integer)]
       ;(Void)]
      [(Var x) (lookup x env)]
      [(FunRef f n) (lookup f env)]
      [(Int n) (Tagged n 'Integer)]
      [(Bool b) (Tagged b 'Boolean)]
      [(Lambda xs rt body)
       ;; lambda 会转化为 Tagged
       (Tagged (Function xs body env) 'Procedure)]
      [(Prim 'vector es)
       (Tagged (apply vector (for/list ([e es]) (recur e))) 'Vector)]
      [(Prim 'vector-ref (list e1 e2))
       (define vec (recur e1)) (define i (recur e2))
       (check-tag vec 'Vector ast) (check-tag i 'Integer ast)
       (unless (< (Tagged-value i) (vector-length (Tagged-value vec)))
         (error 'trapped-error "index ~a too big\nin ~v" (Tagged-value i) ast))
       (vector-ref (Tagged-value vec) (Tagged-value i))]
      [(Prim 'vector-set! (list e1 e2 e3))
       (define vec (recur e1)) (define i (recur e2)) (define arg (recur e3))
       (check-tag vec 'Vector ast) (check-tag i 'Integer ast)
       (unless (< (Tagged-value i) (vector-length (Tagged-value vec)))
         (error 'trapped-error "index ~a too big\nin ~v" (Tagged-value i) ast))
       (vector-set! (Tagged-value vec) (Tagged-value i) arg)
       (Tagged (void) 'Void)]
      [(Let x e body)
       ((interp-Ldyn-exp (cons (cons x (recur e)) env)) body)]
      [(Prim 'and (list e1 e2)) (recur (If e1 e2 (Bool #f)))]
      [(Prim 'or (list e1 e2))
       (define v1 (recur e1))
       (match (Tagged-value v1) [#f (recur e2)] [else v1])]
      [(Prim 'not (list e1))
       (match (Tagged-value (recur e1)) [#f (Tagged #t 'Boolean)]
              [else (Tagged #f 'Boolean)])]
      [(Prim 'eq? (list e1 e2))
       (Tagged (equal? (recur e1) (recur e2)) 'Boolean)]
      [(Prim op (list e1))
       #:when (set-member? type-predicates op)
       (tag-value ((interp-op op) (Tagged-value (recur e1))))]
      [(Prim op es)
       (define args (map recur es))
       (define tags (for/list ([arg args]) (Tagged-tag arg)))
       (unless (for/or ([expected-tags (op-tags op)])
                 (equal? expected-tags tags))
         (error 'trapped-error "illegal argument tags ~a\nin ~v" tags ast))
       (tag-value
        (apply (interp-op op) (for/list ([a args]) (Tagged-value a))))]
      [(If q t f)
       (match (Tagged-value (recur q)) [#f (recur f)] [else (recur t)])]
      [(Apply f es)
       (define new-f (recur f))
       (printf "f is ~a, new-f is ~a \n" f new-f)
       (define args (map recur es))
       (check-tag new-f 'Procedure ast)
       (define f-val (Tagged-value new-f))
       (match f-val 
         [(Function xs body lam-env)
          (unless (eq? (length xs) (length args))
            (error 'trapped-error "number of arguments ~a != arity ~a\nin ~v"
                   (length args) (length xs) ast))
          ;; 构建新的环境
          (define new-env (append (map cons xs args) lam-env))
          ;; 解释body
          ((interp-Ldyn-exp new-env) body)]
         [else (error "interp-Ldyn-exp, expected function, not" f-val)])]))
  (verbose 'interp-Ldyn ast result)
  result)

(define (interp-Ldyn-def ast)
  (match ast
    [(Def f xs rt info body)
     (mcons f (Function xs body '()))]))

;; This version is for source code in Ldyn.
(define (interp-Ldyn ast)
  (match ast
    [(ProgramDefsExp info ds body)
     (define top-level (map (lambda (d) (interp-Ldyn-def d)) ds))
     (for/list ([b top-level])
       (set-mcdr! b (match (mcdr b)
                      [(Function xs body '())
                       ;; 变成 tagged
                       (Tagged (Function xs body top-level) 'Procedure)])))
     (define result ((interp-Ldyn-exp top-level) body))
     (check-tag result 'Integer ast)
     (Tagged-value result)]
    [(Program info body) (interp-Ldyn (ProgramDefsExp info '() body))]))

;; This version is for after shrink.
(define (interp-Ldyn-prog ast)
  (match ast
    [(ProgramDefs info ds)
     (define top-level (map (lambda (d) (interp-Ldyn-def d)) ds))
     (for/list ([b top-level])
       (set-mcdr! b (match (mcdr b)
                      [(Function xs body '())
                       (Tagged (Function xs body top-level) 'Procedure)])))
     (define result ((interp-Ldyn-exp top-level) (Apply (Var 'main) '())))
     (check-tag result 'Integer ast)
     (Tagged-value result)]))


(interp-Ldyn (ProgramDefsExp '() '() (Int 42)))

(interp-Ldyn (ProgramDefsExp '() '() (Apply (Lambda '(x) 'Any (Var 'x)) (list (Int 42)))))

(interp-Ldyn 
 (ProgramDefsExp
  '()
  (list (Def 'id '(x) 'Any '() (Var 'x)))
  (Apply (Var 'id) (list (Int 42)))))

(interp-Ldyn 
 (ProgramDefsExp
  '()
  '()
  (Let
   'x
   (Prim 'vector (list (Int 42) (Int 42) (Int 42)))
   (If
    (Prim 'read '())
    (Apply
     (Lambda
      '(x)
      'Any
      (Prim
       '+
       (list
        (Prim '- (list (Prim 'vector-ref (list (Var 'x) (Int 2)))))
        (Int 84))))
     (list (Var 'x)))
    (If
     (Prim
      'and
      (list
       (Prim 'eq? (list (Bool #t) (Bool #f)))
       (Prim
        'eq?
        (list
         (Prim 'vector-ref (list (Var 'x) (Int 0)))
         (Prim 'vector-ref (list (Var 'x) (Int 1)))))))
     (Prim 'vector-ref (list (Var 'x) (Int 0)))
     (Void))))))

(interp-Ldyn 
 (ProgramDefsExp
  '()
  '()
  (Let
   'x
   (Prim 'vector (list (Int 42) (Int 10) (Int 20)))
   (If
    (Prim 'eq? (list (Prim 'read '()) (Int 1)))
    (Apply
     (Lambda
      '(x)
      'Any
      (Prim
       '+
       (list
        (Prim '- (list (Prim 'vector-ref (list (Var 'x) (Int 2)))))
        (Int 84))))
     (list (Var 'x)))
    (If
     (Prim
      'and
      (list
       (Prim 'eq? (list (Bool #t) (Bool #f)))
       (Prim
        'eq?
        (list
         (Prim 'vector-ref (list (Var 'x) (Int 0)))
         (Prim 'vector-ref (list (Var 'x) (Int 1)))))))
     (Prim 'vector-ref (list (Var 'x) (Int 0)))
     (Void))))))


(interp-Ldyn 
 (ProgramDefsExp
  '()
  '()
  (Let
   'x
   (Prim 'vector (list (Int 42) (Int 10) (Int 20)))
   (If
    (Prim 'eq? (list (Prim 'read '()) (Int 1)))
    (Apply
     (Lambda
      '(x)
      'Any
      (Prim
       '+
       (list
        (Prim '- (list (Prim 'vector-ref (list (Var 'x) (Int 2)))))
        (Int 84))))
     (list (Var 'x)))
    (If
     (Prim
      'and
      (list
       (Prim 'eq? (list (Bool #t) (Bool #f)))
       (Prim
        'eq?
        (list
         (Prim 'vector-ref (list (Var 'x) (Int 0)))
         (Prim 'vector-ref (list (Var 'x) (Int 1)))))))
     (Prim 'vector-set! (list (Var 'x) (Int 0) (Int 100)))
     (Void))))))
