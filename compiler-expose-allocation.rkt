#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require data/queue)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Cvec.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

(provide (all-defined-out))


(define/public (expose-alloc-vector es vec-type alloc-exp) ;; es为数据，vec-type为对应的类型
  (define e* (for/list ([e es]) (expose-alloc-exp e)))
  ;; 1. evaluate the e* and let-bind them to x*
  ;; 2. allocate the vector
  ;; 3. initialize the vector
  ;; Setp 1 comes before step 2 because the e* may trigger GC!
  ;; 在分配之前有可能会触发gc，因为分配之前首先要检查是否有足够的空间，如果没有需要先gc
  (define len (length e*))
  (define size (* (+ len 1) 8))
  (define vec (gensym 'alloc))

  ;; step 1
  (define-values (bndss inits)
    (for/lists (l1 l2) ([e e*])
      (cond [(atm? e) (values '() e)]
            [else
             (define tmp (gensym 'vecinit))
             (values (list (cons tmp e)) (Var tmp))])))
  (define bnds (append* bndss))

  ;; step 3
  (define init-vec (foldr
                    (lambda (init n rest)
                      (let ([v (gensym '_)])
                        (Let v (Prim 'vector-set! (list (Var vec) (Int n) init)) rest)))
                    (Var vec)
                    inits
                    (range len)))

  ;; step 2 (and include step 3)
  (define voidy (gensym '_))
  (define alloc-init-vec
    (Let voidy
         (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr)
                                           (Int size)))
                            (GlobalValue 'fromspace_end)))
             (Void)
             (Collect size))
         (Let vec alloc-exp init-vec)))

  ;; combine 1 and 2-3
  (make-lets bnds alloc-init-vec))

(define/public (expose-alloc-exp e)
  (verbose "expose alloc exp" e)
  (match e
    [(HasType (Prim 'vector es) vec-type) ;; 创建vector，此时需要进行分配到堆上 page 108
     (define len (length es))
     (expose-alloc-vector es vec-type (Allocate len vec-type))]
    [(Prim 'vector es)
     (error "expose-alloc-exp expected has-type around vector ~a" e)]
    #;[(HasType e t)
     (HasType (expose-alloc-exp e) t)]
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(If cnd thn els)
     (If (expose-alloc-exp cnd)
         (expose-alloc-exp thn)
         (expose-alloc-exp els))]
    [(Prim op es)
     (define new-es (map (lambda (e)
                           (expose-alloc-exp e))
                         es))
     (Prim op new-es)]
    [(Let x rhs body)
     (Let x (expose-alloc-exp rhs)
          (expose-alloc-exp body))]))

(define/public (expose-allocation e)
  (verbose "expose-allocation" e)
  (match e
    [(Program info body)
     (Program info (expose-alloc-exp body))]
    [else
     (error "expose allocation unmatched" e)]))