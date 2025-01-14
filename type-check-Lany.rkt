#lang racket
(require "utilities.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Cfun.rkt")
(require "type-check-Llambda.rkt")
(provide type-check-Lany type-check-Lany-class)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Type Checker for the Any type and inject, project, etc.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; type-check-Lany

(define type-check-Lany-class
  (class type-check-Llambda-class
    (super-new)
    (inherit check-type-equal?)

    (define/override (operator-types)
      (append
       '((integer? . ((Any) . Boolean))
         (vector? . ((Any) . Boolean))
         (procedure? . ((Any) . Boolean))
         (void? . ((Any) . Boolean))
         (tag-of-any . ((Any) . Integer))
         (make-any . ((_ Integer) . Any))
         )
       (super operator-types)))

    (define/public (type-predicates)
      (set 'boolean? 'integer? 'vector? 'procedure? 'void?))

    (define/public (join-types t1 t2)
      (match (list t1 t2)
        [(list '_ t2) t2]
        [(list t1 '_) t1]
        [(list `(Vector ,ts1 ...)
               `(Vector ,ts2 ...))
         `(Vector ,@(for/list ([t1 ts1] [t2 ts2])
                      (join-types t1 t2)))]
        [(list `(,ts1 ... -> ,rt1)
               `(,ts2 ... -> ,rt2))
         `(,@(for/list ([t1 ts1] [t2 ts2])
               (join-types t1 t2))
           -> ,(join-types rt1 rt2))]
        [else
         t1]))

    (define/public (flat-ty? ty)
      (match ty
        [(or `Integer `Boolean '_ `Void)
         #t]
        ;; The following is a special case to handle programs
        ;; after closure conversion. -Jeremy
        [`(Vector ((Vector _) ,ts ... -> Any))
         (for/and ([t ts]) (eq? t 'Any))]
        [`(Vector ,ts ...)
         (for/and ([t ts]) (eq? t 'Any))]
        ['(Vectorof Any) #t]
        [`(,ts ... -> ,rt)
         (and (eq? rt 'Any) (for/and ([t ts]) (eq? t 'Any)))]
        [else
         #f]
        ))

    ;; 使用inject和project 创建静态类型Any语言
    (define/override (type-check-exp env)
      (lambda (e)
        (debug 'type-check-exp "Lany" e)
        (define recur (type-check-exp env))
        (match e
          ;; Change If to use join-types
          [(If cnd thn els)
           (define-values (cnd^ Tc) (recur cnd))
           (define-values (thn^ Tt) (recur thn))
           (define-values (els^ Te) (recur els))
           (check-type-equal? Tc 'Boolean cnd)
           (check-type-equal? Tt Te e)
           (values (If cnd^ thn^ els^) (join-types Tt Te))]
          
          [(Prim 'any-vector-length (list e1))
           (define-values (e1^ t1) (recur e1))
           (check-type-equal? t1 'Any e)
           (values (Prim 'any-vector-length (list e1^)) 'Integer)]
          
          [(Prim 'any-vectorof-length (list e1))
           (define-values (e1^ t1) (recur e1))
           (check-type-equal? t1 'Any e)
           (values (Prim 'any-vectorof-length (list e1^)) 'Integer)]
          
          [(Prim 'any-vector-ref (list e1 e2))
           (define-values (e1^ t1) (recur e1))
           (define-values (e2^ t2) (recur e2))
           (check-type-equal? t1 'Any e)
           (check-type-equal? t2 'Integer e)
           (values (Prim 'any-vector-ref (list e1^ e2^)) 'Any)]
          
          [(Prim 'any-vector-set! (list e1 e2 e3))
           (define-values (e1^ t1) (recur e1))
           (define-values (e2^ t2) (recur e2))
           (define-values (e3^ t3) (recur e3))
           (check-type-equal? t1 'Any e)
           (check-type-equal? t2 'Integer e)
           (check-type-equal? t3 'Any e)
           (values (Prim 'any-vector-set! (list e1^ e2^ e3^)) 'Void)]
          
          ;; inject 创建Any类型
          [(Inject e1 ty)
           (unless (flat-ty? ty)
             (error 'type-check "may only inject from flat type, not ~a" ty))
           (define-values (new-e1 e-ty) (recur e1))
           (check-type-equal? e-ty ty e)
           (values (Inject new-e1 ty) 'Any)]
          
          [(ValueOf e ty)
           (define-values (new-e e-ty) (recur e))
           (values (ValueOf new-e ty) ty)]
          
          ;; 使用Any
          [(Project e1 ty)
           (unless (flat-ty? ty)
             (error 'type-check "may only project to flat type, not ~a" ty))
           (define-values (new-e1 e-ty) (recur e1))
           (check-type-equal? e-ty 'Any e)
           (values (Project new-e1 ty) ty)]
          
          [(Prim pred (list e1))
           #:when (set-member? (type-predicates) pred)
           ;; The type predicates such as boolean? expect their argument to produce a tagged value
           (define-values (new-e1 e-ty) (recur e1))
           (check-type-equal? e-ty 'Any e)
           (values (Prim pred (list new-e1)) 'Boolean)]
          
          ;[(Exit)
          ; (values (Exit) '_)]
          [(Prim 'eq? (list arg1 arg2))
           (define-values (e1 t1) (recur arg1))
           (define-values (e2 t2) (recur arg2))
           (match* (t1 t2)
             ;; allow comparison of vectors of different element types
             [(`(Vector ,ts1 ...) `(Vector ,ts2 ...))   (void)]
             [(`(Vectorof ,t1) `(Vectorof ,t2))         (void)]
             [(other wise) (check-type-equal? t1 t2 e)])
           (values (Prim 'eq? (list e1 e2)) 'Boolean)]
          [else ((super type-check-exp env) e)])))

    ))

(define (type-check-Lany p)
  (send (new type-check-Lany-class) type-check-program p))


;; 解释的时候，将基本类型变成Tagged类型
;; 在编译时tagged类型如何表示？ 使用低位的3个bit表示
;; To make tagged values into first-class entities, we can give them a type called Any
;; define operations such as Inject and Project for creating and using them
;; tagged的类型为Any

;; 创建Tagged
;; The (Inject e T) form converts the value produced by expression e of type T into a tagged value.
;; 使用Tagged
;; The (Project e T) form either converts the tagged value produced by expression e into a value of type T
;; 里面的类型必须是 非终结符类型 ftype ::= Integer | Boolean | Void | (Vector Any...) | (Any... -> Any)
;; Note that in both Inject and Project, the type T is restricted to be a flat type (the nonterminal ftype)

