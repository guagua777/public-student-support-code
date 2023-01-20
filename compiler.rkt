#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([new-sym (gensym x)]
              [new-env (dict-set env x new-sym)])
         (Let new-sym ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp '()) e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Let x rhs body)
     (define new-rhs (rco-exp rhs))
     (define-values (new-body body-ss) (rco-atom body))
     (values new-body (append `((,x . ,new-rhs)) body-ss))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (append ss `((,tmp . ,(Prim op new-es)))))]))


;; rco-exp : exp -> exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     ;; an atomic expression and
     ;; an alist mapping temporary variables to complex subexpressions.
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets (append* sss) (Prim op new-es))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))

;(Program
; '()
; (Let
;  'x2019415
;  (Int 10)
;  (Let
;   'y2019416
;   (Let
;    'tmp2019417
;    (Prim '- (list (Int 100)))
;    (Prim '+ (list (Int 42) (Var 'tmp2019417))))
;   (Prim '+ (list (Var 'x2019415) (Var 'y2019416))))))

;; tail ::= (Return exp) | (Seq stmt tail)
;; The explicate_tail function takes an exp in LVar as input and produces a tail in CVar (see figure 2.13). 
(define (explicate-tail exp)
  (match exp
    [(Var x) (values (Return (Var x)) '())]
    [(Int n) (values (Return (Int n)) '())]
    [(Let lhs rhs body)
     ;; the right-hand side of a let executes before its body
     #;(let*-values
         ([(body-c0 body-vars) (explicate-tail body)]
          [(new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0)])
       (values new-tail (cons lhs (append new-rhs-vars body-vars))))
     
     (define-values (body-c0 body-vars) (explicate-tail body))
     (define-values (new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0))
     (values new-tail (cons lhs (append new-rhs-vars body-vars)))
     ]
    [(Prim op es)
     (values (Return (Prim op es)) '())]))

;; The explicate_assign function takes an exp in LVar, the variable to which it is to be assigned, and a tail in CVar for the code that comes after the assignment.
;; The explicate_assign function returns a tail in CVar.
;; the c parameter is used for accumulating the output
(define (explicate-assign r1exp v c)
  (match r1exp
    [(Int n)
     (values (Seq (Assign v (Int n)) c) '())]
    [(Prim 'read '())
     (values (Seq (Assign v (Prim 'read '())) c) '())]
    [(Prim '- (list e))
     (values (Seq (Assign v (Prim '- (list e))) c)
             '())] 
    [(Prim '+ (list e1 e2))
     (values (Seq (Assign v (Prim '+ (list e1 e2))) c)
             '())] 
    [(Var x)
     (values (Seq (Assign v (Var x)) c) '())]
    [(Let x e body) 
     (define-values (tail let-binds) (explicate-assign body v c))
     (define-values (tail^ let-binds^) (explicate-assign e (Var x) tail))
     (values tail^ (cons x (append let-binds let-binds^)))]
    [else
     (error "error explicate-assign ")]))
;     (printf "else v r1exp is ******* ~a ~a \n" v r1exp)
;     (values (Seq (Assign v r1exp) c) '())]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body)
     (begin
       (define-values (tail vars) (explicate-tail body))
       (printf "-=-=-=-=-=-=-= ~a ~a \n" tail vars)
       ;; contains an alist that associates the symbol locals with a list of all the variables used in the program. 
       (CProgram (cons (cons 'locals vars) info)
                 (list (cons 'start tail))))]))
  ;(error "TODO: code goes here (explicate-control)"))

(define (select-instr-atm a)
  (match a
    [(Int i) (Imm i)]
    [(Var _) a]))

(define (select-instr-assign v e)
  (match e
    [(Int i) 
     (list (Instr 'movq (list (select-instr-atm e) v)))]
    [(Var _)
     (list (Instr 'movq (list (select-instr-atm e) v)))]
    [(Prim 'read '())
     (list (Callq 'read_int)
           (Instr 'movq (list (Reg 'rax) v)))]
    [(Prim '- (list a))
     (list (Instr 'movq (list (select-instr-atm a) v))
           (Instr 'negq (list v)))]
    [(Prim '+ (list a1 a2))
     (list (Instr 'movq (list (select-instr-atm a1) v))
           (Instr 'addq (list (select-instr-atm a2) v)))]))

(define (select-instr-stmt stmt)
  (match stmt
    [(Assign (Var v) (Prim '+ (list (Var v1) a2))) #:when (equal? v v1)
     (list (Instr 'addq (list (select-instr-atm a2) (Var v))))]
    [(Assign (Var v) (Prim '+ (list a1 (Var v2)))) #:when (equal? v v2)
     (list (Instr 'addq (list (select-instr-atm a1) (Var v))))]
    [(Assign v e)
     (select-instr-assign v e)]))

(define (select-instr-tail t)
  (match t
    [(Seq stmt t*) 
     (append (select-instr-stmt stmt) (select-instr-tail t*))]
    [(Return (Prim 'read '())) 
     (list (Callq 'read_int) (Jmp 'conclusion))]
    [(Return e) (append
                 (select-instr-assign (Reg 'rax) e)
                 (list (Jmp 'conclusion)))]))

(define (select-instructions p)
  (match p
    [(Program info (CFG (list (cons 'start t))))
     (Program info
       (CFG (list (cons 'start (Block '() (select-instr-tail t))))))]))


;; select-instructions : C0 -> pseudo-x86
;(define (select-instructions p)
;  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
