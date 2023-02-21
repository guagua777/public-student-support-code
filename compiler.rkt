#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

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

;(define (type-check-exp env)
;  (lambda (e)
;    (match e
;      [(Var x) (dict-ref env x)]
;      [(Int n) 'Integer]
;      [(Bool b) 'Boolean]
;      [(Prim op args) ((type-check-prim env) e)]
;      [(Let x e body)
;       (define Te ((type-check-exp env) e))
;       (define Tb ((type-check-exp (dict-set env x Te)) body))
;       Tb]
;      [(If cnd cnsq alt)
;       (unless (eqv? 'Boolean ((type-check-exp env) cnd))
;         (error "condition given to if should be bool, given " cnd))
;       (define Tc ((type-check-exp env) cnsq))
;       (define Ta ((type-check-exp env) alt))
;       (unless (equal? Tc Ta)
;         (error (string-append "consequent and alternative in if should "
;                               "have same type, given")
;                (list Tc Ta)))
;       Tc]
;      [else
;       (error "type-check-exp couldn't match" e)])))
;
;(define (type-check-prim env)
;  (lambda (prim)
;    (let ([recur (type-check-exp env)])
;      (match prim
;        [(Prim 'read (list)) 'Integer]
;        [(Prim 'eq? (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (eqv? Te1 Te2)
;             (and (eqv? Te1 Te1)
;                  (or (eqv? Te1 'Integer)
;                      (eqv? Te1 'Boolean)))
;             'Boolean
;             (error "eq? should take two ints or two bools, given " (list e1 e2)))]
;        [(Prim '< (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Boolean
;             (error "< should take two ints, given " (list e1 e2)))]
;        [(Prim '<= (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Boolean
;             (error "<= should take two ints, given " (list e1 e2)))]
;        [(Prim '> (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Boolean
;             (error "> should take two ints, given " (list e1 e2)))]
;        [(Prim '>= (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Boolean
;             (error ">= should take two ints, given " (list e1 e2)))]
;        [(Prim '+ (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Integer
;             (error "+ should take two ints, given " (list e1 e2)))]
;        [(Prim '- (list e))
;         (define Te (recur e))
;         (if (eqv? Te 'Integer)
;             'Integer
;             (error "- should take one int, given " (list e)))]
;        [(Prim '- (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Integer)
;                  (eqv? Te2 'Integer))
;             'Integer
;             (error "- should take two ints, given " (list e1 e2)))]
;        [(Prim 'and (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Boolean)
;                  (eqv? Te2 'Boolean))
;             'Boolean
;             (error "and should take two bools, given " (list e1 e2)))]
;        [(Prim 'or (list e1 e2))
;         (define Te1 (recur e1))
;         (define Te2 (recur e2))
;         (if (and (eqv? Te1 'Boolean)
;                  (eqv? Te2 'Boolean))
;             'Boolean
;             (error "or should take two bools, given " (list e1 e2)))]
;        [(Prim 'not (list e))
;         (define Te (recur e))
;         (if (eqv? Te 'Boolean)
;             'Boolean
;             (error "not should take one bool, given " (list e)))]))))
;             
;(define (type-check p)
;  (match p
;    [(Program info body)
;     (define Tb ((type-check-exp '()) body))
;     (unless (equal? Tb 'Integer)
;       (error "result of the program must be an integer, not " Tb))
;     (Program info body)]))


;(define (check-bool e) 
;    (match e
;        ['Boolean 'Boolean]
;        [else (error "expected Boolean but got" e)]
;        ))
;
;(define (check-int e) 
;    (match e
;        ['Integer 'Integer]
;        [else (error "expected Integer but got" e)]
;        ))
;
;(define (check-eq ts)
;    (if (equal? (first ts) (last ts))
;        (void)
;        (error "Cannot compare items of different types" ts)))
;
;(define (type-check-op op ts)
;    (match op
;        ['read 'Integer]
;        ['+ (for ([t ts]) (check-int t)) 'Integer]
;        ['- (for ([t ts]) (check-int t)) 'Integer]
;        ['not (for ([t ts]) (check-bool t)) 'Boolean]
;        ['and (for ([t ts]) (check-bool t)) 'Boolean]
;        ['or (for ([t ts]) (check-bool t)) 'Boolean]
;        ['eq? (check-eq ts) 'Boolean]
;        ['cmp (check-eq ts) 'Boolean]
;        ['< (for ([t ts]) (check-int t)) 'Boolean]
;        ['<= (for ([t ts]) (check-int t)) 'Boolean]
;        ['> (for ([t ts]) (check-int t)) 'Boolean]
;        ['>= (for ([t ts]) (check-int t)) 'Boolean]
;        [else (error "unknown operator" op)]
;))
;
;(define (type-check-exp env)
;  (lambda (e)
;    (match e
;      [(Var x) (dict-ref env x)]
;      [(Int n) 'Integer]
;      [(Bool b) 'Boolean]
;      [(Let x e body)
;        (define Te ((type-check-exp env) e))
;        (define Tb ((type-check-exp (dict-set env x Te)) body))
;        Tb]
;
;      [(If e1 e2 e3)
;       (define T1 ((type-check-exp env) e1))
;       (unless (equal? T1 'Boolean) 
;         (error "Conditional of if statement must resolve to a boolean. Was " T1))
;       (define T2 ((type-check-exp env) e2))
;       (define T3 ((type-check-exp env) e3))
;       (unless (equal? T2 T3) 
;         (error "Return types of both branches of If must match. Got" T2 " and " T3))
;       T2]
;      [(Prim op es)
;        (define ts
;           (for/list ([e es]) ((type-check-exp env) e)))
;        (define t-ret (type-check-op op ts))
;        t-ret]
;      [else
;       (error "type-check-exp couldn't match" e)])))
;
;(define (type-checker e)
;    (match e
;      [(Program info body)
;       (define Tb ((type-check-exp '()) body))
;       (unless (equal? Tb 'Integer)
;         (error "result of the program must be an integer, not " Tb))
;       (Program info body)]
;      ))


;; 想一想环境中保存的是什么
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let* ([new-sym (gensym x)]
              [new-env (dict-set env x new-sym)])
         (Let new-sym ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e)
     (Program info ((uniquify-exp '()) e))]))

;(Program
; '()
; (If
;  (Let 'x4501192 (Int 100) (Prim '> (list (Var 'x4501192) (Int 10))))
;  (If
;   (Prim
;    'and
;    (list (Prim '> (list (Int 10) (Int 1))) (Prim '> (list (Int 10) (Int 2)))))
;   (Int 10)
;   (Int 20))
;  (Int 30)))

;(and e1 e2) ⇒ (if e1 e2 #f)
;(or e1 e2) ⇒ (if e1 #t e2)

(define shrink-exp
  (lambda (e)
    (match e
      [(Prim 'and (list e1 e2))
       (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
      [(Prim 'or (list e1 e2))
       (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
      [(Prim op (list e1))
       (Prim op (list (shrink-exp e1)))]
      [(Prim op (list e1 e2))
       (Prim op (list (shrink-exp e1) (shrink-exp e2)))]
      [(Let x e1 body)
       (Let x (shrink-exp e1) (shrink-exp body))]
      [(If cnd thn els)
       (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
      [else e])))
      
      
(define shrink
  (lambda (p)
    (match p
      [(Program info e)
       (Program info (shrink-exp e))])))

;for/list
;与
;for/lists的区别
;
;(for/list 待遍历的集合 对元素的处理)
;(for/lists 结果集values 待遍历的集合 对元素的处理)


;; 思路是什么?
;; (+ 5 (- 6))
;; (let ([tmp4735188 (- 6)])
;;    (+ 5 tmp4735188))
;; 将复杂表达式 转换成 原子表达式（在这期间会生成临时变量，因此需要记录临时变量和对应的复杂表达式）
;(- 10) ⇒  tmp.1
;          ((tmp.1 . (- 10)))

;(define (rco-atom e)
;  (match e
;    [(Var x) (values (Var x) '())]
;    [(Int n) (values (Int n) '())]
;    [(Let x rhs body)
;     ;; 想一想返回的应该是什么？
;     ;; 最后的表达式，以及最后表达式中变量和原子表达式的对应关系列表
;     ;; 变成atom之后的表达式，以及中间变量与对应的atom表达式的对应列表
;     (define new-rhs (rco-exp rhs))
;     (define-values (new-body body-ss) (rco-atom body))
;     (values new-body (append `((,x . ,new-rhs)) body-ss))]
;    [(Prim op es)
;     (define-values (new-es sss)
;       (for/lists (l1 l2) ([e es]) (rco-atom e)))
;     (define ss (append* sss))
;     (define tmp (gensym 'tmp))
;     (values (Var tmp)
;             (append ss `((,tmp . ,(Prim op new-es)))))]))


;; rco-exp : exp -> exp
;; 最后会变成一个let
;; 返回最后的结果
;(define (rco-exp e)
;  (match e
;    [(Var x) (Var x)]
;    [(Int n) (Int n)]
;    [(Let x rhs body)
;     (Let x (rco-exp rhs) (rco-exp body))]
;    [(Prim op es)
;     ;; an atomic expression and
;     ;; an alist mapping temporary variables to complex subexpressions.
;     (define-values (new-es sss)
;       (for/lists (l1 l2) ([e es]) (rco-atom e)))
;     (make-lets (append* sss) (Prim op new-es))]))

;; remove-complex-opera* : R1 -> R1
;(define (remove-complex-opera* p)
;  (match p
;    [(Program info e)
;     (Program info (rco-exp e))]))

;; resolve1
;(define (rco-atom e)
;  (match e
;      [(Var x) (values (Var x) '())]
;      [(Int n) (values (Int n) '())]
;      [(Bool bool) (values (Bool bool) '())]
;      [(Let x e body)
;       (define tmp (gensym "tmp"))
;       (define-values (e-val e-alist) (rco-atom e))
;       (values (Var tmp) (append e-alist  `((,tmp . ,(Let x e-val (rco-exp body))))))]
;      [(Prim op es)
;       (define tmp (gensym "tmp"))
;       (define-values (new-es bs)
;         (for/lists (l1 l2) ([e es])
;           (rco-atom e)))
;       (values (Var tmp) (append bs `((,tmp . ,(Prim op new-es)))))]
;      [(If cond exp else)
;       (define tmp (gensym "tmp"))
;       (define cond-val (rco-exp cond))
;       (define exp-val (rco-exp exp))
;       (define else-val (rco-exp else))
;       (values (Var tmp) `((,tmp . ,(If cond-val exp-val else-val))))]
;      ))
;
;(define (rco-exp e)
;  (match e
;      [(Var x) (Var x)]
;      [(Int n) (Int n)]
;      [(Bool bool) (Bool bool)]
;      [(Let x e body)
;       (begin (define e-val (rco-exp e))
;              (Let x e-val (rco-exp body)))]
;      [(Prim op es)
;       (let [(exps (split-pairs (for/list ([e es]) 
;                                     (begin (define-values (var alist) (rco-atom e)) 
;                                            `(,var . ,alist)))))]
;         (expand-alist (cdr exps) (Prim op (car exps))))]
;      [(If cond exp else)
;       (define exp-var (rco-exp exp))
;       (define else-var (rco-exp else))
;       (define cond-var (rco-exp cond))
;       (If cond-var exp-var else-var)]
;      ))
;
;(define (remove-complex-opera* p)
;  (match p
;    [(Program info e)
;     (Program info (rco-exp e))]
;    ))


(define (remove-complex-opera* p)
    (match p
      [(Program info e)
       (Program info (rco-exp e))]))

(define (rco-atom e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
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
             (append ss `((,tmp . ,(Prim op new-es)))))]
    [(If e1 e2 e3)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (define ss (append* sss))
     (define tmp (gensym 'tmp))
     (match new-es
	    [(list e1 e2 e3)
	     (values (Var tmp)
             (append ss `((,tmp . ,(If e1 e2 e3)))))])]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x rhs body)
     (Let x (rco-exp rhs) (rco-exp body))]
    [(Prim op es)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e es]) (rco-atom e)))
     (make-lets^ (append* sss) (Prim op new-es))]
    [(If e1 e2 e3)
     (define-values (new-es sss)
       (for/lists (l1 l2) ([e (list e1 e2 e3)]) (rco-atom e)))
     (match new-es
	    [(list e1 e2 e3)
	     (make-lets^ (append* sss) (If e1 e2 e3))])]
    ))



;; tail ::= (Return exp) | (Seq stmt tail)
;; The explicate_tail function takes an exp in LVar as input
;; and produces a tail in CVar (see figure 2.13). 
;(define (explicate-tail exp)
;  (match exp
;    [(Var x) (values (Return (Var x)) '())]
;    [(Int n) (values (Return (Int n)) '())]
;    ;; 先想想应该返回的是什么
;    ;; 应该返回的是顺序的赋值表达式列表，是个Seq，对let中变量和值进行赋值
;    [(Let lhs rhs body)
;     ;; the right-hand side of a let executes before its body
;;     (let*-values
;;         ([(body-c0 body-vars) (explicate-tail body)]
;;          [(new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0)])
;;       (values new-tail (cons lhs (append new-rhs-vars body-vars))))
;     ;; body-vars为body中的变量
;     ;; body-c0为tail，即为(Return exp) 或者是 (Seq stmt tail)
;     (define-values (body-c0 body-vars) (explicate-tail body))
;     ;; (printf "exp is ~a , body-c0 is ------ ~a \n" exp body-c0)
;     (define-values (new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0))
;     (values new-tail (cons lhs (append new-rhs-vars body-vars)))
;     ]
;    [(Prim op es)
;     (values (Return (Prim op es)) '())]))

;; The explicate_assign function takes an exp in LVar,
;; the variable to which it is to be assigned,
;; and a tail in CVar for the code that comes after the assignment.
;; The explicate_assign function returns a tail in CVar.
;; the c parameter is used for accumulating the output
;; 把r1exp赋值给变量v
;;想想返回值是什么？
;; 对变量进行赋值后，形成的Seq
;(define (explicate-assign r1exp v c)
;  (match r1exp
;    [(Int n)
;     ;; 在c的前面加上，这样就反过来了，最里面的会跑到最外面来
;     (values (Seq (Assign v (Int n)) c) '())]
;    [(Prim 'read '())
;     (values (Seq (Assign v (Prim 'read '())) c) '())]
;    [(Prim '- (list e))
;     (values (Seq (Assign v (Prim '- (list e))) c)
;             '())] 
;    [(Prim '+ (list e1 e2))
;     (values (Seq (Assign v (Prim '+ (list e1 e2))) c)
;             '())] 
;    [(Var x)
;     (values (Seq (Assign v (Var x)) c) '())]
;    [(Let x e body) 
;     (define-values (tail let-binds) (explicate-assign body v c))
;     (define-values (tail^ let-binds^) (explicate-assign e (Var x) tail))
;     ;; 想一想为什么不是(append let-binds^ let-binds)
;     ;(values tail^ (cons x (append let-binds^ let-binds)))]
;     (values tail^ (cons x (append let-binds let-binds^)))]
;    [else
;     (error "error explicate-assign ")]))
;     (printf "else v r1exp is ******* ~a ~a \n" v r1exp)
;     (values (Seq (Assign v r1exp) c) '())]))

;; explicate-control : R1 -> C0
;(define (explicate-control p)
;  (match p
;    [(Program info body)
;     (begin
;       (define-values (tail let-binds) (explicate-tail body))
;       ;;(printf "-=-=-=-=-=-=-= ~a ~a \n" tail vars)
;       ;; contains an alist that associates the symbol locals with a list of all the variables used in the program. 
;       (CProgram (cons (cons 'locals let-binds) info)
;                 (list (cons 'start tail))))]))
  ;(error "TODO: code goes here (explicate-control)"))



;; explicate-control 思路

(define basic-blocks '())

(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

;(define (create_block tail)
;  (delay
;    (define t (force tail))
;    (match t
;      [(Goto label) (Goto label)]
;      [else
;       (let ([label (gensym 'block)])
;         (set! basic-blocks (cons (cons label t) basic-blocks))
;         (Goto label))])))

;;------------------------------------
;(define (do-assignment exp var tail)
;  (match exp
;    [(Return (Int n)) (Seq (Assign var (Int n)) tail)]
;    [(Return (Var x)) (Seq (Assign var (Var x)) tail)]
;    [(Return (Bool bool)) (Seq (Assign var (Bool bool)) tail)]
;    [(Return (Prim op es)) (Seq (Assign var (Prim op es)) tail)]
;    [(Seq stmt seq-tail) (Seq stmt (do-assignment seq-tail var tail))]))
;
;(define (explicate-assign exp var tail cgraph)
;  (match exp
;    [(If pred then else)
;     (define tail-block (gensym "block"))
;     (define-values (then-block then-vars then-graph) (explicate-assign then var (Goto tail-block) cgraph))
;     (define-values (else-block else-vars else-graph) (explicate-assign else var (Goto tail-block) then-graph))
;     (define-values (pred-exp pred-vars pred-cgraph) (explicate-pred pred then-block else-block else-graph))
;     (values pred-exp (remove-duplicates (append then-vars else-vars pred-vars)) 
;               (cons `(,tail-block . ,tail) pred-cgraph))]
;    [(Let x exp body)
;      (begin (define-values (exp-body body-vars body-graph) (explicate-assign body var tail cgraph))
;             (define-values (body-tail vars newgraph) (explicate-assign exp (Var x) exp-body body-graph))
;             (values body-tail (cons (Var x) (remove-duplicates (append body-vars vars))) newgraph))]
;    [x (begin (define-values (exp-tail exp-vars exp-graph) (explicate-tail exp cgraph))
;              (values (do-assignment exp-tail var tail) exp-vars exp-graph))
;  ]))
;
;(define (explicate-pred e true-block false-block cgraph)
;  (match e
;    [(Bool b) (values (if b true-block false-block) '() cgraph))]
;
;    ;;[(Bool bool) 
;    ;; (values (IfStmt (Prim 'eq? (list (Bool bool) (Bool #t))) (Goto true-lbl) (Goto false-lbl)) '() cgraph)]
;     
;    [(Var x) 
;     (let ([true-lbl (gensym "block")]
;           [false-blb (gensym "block")])
;      (values (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (Goto true-lbl) (Goto false-lbl)) '() 
;          ... cgraph ...)]
;    [(Prim 'not (list var)) (values (IfStmt (Prim 'eq? (list var (Bool #f))) (Goto true-lbl) (Goto false-lbl)) '() cgraph)]
;    [(Prim cmp es) (values (IfStmt (Prim cmp es) (Goto true-lbl) (Goto false-lbl)) '() cgraph)]
;    [(Let x exp body)
;      (begin (define-values (exp-body body-vars body-graph) (explicate-pred body true-lbl false-lbl cgraph))
;             (define-values (tail vars tail-graph) (explicate-assign exp (Var x) exp-body body-graph)) 
;             (values tail (cons (Var x) (remove-duplicates (append body-vars vars))) tail-graph))]
;    [(If pred then else) 
;     (let ([true-lbl (gensym "block")]
;           [false-lbl (gensym "block")])
;        (begin (define-values (then-exp then-vars then-cgraph) (explicate-pred then (Goto true-lbl) (Goto false-lbl) cgraph))
;               (define-values (else-exp else-vars else-cgraph) (explicate-pred else (Goto true-lbl) (Goto false-lbl) then-cgraph))
;               (define-values (pred-exp pred-vars pred-cgraph) (explicate-pred pred then-exp else-exp else-cgraph))
;               (values pred-exp (remove-duplicates (append then-vars else-vars pred-vars))
;                  ... pred-cgraph))))]
;    ))
;                                  
;(define (explicate-tail e cgraph)
;  (match e
;      [(Var x) (values (Return (Var x)) '() cgraph)]
;      [(Int n) (values (Return (Int n)) '() cgraph)]
;      [(Bool bool) (values (Return (Bool bool)) '() cgraph)]
;      [(Let x e body)
;       (begin (define-values (exp-body body-vars body-graph) (explicate-tail body cgraph))
;         (define-values (tail vars newgraph) (explicate-assign e (Var x) exp-body body-graph))
;         (values tail (cons (Var x) (remove-duplicates (append body-vars vars))) newgraph))]
;      [(Prim op es)
;       (values (Return (Prim op es)) '() cgraph)]
;      [(If pred then else)
;        (let ([then-block (gensym "block")] [else-block (gensym "block")])
;          (begin (define-values (then-exp then-vars then-cgraph) (explicate-tail then cgraph))
;                 (define-values (else-exp else-vars else-cgraph) (explicate-tail else then-cgraph))
;                 (define-values (pred-exp pred-vars pred-cgraph) (explicate-pred pred then-block else-block else-cgraph))
;                 (values pred-exp (remove-duplicates (append then-vars else-vars pred-vars))
;                      (cons `(,then-block . ,then-exp) (cons `(,else-block . ,else-exp) pred-cgraph)))))]
;      ))
;
;(define (explicate-control p)
;  (match p
;    [(Program info e)
;     (begin (define-values (tail vars graph) (explicate-tail e '())) 
;            (CProgram `((locals . ,vars)) (cons `(start . ,tail) graph)))]
;    ))

;;----------------------
(define Explicate-CFG '())

(define (add-to-cfg t)
  (define new-label (gensym "l"))
  (set! Explicate-CFG (cons (cons new-label t) Explicate-CFG))
  new-label)

(define (explicate-tail exp)
  (match  exp
    [(Int n) (values (Return (Int n)) '())]
    [(Var v) (values (Return (Var v)) '())]
    [(Bool bool) (values (Return (Bool bool)) '())]
    [(Prim rator rand) (values (Return (Prim rator rand)) '())]
    [(Let var exp body)
     (let*-values ([(let-body variables1) (explicate-tail body)]
                   [(assigned-tail variables2) (explicate-assign exp var let-body)])
       (values assigned-tail (cons var (append variables1 variables2))))]
    [(If cnd thn els)
     (let*-values ([(thn-tail vars1) (explicate-tail thn)]
                   [(els-tail vars2) (explicate-tail els)])
     (let-values ([(cnd-tail vars3) (explicate-pred cnd thn-tail els-tail)])
       ;; (values cnd-tail (append vars3 vars1 vars2))))]))
       (values cnd-tail (append vars1 vars2 vars3))))]))

(define (explicate-assign exp var tail)
  (match exp
    [(Int n) (values (Seq (Assign (Var var) (Int n)) tail) '())]
    [(Var v) (values (Seq (Assign (Var var) (Var v)) tail) '())]
    [(Bool bool) (values (Seq (Assign (Var var) (Bool bool)) tail) '())]
    [(Prim rator rand) (values (Seq (Assign (Var var) (Prim rator rand)) tail) '())]
    [(Let var* exp body)
     (let*-values ([(body-tail vars1) (explicate-assign body var tail)]
                   [(exp-tail vars2) (explicate-assign exp var* body-tail)])
       (values exp-tail (cons var* (append vars1 vars2))))]
    [(If cnd thn els)
     (define label (add-to-cfg tail))
     (let*-values ([(thn-tail vars1) (explicate-assign thn var (Goto label))]
                   [(els-tail vars2) (explicate-assign els var (Goto label))]
                   [(cnd-tail vars3) (explicate-pred cnd thn-tail els-tail)])
       ;; 注意变量顺序
       (values cnd-tail (append vars3 vars1 vars2)))]))

(define (explicate-pred e tail1 tail2)
  (match e
    [(Bool bool) (if bool (values tail1 '()) (values tail2 '()))]
    [(Var v)
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (values (IfStmt (Prim 'eq? (list (Var v) (Bool #t))) 
                     (Goto label1) (Goto label2)) 
             '())]
    [(Prim rator (list exp1 exp2))
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (define atm1 (gensym "rator-1-"))
     (define atm2 (gensym "rator-2-"))
     (let*-values ([(atm2-tail vars2) (explicate-assign exp2 atm2 (IfStmt (Prim rator (list (Var atm1) (Var atm2))) (Goto label1) (Goto label2)))]
                    [(atm1-tail vars1) (explicate-assign exp1 atm1 atm2-tail)])
        (values atm1-tail (cons atm1 (cons atm2 (append vars1 vars2)))))]
    [(Prim 'not (list exp))
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (values (IfStmt (Prim 'eq? (list exp (Bool #t))) (Goto label2) (Goto label1)) '())]
    [(Let var exp body)
      (define label1 (add-to-cfg tail1))
      (define label2 (add-to-cfg tail2))
      (define t (gensym "let-ec-"))
      (let*-values ([(body-tail vars1) (explicate-assign body t (IfStmt (Prim 'eq? (list (Var t) (Bool #t))) (Goto label1) (Goto label2)))]
                    [(exp-tail vars2) (explicate-assign exp var body-tail)])
        (values exp-tail (cons t (cons var (append vars1 vars2)))))]
    [(If cnd thn els)
     (define label1 (add-to-cfg tail1))
     (define label2 (add-to-cfg tail2))
     (let*-values ([(thn-block vars2) (explicate-pred thn (Goto label1) (Goto label2))]
                   [(els-block vars3) (explicate-pred els (Goto label1) (Goto label2))]
                   [(thn-label) (add-to-cfg thn-block)]
                   [(els-label) (add-to-cfg els-block)]
                   [(result vars) (explicate-pred cnd (Goto thn-label) (Goto els-label))]
                   )
       (values result (append vars vars2 vars3)))]
    ))


;(define (explicate-pred e tail1 tail2)
;  (match e
;    [(Bool b)
;     (if b
;         (values tail1 '())
;         (values tail2 '()))]
;    [(Var v)
;     (values (IfStmt (Prim 'eq? (list (Var v) (Bool #t)))
;                     (create-block tail1)
;                     (create-block tail2))
;             '())]
;    [(Prim op (list e1 e2))
;     (values (IfStmt (Prim op (list e1 e2))
;                     (create-block tail1)
;                     (create-block tail2))
;             '())]
;    [(Let x v body)
;     ...
     
     
    

(define (explicate-control p)
  (set! Explicate-CFG '())
  (match p
    [(Program info e)
     (let-values ([(tail vars) (explicate-tail e)])
       (CProgram
        (list (cons 'locals vars))
        (cons (cons 'start tail) Explicate-CFG)))]
    ))


;(CProgram
; '((locals tmp397488 tmp397489 tmp397490 tmp397491 tmp397492))
; (list
;  (cons
;   'start
;   (Seq
;    (Assign (Var 'tmp397488) (Prim 'read '()))
;    (Seq
;     (Assign (Var 'tmp397489) (Prim 'eq? (list (Var 'tmp397488) (Int 0))))
;     (Seq
;      (Assign (Var 'tmp397490) (Prim 'read '()))
;      (Seq
;       (Assign (Var 'tmp397491) (Prim 'eq? (list (Var 'tmp397490) (Int 1))))
;       (IfStmt
;        (Prim 'eq? (list (Var 'tmp397489) (Bool #t)))
;        (Goto 'l397823)
;        (Goto 'l397824)))))))
;  (cons 'l397824 (Seq (Assign (Var 'tmp397492) (Bool #f)) (Goto 'l397822)))
;  (cons
;   'l397823
;   (Seq (Assign (Var 'tmp397492) (Var 'tmp397491)) (Goto 'l397822)))
;  (cons
;   'l397822
;   (IfStmt
;    (Prim 'eq? (list (Var 'tmp397492) (Bool #t)))
;    (Goto 'l397820)
;    (Goto 'l397821)))
;  (cons 'l397821 (Return (Int 42)))
;  (cons 'l397820 (Return (Int 0)))))
;
;
;program:
;locals:
;'(tmp402042 tmp402043 tmp402044 tmp402045 tmp402046)
;start:
;    tmp402042 = (read);
;    tmp402043 = (eq? tmp402042 0);
;    tmp402044 = (read);
;    tmp402045 = (eq? tmp402044 1);
;    if (eq? tmp402043 #t)
;       goto l402132;
;    else
;       goto l402133;
;l402133:
;    tmp402046 = #f;
;    goto l402131;
;l402132:
;    tmp402046 = tmp402045;
;    goto l402131;
;l402131:
;    if (eq? tmp402046 #t)
;       goto l402129;
;    else
;       goto l402130;
;l402130:
;    return 42;
;l402129:
;    return 0;


;In this way, jump instructions are edges in the graph and the basic blocks are the nodes.
;Likewise, our language CIf provides the ability to label a sequence of statements and to jump to a label via goto.

;These ordering constraints are the
;reverse of a topological order on a graph representation of the program. In particular,
;the control flow graph (CFG) (Allen 1970) of a program has a node for each basic
;block and an edge for each jump from one block to another. It is straightforward to
;generate a CFG from the dictionary of basic blocks.



(define (is-trivial? block)
  (match block
    [(Goto label) #t]
    [else #f]))

(define (get-label block)
  (match block
    [(Goto label) label]))

(define (add-to-hash hash src-label goto-label)
  (hash-set! hash src-label goto-label)
  (hash-map hash 
    (lambda (k v) (if (equal? v src-label)
      (hash-set! hash k goto-label)
      (void))))
  hash)

(define (short-cut blocks)
  (define ret (make-hash))
  (for ([(label block) (in-dict blocks)])
          (if (is-trivial? block)
            (add-to-hash ret label (get-label block))
            (hash-set! ret label label)))
  ret)

(define (patch-tail hash tl)
  (match tl
    [(IfStmt cnd thn els) (IfStmt cnd (patch-tail hash thn) (patch-tail hash els))]
    [(Return exp) tl]
    [(Seq stmt tail) (Seq stmt (patch-tail hash tail))]
    [(Goto label) (Goto (hash-ref hash label))]
    ))
;; 消除只有一个goto的label
;; remove the label who has only the goto
(define (patch-gotos short-cuts blocks)   
  (for/list ([(label block) (in-dict blocks)])
        (cons label (patch-tail short-cuts block))))

(define (optimize-jumps p)
  (match p
    [(CProgram info blocks)
      (define short-cuts (short-cut blocks))
      (printf "short cuts is ~a \n" short-cuts)
      (define not-short-cut (filter (lambda (b) (or (not (is-trivial? (cdr b)))
                                                    (equal? (car b) 'start))) blocks))
      (printf "not short cut is ~a \n" not-short-cut)
      (define patched (patch-gotos short-cuts not-short-cut))
      (printf "patched is ~a \n" patched)
      (define ref-graph (block-list->racketgraph patched))
      (printf "edges is ~a \n" (get-edges ref-graph))
      ;; what is the effect of this step?
      (define has-neighbors (filter (lambda (b) (or (has-vertex? ref-graph (car b))
                                                    (equal? (car b) 'start))) patched))
      (printf "has-neighbors is ~a \n" has-neighbors)
      (CProgram info (patch-gotos short-cuts has-neighbors))]))

;; 最后一步的goto的label，指向当前的label
;; 根据图4.8，tail总共有四种形式
;; (Return exp)
;; (Seq stmt tail)
;; (Goto label)
;; (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))
(define (build-graph-optimize label tail racket-cfg)
  (match tail
    [(Goto target)
     (printf "source is ~a, target is ~a \n " target label)
     (add-directed-edge! racket-cfg target label)]
    [(IfStmt cnd thn els) (begin
                            (build-graph-optimize label thn racket-cfg)
                            (build-graph-optimize label els racket-cfg))]
    [(Seq stmt tl) (build-graph-optimize label tl racket-cfg)]
    [_ (void)]))

(define (block-list->racketgraph blocks)
  (define racket-cfg (directed-graph '()))
     (for ([(label block) (in-dict blocks)])
       (build-graph-optimize label block racket-cfg))
     racket-cfg)

;(optimize-jumps
;(CProgram
; '((locals
;    x599559
;    y599560
;    tmp599599
;    tmp599600
;    tmp599601
;    tmp599602
;    tmp599603
;    tmp599604))
; (list
;  (cons
;   'start
;   (Seq
;    (Assign (Var 'x599559) (Prim 'read '()))
;    (Seq
;     (Assign (Var 'y599560) (Prim 'read '()))
;     (Seq
;      (Assign (Var 'tmp599599) (Prim '< (list (Var 'x599559) (Int 10))))
;      (Seq
;       (Assign (Var 'tmp599600) (Prim 'eq? (list (Var 'x599559) (Int 0))))
;       (Seq
;        (Assign (Var 'tmp599601) (Prim 'eq? (list (Var 'x599559) (Int 20))))
;        (IfStmt
;         (Prim 'eq? (list (Var 'tmp599599) (Bool #t)))
;         (Goto 'l599654)
;         (Goto 'l599655))))))))
;  (cons
;   'l599655
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599601)) (Goto 'l599653)))
;  (cons
;   'l599654
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599600)) (Goto 'l599653)))
;  (cons
;   'l599653
;   (Seq
;    (Assign (Var 'tmp599603) (Prim '+ (list (Var 'y599560) (Int 2))))
;    (Seq
;     (Assign (Var 'tmp599604) (Prim '+ (list (Var 'y599560) (Int 10))))
;     (IfStmt
;      (Prim 'eq? (list (Var 'tmp599602) (Bool #t)))
;      (Goto 'l599651)
;      (Goto 'l599652)))))
;  (cons 'l599652 (Return (Var 'tmp599604)))
;  (cons 'l599651 (Return (Var 'tmp599603))))))
;
;(optimize-jumps
; (CProgram
; '((locals
;    x599559
;    y599560
;    tmp599599
;    tmp599600
;    tmp599601
;    tmp599602
;    tmp599603
;    tmp599604))
; (list
;  (cons
;   'start
;   (Seq
;    (Assign (Var 'x599559) (Prim 'read '()))
;    (Seq
;     (Assign (Var 'y599560) (Prim 'read '()))
;     (Seq
;      (Assign (Var 'tmp599599) (Prim '< (list (Var 'x599559) (Int 10))))
;      (Seq
;       (Assign (Var 'tmp599600) (Prim 'eq? (list (Var 'x599559) (Int 0))))
;       (Seq
;        (Assign (Var 'tmp599601) (Prim 'eq? (list (Var 'x599559) (Int 20))))
;        (IfStmt
;         (Prim 'eq? (list (Var 'tmp599599) (Bool #t)))
;         (Goto 'l599654)
;         (Goto 'l599655))))))))
;  (cons
;   'l599655
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599601)) (Goto 'l511111)))
;  (cons
;   'l599654
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599600)) (Goto 'l511111)))
;  (cons
;   'l599653
;   (Seq
;    (Assign (Var 'tmp599603) (Prim '+ (list (Var 'y599560) (Int 2))))
;    (Seq
;     (Assign (Var 'tmp599604) (Prim '+ (list (Var 'y599560) (Int 10))))
;     (IfStmt
;      (Prim 'eq? (list (Var 'tmp599602) (Bool #t)))
;      (Goto 'l599651)
;      (Goto 'l599652)))))
;  (cons
;   'l511111 
;   (Goto 'l599653))    
;  (cons 'l599652 (Return (Var 'tmp599604)))
;  (cons 'l599651 (Return (Var 'tmp599603))))))
;
;(optimize-jumps
; (CProgram
; '((locals
;    x599559
;    y599560
;    tmp599599
;    tmp599600
;    tmp599601
;    tmp599602
;    tmp599603
;    tmp599604))
; (list
;  (cons
;   'start
;   (Seq
;    (Assign (Var 'x599559) (Prim 'read '()))
;    (Seq
;     (Assign (Var 'y599560) (Prim 'read '()))
;     (Seq
;      (Assign (Var 'tmp599599) (Prim '< (list (Var 'x599559) (Int 10))))
;      (Seq
;       (Assign (Var 'tmp599600) (Prim 'eq? (list (Var 'x599559) (Int 0))))
;       (Seq
;        (Assign (Var 'tmp599601) (Prim 'eq? (list (Var 'x599559) (Int 20))))
;        (IfStmt
;         (Prim 'eq? (list (Var 'tmp599599) (Bool #t)))
;         (Goto 'l599654)
;         (Goto 'l599655))))))))
;  (cons
;   'l599655
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599601)) (Goto 'l511111)))
;  (cons
;   'l599654
;   (Seq (Assign (Var 'tmp599602) (Var 'tmp599600)) (Goto 'l511111)))
;  (cons
;   'l599653
;   (Seq
;    (Assign (Var 'tmp599603) (Prim '+ (list (Var 'y599560) (Int 2))))
;    (Seq
;     (Assign (Var 'tmp599604) (Prim '+ (list (Var 'y599560) (Int 10))))
;     (IfStmt
;      (Prim 'eq? (list (Var 'tmp599602) (Bool #t)))
;      (Goto 'l599651)
;      (Goto 'l599652)))))
;  (cons
;   'l511111 
;   (Goto 'l522222))  
;  (cons
;   'l522222 
;   (Goto 'l599653))    
;  (cons 'l599652 (Return (Var 'tmp599604)))
;  (cons 'l599651 (Return (Var 'tmp599603))))))

;short cuts is #hash((l511111 . l599653)
;                    (l599651 . l599651)
;                    (l599652 . l599652)
;                    (l599653 . l599653)
;                    (l599654 . l599654)
;                    (l599655 . l599655)
;                    (start . start)) 
;not short cut is
;(
;(start . #<Seq: #<Assign: #<Var: x599559> #<Prim: read ()>> #<Seq: #<Assign: #<Var: y599560> #<Prim: read ()>> #<Seq: #<Assign: #<Var: tmp599599> #<Prim: < (#<Var: x599559> #<Int: 10>)>> #<Seq: #<Assign: #<Var: tmp599600> #<Prim: eq? (#<Var: x599559> #<Int: 0>)>> #<Seq: #<Assign: #<Var: tmp599601> #<Prim: eq? (#<Var: x599559> #<Int: 20>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599599> #<Bool: #t>)> #<Goto: l599654> #<Goto: l599655>>>>>>>) 
;(l599655 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599601>> #<Goto: l511111>>) 
;(l599654 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599600>> #<Goto: l511111>>) 
;(l599653 . #<Seq: #<Assign: #<Var: tmp599603> #<Prim: + (#<Var: y599560> #<Int: 2>)>> #<Seq: #<Assign: #<Var: tmp599604> #<Prim: + (#<Var: y599560> #<Int: 10>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599602> #<Bool: #t>)> #<Goto: l599651> #<Goto: l599652>>>>) 
;(l599652 . #<Return: #<Var: tmp599604>>) 
;(l599651 . #<Return: #<Var: tmp599603>>))
;patchs is 
;((start . #<Seq: #<Assign: #<Var: x599559> #<Prim: read ()>> #<Seq: #<Assign: #<Var: y599560> #<Prim: read ()>> #<Seq: #<Assign: #<Var: tmp599599> #<Prim: < (#<Var: x599559> #<Int: 10>)>> #<Seq: #<Assign: #<Var: tmp599600> #<Prim: eq? (#<Var: x599559> #<Int: 0>)>> #<Seq: #<Assign: #<Var: tmp599601> #<Prim: eq? (#<Var: x599559> #<Int: 20>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599599> #<Bool: #t>)> #<Goto: l599654> #<Goto: l599655>>>>>>>) 
;(l599655 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599601>> #<Goto: l599653>>) 
;(l599654 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599600>> #<Goto: l599653>>) 
;(l599653 . #<Seq: #<Assign: #<Var: tmp599603> #<Prim: + (#<Var: y599560> #<Int: 2>)>> #<Seq: #<Assign: #<Var: tmp599604> #<Prim: + (#<Var: y599560> #<Int: 10>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599602> #<Bool: #t>)> #<Goto: l599651> #<Goto: l599652>>>>) 
;(l599652 . #<Return: #<Var: tmp599604>>) 
;(l599651 . #<Return: #<Var: tmp599603>>))
;l599655和l599654中的goto替换为了l599653
; edges is ((l599654 start)
;           (l599651 l599653)
;           (l599652 l599653)
;           (l599655 start)
;           (l599653 l599655)
;           (l599653 l599654))
;has-neighbors is 
;((start . #<Seq: #<Assign: #<Var: x599559> #<Prim: read ()>> #<Seq: #<Assign: #<Var: y599560> #<Prim: read ()>> #<Seq: #<Assign: #<Var: tmp599599> #<Prim: < (#<Var: x599559> #<Int: 10>)>> #<Seq: #<Assign: #<Var: tmp599600> #<Prim: eq? (#<Var: x599559> #<Int: 0>)>> #<Seq: #<Assign: #<Var: tmp599601> #<Prim: eq? (#<Var: x599559> #<Int: 20>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599599> #<Bool: #t>)> #<Goto: l599654> #<Goto: l599655>>>>>>>) 
;(l599655 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599601>> #<Goto: l599653>>) 
;(l599654 . #<Seq: #<Assign: #<Var: tmp599602> #<Var: tmp599600>> #<Goto: l599653>>) 
;(l599653 . #<Seq: #<Assign: #<Var: tmp599603> #<Prim: + (#<Var: y599560> #<Int: 2>)>> #<Seq: #<Assign: #<Var: tmp599604> #<Prim: + (#<Var: y599560> #<Int: 10>)>> #<IfStmt: #<Prim: eq? (#<Var: tmp599602> #<Bool: #t>)> #<Goto: l599651> #<Goto: l599652>>>>) 
;(l599652 . #<Return: #<Var: tmp599604>>) 
;(l599651 . #<Return: #<Var: tmp599603>>))




;(define (select-instr-atm a)
;  (match a
;    [(Int i) (Imm i)]
;    [(Var _) a]))
;
;(define (select-instr-assign v e)
;  (match e
;    [(Int i) 
;     (list (Instr 'movq (list (select-instr-atm e) v)))]
;    [(Var _)
;     (list (Instr 'movq (list (select-instr-atm e) v)))]
;    [(Prim 'read '())
;     (list (Callq 'read_int)
;           (Instr 'movq (list (Reg 'rax) v)))]
;    [(Prim '- (list a))
;     (list (Instr 'movq (list (select-instr-atm a) v))
;           (Instr 'negq (list v)))]
;    [(Prim '+ (list a1 a2))
;     (list (Instr 'movq (list (select-instr-atm a1) v))
;           (Instr 'addq (list (select-instr-atm a2) v)))]))
;
;(define (select-instr-stmt stmt)
;  (match stmt
;    ;; one of the args is the same as the left hand side Var
;    [(Assign (Var v) (Prim '+ (list (Var v1) a2))) #:when (equal? v v1)
;     (list (Instr 'addq (list (select-instr-atm a2) (Var v))))]
;    [(Assign (Var v) (Prim '+ (list a1 (Var v2)))) #:when (equal? v v2)
;     (list (Instr 'addq (list (select-instr-atm a1) (Var v))))]
;    [(Assign v e)
;     (select-instr-assign v e)]))
;
;(define (select-instr-tail t)
;  (match t
;    [(Seq stmt t*) 
;     (append (select-instr-stmt stmt) (select-instr-tail t*))]
;    [(Return (Prim 'read '())) 
;     (list (Callq 'read_int) (Jmp 'conclusion))]
;    [(Return e) (append
;                 (select-instr-assign (Reg 'rax) e)
;                 (list (Jmp 'conclusion)))]))
;
;(define (select-instructions p)
;  (match p
;    [(CProgram info (list (cons 'start t)))
;     (X86Program info
;       (list (cons 'start (Block '() (select-instr-tail t)))))]))


(define (sel-ins-atm c0a)
  (match c0a
    [(Int n) (Imm n)]
    [(Var x) (Var x)]
    [(Bool b) 
     (match b
      [#t (Imm 1)]
      [#f (Imm 0)])]))

(define (sel-ins-stmt c0stmt)
  (match c0stmt
    [(Assign v e)
     (if (atm? e)
         (list (Instr 'movq (list (sel-ins-atm e) v)))
         (match e
           [(Prim 'read '())
            (list (Callq 'read_int 0)
                  (Instr 'movq (list (Reg 'rax) v)))]
           [(Prim '- (list atm))
            (define x86atm (sel-ins-atm atm))
            (if (equal? x86atm v)
                (list (Instr 'negq (list v)))
                (list (Instr 'movq (list x86atm v))
                      (Instr 'negq (list v))))]
           [(Prim '+ (list atm1 atm2))
            (define x86atm1 (sel-ins-atm atm1))
            (define x86atm2 (sel-ins-atm atm2))
            (cond [(equal? x86atm1 v) (list (Instr 'addq (list x86atm2 v)))]
                  [(equal? x86atm2 v) (list (Instr 'addq (list x86atm1 v)))]
                  [else (list (Instr 'movq (list x86atm1 v))
                              (Instr 'addq (list x86atm2 v)))])]
           [(Prim 'not (list atm))
            (if (eqv? v atm)
                (list (Instr 'xorq (list (Imm 1) v)))
                (list (let ([atm_ (sel-ins-atm atm)])
                        (Instr 'movq (list atm_ v)))
                      (Instr 'xorq (list (Imm 1) v))))]
           [(Prim 'eq? (list atm1 atm2))
            (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'e (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]
           [(Prim '< (list atm1 atm2))
           (let ([atm1_ (sel-ins-atm atm1)]
                  [atm2_ (sel-ins-atm atm2)]
                  [v_ (sel-ins-atm v)])
              (list
               (Instr 'cmpq (list atm2_ atm1_))
               (Instr 'set (list 'l (Reg 'al)))
               (Instr 'movzbq (list (Reg 'al) v_))))]))]))

(define (sel-ins-tail c0t)
  (match c0t
    [(Return e)
     (append (sel-ins-stmt (Assign (Reg 'rax) e))
             (list (Jmp 'conclusion)))]
    [(Seq stmt tail)
     (define x86stmt (sel-ins-stmt stmt))
     (define x86tail (sel-ins-tail tail))
     (append x86stmt x86tail)]
    [(Goto label)
     (list (Jmp label))]
    [(IfStmt (Prim 'eq? (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'e label1)
        (Jmp label2)))]
    [(IfStmt (Prim '< (list arg1 arg2)) (Goto label1) (Goto label2))
     (let ([arg1_ (sel-ins-atm arg1)]
           [arg2_ (sel-ins-atm arg2)])
       (list
        (Instr 'cmpq (list arg2_ arg1_))
        (JmpIf 'l label1)
        (Jmp label2)))]))

(define (select-instructions p)
  (match p
    [(CProgram info es)
     (X86Program info (for/list ([ls es])
                        (cons (car ls) (Block '() (sel-ins-tail (cdr ls))))))]))


;(X86Program
; '((locals
;    x1751720
;    y1751721
;    tmp1751760
;    tmp1751761
;    tmp1751762
;    tmp1751763
;    tmp1751764
;    tmp1751765)
;   (locals-types
;    (tmp1751760 . Boolean)
;    (x1751720 . Integer)
;    (tmp1751765 . Integer)
;    (tmp1751763 . Boolean)
;    (tmp1751764 . Integer)
;    (tmp1751761 . Boolean)
;    (y1751721 . Integer)
;    (tmp1751762 . Boolean)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Callq 'read_int 0)
;     (Instr 'movq (list (Reg 'rax) (Var 'x1751720)))
;     (Callq 'read_int 0)
;     (Instr 'movq (list (Reg 'rax) (Var 'y1751721)))
;     (Instr 'cmpq (list (Imm 10) (Var 'x1751720)))
;     (Instr 'set (list 'l (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751760)))
;     (Instr 'cmpq (list (Imm 0) (Var 'x1751720)))
;     (Instr 'set (list 'e (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751761)))
;     (Instr 'cmpq (list (Imm 20) (Var 'x1751720)))
;     (Instr 'set (list 'e (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751762)))
;     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751760)))
;     (JmpIf 'e 'l1751807)
;     (Jmp 'l1751808))))
;  (cons
;   'l1751808
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'tmp1751762) (Var 'tmp1751763)))
;     (Jmp 'l1751806))))
;  (cons
;   'l1751807
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'tmp1751761) (Var 'tmp1751763)))
;     (Jmp 'l1751806))))
;  (cons
;   'l1751806
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751764)))
;     (Instr 'addq (list (Imm 2) (Var 'tmp1751764)))
;     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751765)))
;     (Instr 'addq (list (Imm 10) (Var 'tmp1751765)))
;     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751763)))
;     (JmpIf 'e 'l1751804)
;     (Jmp 'l1751805))))
;  (cons
;   'l1751805
;   (Block
;    '()
;    (list (Instr 'movq (list (Var 'tmp1751765) (Reg 'rax))) (Jmp 'conclusion))))
;  (cons
;   'l1751804
;   (Block
;    '()
;    (list (Instr 'movq (list (Var 'tmp1751764) (Reg 'rax))) (Jmp 'conclusion))))))




;;==============================================================
;; live --- interference --- color
;; 47 minutes
;; uncover-live: live-after -> pseudo-x86 -> pseudo-x86*
;; *annotated program with live-after information for each stmt

(define (free-vars arg)
  (match arg
    [(Var x) (set x)]
    [(Reg r) (set r)]
    ;; 栈 r为rbp i为offset
    [(Deref r i) (set r)]
    [(Imm n) (set)]
    [else (error "free-vars, unhandled" arg)]))

(define (read-vars instr)
  ;(printf "instr is ~a \n" instr)
  (match instr
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity)
    ;; (apply set-union (for/list ([a arity]) (free-vars a)))]
    [(Jmp label) (set)]
    [(JmpIf cc label)
     (set)]
    [(Instr 'movq (list s d)) (free-vars s)]
    [(Instr 'movzbq (list s d))
     (free-vars s)]
    [(Instr name arg*)
     (if (eq? name 'set)
         (set)
         (apply set-union (for/list ([arg arg*]) (free-vars arg))))]
    [else (error "read-vars unmatched" instr)]))

(define (write-vars instr)
  (match instr
    [(Jmp label) (set)]
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity)
    [(JmpIf cc label)
     (set)]
    [(Instr 'movq (list s d)) (free-vars d)]
    [(Instr 'movzbq (list s d))
     (free-vars d)]
    ;;[(Instr name arg*) (free-vars (last arg*))]
    [(Instr name arg*)
     (if (eq? name 'set)
         (set)
         (free-vars (last arg*)))]
    [else (error "write-vars unmatched" instr)]))

(define (uncover-live-instr live-after)
  (lambda (stmt)
    (set-union (set-subtract live-after (write-vars stmt))
               (read-vars stmt))))
                                   
(define (uncover-live-stmts orig-live-after)
  (lambda (orig-ss)
    (let loop ([ss (reverse orig-ss)]
               [live-after orig-live-after]
               [lives (list orig-live-after)])
      (cond [(null? ss) lives]
            [else
             (define new-live-after
               ((uncover-live-instr live-after) (car ss)))
             (loop (cdr ss) new-live-after
                   (cons new-live-after lives))]))))

(define (uncover-live-block ast live-after)
  (match ast
    ;; ss is list statements
    [(Block info ss)
     (define lives ((uncover-live-stmts live-after) ss))
     (define new-info (dict-set info 'lives lives))
     (Block new-info ss)]
    [else
     (error "R1-reg/uncover-live-block unhandled" ast)]))
;
;;; what is args of the uncover-list
;;; what is the ast
;;; it is the result of the instruction selection
;(define (uncover-live ast)
;  (match ast
;    [(X86Program info (list (cons 'start block)))
;     (define new-block (uncover-live-block block (set)))
;     (X86Program info (list (cons 'start new-block)))]))

;;-----------------------

;(define (uncover-live p)
;  (match p
;    [(X86Program info es)
;     ;; 构造图？
;     (define cfg-with-edges (isomorph es))
;     ;; 翻转边
;     (define cfg-we-tp (transpose cfg-with-edges))
;     ;; 返回顶点 '(l599652 l599651 l599653 l599655 l599654 start)
;     (define reverse-top-order (tsort cfg-we-tp))
;     (X86Program
;      info
;      (foldl
;       (lambda (label cfg)
;         (begin
;           ;; 找出block
;           (define block (cdr (assv label es)))
;           ;; block中的指令和对应的info
;           (define-values (instr+ bl-info)
;             (match block
;               [(Block bl-info instr+)
;                (values instr+ bl-info)]))
;           ;; 比如start的为l599654 和 l599655
;           (define neighbors (get-neighbors cfg-with-edges label))
;           ;; 合并跳转block的liveness
;           (define live-after
;             (foldr
;              (lambda (nbr lv-after)
;                (set-union
;                 lv-after
;                 ; the lv-before of its neighbor
;                 ; TODO this assv is failing? or see above
;                 (begin
;                   (match (cdr (assv nbr es));;(assv nbr cfg))
;                     [(Block bl-info instr+)
;                      (car bl-info)]))))
;              '()
;              (filter (lambda (vtx) (not (eqv? vtx 'conclusion)))
;                      neighbors)))
;           (define liveness-blk (liveness instr+ live-after))
;           (define blonk (Block liveness-blk instr+))
;           (cons `(,label . ,blonk) cfg)))
;       '() ;; init 
;       ; remove conclusion from liveness analysis since we have not
;       ; created it yet
;       (filter (lambda (vtx) (not (eqv? vtx 'conclusion)))
;               reverse-top-order)))]))

;;--------------------------------

(define (adjacent-instr s)
  (match s
    [(Jmp label)
     (cond [(string-suffix? (symbol->string label) "conclusion") (set)]
           [else (set label)])]
    [(JmpIf cc label) (set label)]
    [else (set)]))

;; 'start 的adjacent-instrs为 l599654 和 l599655
(define (adjacent-instrs b)
  (match b
    [(Block info ss) ;; ss为指令list
     (for/fold ([outs (set)]) ([s ss]) ;; (set) 为outs的初始值
       (set-union outs (adjacent-instr s)))]
    ))

(define (CFG->graph cfg)
  (define G (directed-graph '()))
  (for ([label (in-dict-keys cfg)])
    ;; label是顶点
    (add-vertex! G label))
  (for ([(s b) (in-dict cfg)])
    (for ([t (adjacent-instrs b)])
      ;; 'start -> t ; t是个set
      (add-directed-edge! G s t)))
  (printf "G edges is ~a \n" (get-edges G))
  G)

(define (live-before label CFG-hash)
  (match (hash-ref CFG-hash label)
    [(Block info ss)
     (car (dict-ref info 'lives))]))

(define (uncover-live-CFG cfg)
  (define G (CFG->graph cfg))
  (define CFG-hash (make-hash))
  (for ([label (tsort (transpose G))])
    (define live-after
      (for/fold ([lives (set)])
                ([lbl (in-neighbors G label)])
        (set-union lives (live-before lbl CFG-hash))))
    (define new-block
      (uncover-live-block (dict-ref cfg label) live-after))
    (hash-set! CFG-hash label new-block)
    )
  (hash->list CFG-hash))

(define (uncover-live ast)
  (verbose "uncover-live " ast)
  (match ast
    [(X86Program info G)
     (X86Program info (uncover-live-CFG G))]
    ))


;(uncover-live
; (X86Program
; '((locals
;    x1751720
;    y1751721
;    tmp1751760
;    tmp1751761
;    tmp1751762
;    tmp1751763
;    tmp1751764
;    tmp1751765)
;   (locals-types
;    (tmp1751760 . Boolean)
;    (x1751720 . Integer)
;    (tmp1751765 . Integer)
;    (tmp1751763 . Boolean)
;    (tmp1751764 . Integer)
;    (tmp1751761 . Boolean)
;    (y1751721 . Integer)
;    (tmp1751762 . Boolean)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Callq 'read_int 0)
;     (Instr 'movq (list (Reg 'rax) (Var 'x1751720)))
;     (Callq 'read_int 0)
;     (Instr 'movq (list (Reg 'rax) (Var 'y1751721)))
;     (Instr 'cmpq (list (Imm 10) (Var 'x1751720)))
;     (Instr 'set (list 'l (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751760)))
;     (Instr 'cmpq (list (Imm 0) (Var 'x1751720)))
;     (Instr 'set (list 'e (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751761)))
;     (Instr 'cmpq (list (Imm 20) (Var 'x1751720)))
;     (Instr 'set (list 'e (Reg 'al)))
;     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751762)))
;     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751760)))
;     (JmpIf 'e 'l1751807)
;     (Jmp 'l1751808))))
;  (cons
;   'l1751808
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'tmp1751762) (Var 'tmp1751763)))
;     (Jmp 'l1751806))))
;  (cons
;   'l1751807
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'tmp1751761) (Var 'tmp1751763)))
;     (Jmp 'l1751806))))
;  (cons
;   'l1751806
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751764)))
;     (Instr 'addq (list (Imm 2) (Var 'tmp1751764)))
;     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751765)))
;     (Instr 'addq (list (Imm 10) (Var 'tmp1751765)))
;     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751763)))
;     (JmpIf 'e 'l1751804)
;     (Jmp 'l1751805))))
;  (cons
;   'l1751805
;   (Block
;    '()
;    (list (Instr 'movq (list (Var 'tmp1751765) (Reg 'rax))) (Jmp 'conclusion))))
;  (cons
;   'l1751804
;   (Block
;    '()
;    (list (Instr 'movq (list (Var 'tmp1751764) (Reg 'rax))) (Jmp 'conclusion)))))))



;;==========
;; 55 minutes
;; build-interference: live-after x graph -> pseudo-x86* -> pseudo-x86*
;; *annotate program with interference graph

(define (build-interference-instr live-after G)
  (lambda (ast)
    (verbose "build-interference-instr " ast live-after)
    (match ast
      [(or (Instr 'movq (list s d)) (Instr 'movzbq (list s d)))
       (for ([v live-after])
         (for ([d (free-vars d)])
           (cond [(equal? (Var v) s)
                  (verbose "same source" s)]
                 [(equal? v d)
                  (verbose "skip self edge on " d)]
                 [else
                  (verbose "adding edge " d v)
                  (add-edge! G d v)])))
       ast]
      [(Callq f arity)
       (for ([v live-after])
         (for ([u (caller-save-for-alloc)])
           (cond [(equal? v u)
                  (verbose "skip self edge on " v)]
                 [else
                  ;; 这个地方为什么要加边？ caller不是可以随便分配吗？
                  (verbose "adding edge " u v)
                  (add-edge! G u v)])))
       ast]
      [else
       (for ([v live-after])
         (for ([d (write-vars ast)])
           (cond [(equal? v d)
                  (verbose "skip self edge on " d)]
                 [else
                  (verbose "adding edge " d v)
                  (add-edge! G d v)])))
       ast])))
                 
  
(define (build-interference-block ast G)
  (match ast
    [(Block info ss)
     (define lives (dict-ref info 'lives))
     ;; put off the live-before of the first instruction
     (define live-afters (cdr lives))
     (define new-ss (for/list ([inst ss] [live-after live-afters])
                      ((build-interference-instr live-after G) inst)))
     (define new-info (dict-remove info 'lives))
     (Block new-info new-ss)]
    [else (error "R1-reg/build-interference-block unhandled" ast)]))

(define (build-interference ast)
  (verbose "build-interference " ast)
  (match ast
    [(X86Program info Blocks)
     (define locals (dict-ref info 'locals))
     (define G (undirected-graph '()))
     (for ([v locals])
       (add-vertex! G v))
     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label (build-interference-block block G))))
     (print-dot G "./interfere.dot")
     (printf "get conflicts edges is ~a \n" (get-edges G))
     (define new-info (dict-set info 'conflicts G))
     (X86Program new-info new-Blocks)]))


(build-interference
 (X86Program
 '((locals x1751720 y1751721 tmp1751760 tmp1751761 tmp1751762 tmp1751763 tmp1751764 tmp1751765)
   (locals-types
    (tmp1751760 . Boolean)
    (x1751720 . Integer)
    (tmp1751765 . Integer)
    (tmp1751763 . Boolean)
    (tmp1751764 . Integer)
    (tmp1751761 . Boolean)
    (y1751721 . Integer)
    (tmp1751762 . Boolean)))
 (list
  (cons
   'start
   (Block
    (list
     (list
      'lives
      (set 'rax)
      (set 'rax)
      (set 'rax 'x1751720)
      (set 'rax 'x1751720)
      (set 'y1751721 'x1751720)
      (set 'y1751721 'x1751720)
      (set 'al 'y1751721 'x1751720)
      (set 'tmp1751760 'y1751721 'x1751720)
      (set 'tmp1751760 'y1751721 'x1751720)
      (set 'al 'tmp1751760 'y1751721 'x1751720)
      (set 'tmp1751761 'tmp1751760 'y1751721 'x1751720)
      (set 'y1751721 'tmp1751761 'tmp1751760)
      (set 'y1751721 'al 'tmp1751761 'tmp1751760)
      (set 'y1751721 'tmp1751762 'tmp1751761 'tmp1751760)
      (set 'y1751721 'tmp1751762 'tmp1751761)
      (set 'y1751721 'tmp1751762 'tmp1751761)
      (set 'y1751721 'tmp1751762 'tmp1751761)))
    (list
     (Callq 'read_int 0)
     (Instr 'movq (list (Reg 'rax) (Var 'x1751720)))
     (Callq 'read_int 0)
     (Instr 'movq (list (Reg 'rax) (Var 'y1751721)))
     (Instr 'cmpq (list (Imm 10) (Var 'x1751720)))
     (Instr 'set (list 'l (Reg 'al)))
     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751760)))
     (Instr 'cmpq (list (Imm 0) (Var 'x1751720)))
     (Instr 'set (list 'e (Reg 'al)))
     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751761)))
     (Instr 'cmpq (list (Imm 20) (Var 'x1751720)))
     (Instr 'set (list 'e (Reg 'al)))
     (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751762)))
     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751760)))
     (JmpIf 'e 'l1751807)
     (Jmp 'l1751808))))
  (cons
   'l1751807
   (Block
    (list
     (list 'lives (set 'y1751721 'tmp1751761) (set 'y1751721 'tmp1751763) (set 'y1751721 'tmp1751763)))
    (list (Instr 'movq (list (Var 'tmp1751761) (Var 'tmp1751763))) (Jmp 'l1751806))))
  (cons
   'l1751804
   (Block
    (list (list 'lives (set 'tmp1751764) (set) (set)))
    (list (Instr 'movq (list (Var 'tmp1751764) (Reg 'rax))) (Jmp 'conclusion))))
  (cons
   'l1751806
   (Block
    (list
     (list
      'lives
      (set 'y1751721 'tmp1751763)
      (set 'tmp1751764 'y1751721 'tmp1751763)
      (set 'tmp1751764 'y1751721 'tmp1751763)
      (set 'tmp1751763 'tmp1751765 'tmp1751764)
      (set 'tmp1751763 'tmp1751765 'tmp1751764)
      (set 'tmp1751765 'tmp1751764)
      (set 'tmp1751765 'tmp1751764)
      (set 'tmp1751765 'tmp1751764)))
    (list
     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751764)))
     (Instr 'addq (list (Imm 2) (Var 'tmp1751764)))
     (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751765)))
     (Instr 'addq (list (Imm 10) (Var 'tmp1751765)))
     (Instr 'cmpq (list (Imm 1) (Var 'tmp1751763)))
     (JmpIf 'e 'l1751804)
     (Jmp 'l1751805))))
  (cons
   'l1751808
   (Block
    (list
     (list 'lives (set 'y1751721 'tmp1751762) (set 'y1751721 'tmp1751763) (set 'y1751721 'tmp1751763)))
    (list (Instr 'movq (list (Var 'tmp1751762) (Var 'tmp1751763))) (Jmp 'l1751806))))
  (cons
   'l1751805
   (Block
    (list (list 'lives (set 'tmp1751765) (set) (set)))
    (list (Instr 'movq (list (Var 'tmp1751765) (Reg 'rax))) (Jmp 'conclusion)))))))


(define interference-test
  (lambda (ast)
    (match ast
      [(X86Program info Blocks)
       ;;(printf "~a " info)])))
       (printf "~a \n" (dict-ref info 'locals))
       (printf "block is ~a \n" (dict-ref Blocks 'start))
       (define new-Blocks
         (for/list ([(label block) (in-dict Blocks)])
           (cons label block)))
       (printf "new blocks is ~a \n" new-Blocks)])))


;;===========
;; build-move-graph: pseudo-x86* -> pseudo-x86*
;; *annotate program with move graph

(define use-move-biasing #t)

(define (build-move-graph-instr G)
  (lambda (ast)
    (match ast
      [(Instr 'movq (list (Var s) (Var d)))
       (if use-move-biasing
           (add-edge! G s d)
           '())
       ast]
      [else ast])))

(define (build-move-block ast MG)
  (match ast
    [(Block info ss)
     (define new-ss
       (if use-move-biasing
           (let ([nss (for/list ([inst ss])
                        ((build-move-graph-instr MG) inst))])
             (print-dot MG "./move.dot")
             nss)
           ss))
     (Block info new-ss)]
    [else
     (error "R1-reg/build-move-block unhandled" ast)]))

(define (build-move-graph ast)
  (match ast
    [(X86Program info Blocks)
     ;; (define MG (make-graph (dict-ref iinfo 'locals)))
     (define MG (undirected-graph '()))
     (for ([v (dict-ref info 'locals)])
       (add-vertex! MG v))

     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label (build-move-block block MG))))
     (define new-info (dict-set info 'move-graph MG))
     (X86Program new-info new-Blocks)]))


;; ===========
;; allocate-registers: pseudo-x86 -> pseudo-x86
;; Replaces variables with registers and stack locations
;; using graph coloring based on Suduko heuristics
;; This pass encompasses assign-homes

(use-minimal-set-of-registers! #t)

;; 不在饱和度中的颜色
(define (valid-color c v unavail-colors info)
  (not (set-member? unavail-colors c)))

;; unavail-colors为结点v的饱和度
(define (choose-color v unavail-colors move-related info)
  ;; 3
  (define n (num-registers-for-alloc))
  (define biased-selection
    (for/first ([c move-related]
                #:when (valid-color c v unavail-colors info))
      c))
  (define unbiased-selection    
    ;;(for/list
    (for/first ([c (in-naturals)]
                #:when (valid-color c v unavail-colors info))
      c))
  (cond
    [(and biased-selection
          (or (< biased-selection n) (>= unbiased-selection n)))
     ;;(vomit "move-biased, for ~a chose ~a" v biased-selection)
     biased-selection]
    [else unbiased-selection]))

;; (inherit variable-size)
(define variable-size 8)

;; Take into account space for the callee saved registers
;(define (first-offset num-used-callee)
;  (+ (super first-offset num-used-callee)
;     (* num-used-callee (variable-size))))

(define (first-offset num-used-callee)
 (+ (* 1 variable-size)
     (* num-used-callee variable-size))) 

(define (init-num-spills) 0)

(define (update-num-spills spills c)
  (cond
    [(>= c (num-registers-for-alloc))
     (add1 spills)]
    [else spills]))

;; 1. 初始，冲突图
;; 2. 将图中已经存在的寄存器染色（分配数字），此时变量还没有被染色，更新跟已经存在的寄存器相邻的顶点的饱和度
;; 3. 选择最大饱和度的顶点，选择最小的颜色进行染色，更新跟该顶点相邻的结点的饱和度
;; 4. 重复上一步
;; 5. 根据染色分配寄存器
;; 假设现在只有一个寄存器可以分配rcx
;;--------------------
;; 带move的
;; 1. 初始，冲突图和move图
;; 2. 将图中已经存在的寄存器染色(分配数字)，更新跟已经存在的寄存器相邻的顶点的饱和度
;; 3. 选择最大饱和度的顶点，如果有多个，选择move图中存在的顶点，染跟move相关顶点相同的颜色，更新相邻结点饱和度
;; 4. 重复上一步
;; 5. 根据染色分配寄存器

;; 三个hash
;; 一个指定饱和度
;; 一个指定优先级队列中的node
;; 一个指定相应的颜色

;; IG 冲突图
;; MG move图
(define (color-graph IG MG info) ;; DSATUR algorithm
  (define locals (dict-ref info 'locals))
  (define num-spills (init-num-spills))
  (define unavail-colors (make-hash));; pencil marks
  ;; 不可用的color数，优先级队列
  (define (compare u v);; compare saturation
    (>= (set-count (hash-ref unavail-colors u))
        (set-count (hash-ref unavail-colors v))))
  (define Q (make-pqueue compare))
  (define pq-node (make-hash)) ;; maps vars to priority queue nodes
  (define color (make-hash)) ;; maps vars to colors (natural nums)

  ;; 完成第一步，将图中已经存在的寄存器染色(分配数字),更新跟已经存在的寄存器相邻的顶点的饱和度
  (for ([x locals])
    ;; mark neighboring register colors as unavailable
    ;; 找出冲突图中已经存在的寄存器
    (define adj-reg
      (filter (lambda (u) (set-member? registers u))
              (get-neighbors IG x)))
    ;; 先对已经存在的寄存器进行染色
    (define adj-colors (list->set (map register->color adj-reg)))
    ;; 标注x的饱和度（不可用颜色的集合）
    (hash-set! unavail-colors x adj-colors)
    ;; add variables to priority queue
    (hash-set! pq-node x (pqueue-push! Q x)))

  ;; 染色
  ;; Graph coloring
  (while (> (pqueue-count Q) 0)
         ;; 最大饱和度的？这个地方是否应该找出多个
         (define v (pqueue-pop! Q))
         ;; 找出与v有move关系，且已经染色的，为什么要进行排序？
         (define move-related
           (sort (filter (lambda (x) (>= x 0))
                         (map (lambda (k) (hash-ref color k -1))
                              (get-neighbors MG v)))
                 <))
         ;; 染色
         (define c (choose-color v (hash-ref unavail-colors v)
                                 move-related info))
         (verbose "color of ~a is ~a" v c)
         ;; 统计spill的数量
         (set! num-spills (update-num-spills num-spills c))
         (hash-set! color v c)
         ;; mark this color as unavailable for neighbors
         (for ([u (in-neighbors IG v)])
           (when (not (set-member? registers u))
             (hash-set! unavail-colors u
                        (set-add (hash-ref unavail-colors u) c))
             (pqueue-decrease-key! Q (hash-ref pq-node u)))))
  (values color num-spills))
         
(define (identify-home num-used-callee c)
  (define n (num-registers-for-alloc))
  (cond
    [(< c n)
     (Reg (color->register c))]
    [else
     (Deref 'rbp (- (+ (first-offset num-used-callee)
                       (* (- c n) variable-size))))]))
                       ;;(* (- c n) (variable-size)))))]))

(define (callee-color? c)
  (and (< c (num-registers-for-alloc))
       (set-member? callee-save (color->register c))))

(define (used-callee-reg locals color)
  (for/set ([x locals] #:when (callee-color? (hash-ref color x)))
    (color->register (hash-ref color x))))

(define (num-used-callee locals color)
  (set-count (used-callee-reg locals color)))

(define (assign-block-info homes)
  (lambda (b)
    (match b
      [(Block info ss)
       (define new-info (dict-set info 'assign-homes homes))
       (Block new-info ss)])))
       

(define (allocate-registers ast)
  (match ast
    [(X86Program info Blocks)
     (define locals (dict-ref info 'locals))
     (define IG (dict-ref info 'conflicts))
     (define MG (dict-ref info 'move-graph))
     (define-values (color num-spills) (color-graph IG MG info))
     ;; 分配寄存器or栈
     (define homes
       (for/hash ([x locals])
         (define home (identify-home (num-used-callee locals color)
                                     (hash-ref color x)))
         ;;(vomit "home of ~a is ~a" x home)
         ;;(printf "home of ~a is ~a \n" x home)
         (values x home)))

     ;;(printf "homes is ~a \n" homes)
     
     (define new-Blocks
       (for/list ([(label block) (in-dict Blocks)])
         (cons label ((assign-block-info homes) block))))
         ;;(cons label block)))     
         ;;(cons label (assign-homes-block homes) block)))

     (define new-info (dict-remove-all
                       (dict-set (dict-set info 'num-spills num-spills)
                                 'used-callee
                                 (used-callee-reg locals color))
                       (list 'locals 'conflicts 'move-graph)))
     (X86Program new-info new-Blocks)]))


(allocate-registers (build-move-graph
 (build-interference
  (X86Program
   '((locals x1751720 y1751721 tmp1751760 tmp1751761 tmp1751762 tmp1751763 tmp1751764 tmp1751765)
     (locals-types
      (tmp1751760 . Boolean)
      (x1751720 . Integer)
      (tmp1751765 . Integer)
      (tmp1751763 . Boolean)
      (tmp1751764 . Integer)
      (tmp1751761 . Boolean)
      (y1751721 . Integer)
      (tmp1751762 . Boolean)))
   (list
    (cons
     'start
     (Block
      (list
       (list
        'lives
        (set 'rax)
        (set 'rax)
        (set 'rax 'x1751720)
        (set 'rax 'x1751720)
        (set 'y1751721 'x1751720)
        (set 'y1751721 'x1751720)
        (set 'al 'y1751721 'x1751720)
        (set 'tmp1751760 'y1751721 'x1751720)
        (set 'tmp1751760 'y1751721 'x1751720)
        (set 'al 'tmp1751760 'y1751721 'x1751720)
        (set 'tmp1751761 'tmp1751760 'y1751721 'x1751720)
        (set 'y1751721 'tmp1751761 'tmp1751760)
        (set 'y1751721 'al 'tmp1751761 'tmp1751760)
        (set 'y1751721 'tmp1751762 'tmp1751761 'tmp1751760)
        (set 'y1751721 'tmp1751762 'tmp1751761)
        (set 'y1751721 'tmp1751762 'tmp1751761)
        (set 'y1751721 'tmp1751762 'tmp1751761)))
      (list
       (Callq 'read_int 0)
       (Instr 'movq (list (Reg 'rax) (Var 'x1751720)))
       (Callq 'read_int 0)
       (Instr 'movq (list (Reg 'rax) (Var 'y1751721)))
       (Instr 'cmpq (list (Imm 10) (Var 'x1751720)))
       (Instr 'set (list 'l (Reg 'al)))
       (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751760)))
       (Instr 'cmpq (list (Imm 0) (Var 'x1751720)))
       (Instr 'set (list 'e (Reg 'al)))
       (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751761)))
       (Instr 'cmpq (list (Imm 20) (Var 'x1751720)))
       (Instr 'set (list 'e (Reg 'al)))
       (Instr 'movzbq (list (Reg 'al) (Var 'tmp1751762)))
       (Instr 'cmpq (list (Imm 1) (Var 'tmp1751760)))
       (JmpIf 'e 'l1751807)
       (Jmp 'l1751808))))
    (cons
     'l1751807
     (Block
      (list
       (list 'lives (set 'y1751721 'tmp1751761) (set 'y1751721 'tmp1751763) (set 'y1751721 'tmp1751763)))
      (list (Instr 'movq (list (Var 'tmp1751761) (Var 'tmp1751763))) (Jmp 'l1751806))))
    (cons
     'l1751804
     (Block
      (list (list 'lives (set 'tmp1751764) (set) (set)))
      (list (Instr 'movq (list (Var 'tmp1751764) (Reg 'rax))) (Jmp 'conclusion))))
    (cons
     'l1751806
     (Block
      (list
       (list
        'lives
        (set 'y1751721 'tmp1751763)
        (set 'tmp1751764 'y1751721 'tmp1751763)
        (set 'tmp1751764 'y1751721 'tmp1751763)
        (set 'tmp1751763 'tmp1751765 'tmp1751764)
        (set 'tmp1751763 'tmp1751765 'tmp1751764)
        (set 'tmp1751765 'tmp1751764)
        (set 'tmp1751765 'tmp1751764)
        (set 'tmp1751765 'tmp1751764)))
      (list
       (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751764)))
       (Instr 'addq (list (Imm 2) (Var 'tmp1751764)))
       (Instr 'movq (list (Var 'y1751721) (Var 'tmp1751765)))
       (Instr 'addq (list (Imm 10) (Var 'tmp1751765)))
       (Instr 'cmpq (list (Imm 1) (Var 'tmp1751763)))
       (JmpIf 'e 'l1751804)
       (Jmp 'l1751805))))
    (cons
     'l1751808
     (Block
      (list
       (list 'lives (set 'y1751721 'tmp1751762) (set 'y1751721 'tmp1751763) (set 'y1751721 'tmp1751763)))
      (list (Instr 'movq (list (Var 'tmp1751762) (Var 'tmp1751763))) (Jmp 'l1751806))))
    (cons
     'l1751805
     (Block
      (list (list 'lives (set 'tmp1751765) (set) (set)))
      (list (Instr 'movq (list (Var 'tmp1751765) (Reg 'rax))) (Jmp 'conclusion)))))))))

;; ------

;; curr-block为label
(define (fix-block instrs cfg removed-blocks all-blocks curr-block)
  (cond
    [(null? instrs) '()]
    [else (let ([instr (car instrs)])
            (match instr
              ;; check if the target has only this edge
              [(Jmp target) #:when (and (not (equal? target 'conclusion))
                                        (equal? (length (get-neighbors cfg target)) 1)
                                        (< (edge-weight cfg target curr-block) 2))
                            (begin
                              (set-add! removed-blocks target)
                              (append
                               (fix-block (Block-instr* (dict-ref all-blocks target)) cfg removed-blocks all-blocks curr-block)
                               (fix-block (cdr instrs) cfg removed-blocks all-blocks curr-block)))]
              [_ (cons instr (fix-block (cdr instrs) cfg removed-blocks all-blocks curr-block))]))]))


(define (remove-jumps p)
  (match p
    [(X86Program info blocks)
     ;; Get cfg
     (define r-cfg (dict-ref info 'r-cfg))
     ;; tsorted vertices
     (define vertices-order (tsort (transpose r-cfg)))
     ;;keep track of new blocks
     (define new-blocks '())
     ;;keep track of removed blocks
     (define removed-blocks (mutable-set))
     ;;remove jumps
     (for ([vert vertices-order])
       (if (not (set-member? removed-blocks vert))
           (let* ([instrs (Block-instr* (dict-ref blocks vert))] ;; 该顶点(label)对应的所有的instrs
                  [block-info (Block-info (dict-ref blocks vert))] ;; label的info
                  [new-instrs (fix-block instrs r-cfg removed-blocks blocks vert)]
                  [new-block (Block block-info new-instrs)])
             (set! new-blocks (cons (cons vert new-block) new-blocks)))
           (void)))
     ;;(display new-blocks)
     (X86Program info new-blocks)]))



;; =====================================================

;; select-instructions : C0 -> pseudo-x86
;(define (select-instructions p)
;  (error "TODO: code goes here (select-instructions)"))

(define (calc-stack-space ls) (* 8 (length ls)))

;; be related to the function 'explicate-tail' let branch (append new-rhs-vars body-vars)
(define (find-index v ls)
  (cond
    ;;[(eq? v (Var-name (car ls))) 1]
    [(eq? v (car ls)) 1]
    [else (add1 (find-index v (cdr ls)))]
    ))

(define (assign-homes-imm i ls)
  (match i
    [(Reg reg) (Reg reg)]
    [(Imm int) (Imm int)]
    [(Var v) (Deref 'rbp (* -8 (find-index v (cdr ls))))]
   ))
   
(define (assign-homes-instr i ls)
  (match i
    [(Instr op (list e1)) 
     (Instr op (list (assign-homes-imm e1 ls)))]
    [(Instr op (list e1 e2))
     (Instr op (list (assign-homes-imm e1 ls) (assign-homes-imm e2 ls)))]
    [else i]
    ))
    
(define (assign-homes-block b ls)
  (match b
    [(Block info es) 
     (Block info (for/list ([e es]) (assign-homes-instr e ls)))]
    ))

;(define (assign-homes p)
;  (match p
;    ;; The locals-types entry is an alist mapping all the variables in
;    ;; the program to their types (for now, just Integer).
;    ;; the locals-types entry is computed by type-check-Cvar in the support code,
;    [(X86Program info (list (cons 'start es)))
;     ;;(printf "info is ===== ~a \n" (cdr (car info)))
;     (X86Program (list (cons 'stack-space (calc-stack-space (cdr (car info)))))
;       (list (cons 'start (assign-homes-block es (car info)))))]))


;; assign-homes : pseudo-x86 -> pseudo-x86
;(define (assign-homes p)
;  (error "TODO: code goes here (assign-homes)"))

;; ----------

;(define (patch-instr instruction)
;  (match instruction
;    [(Instr op (list (Deref reg off) (Deref reg2 off2)))
;     (list (Instr 'movq (list (Deref reg off) (Reg 'rax)))
;           (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
;    [else (list instruction)]))
;    ;;[else instruction]))
;
;;; append-map
;;; (append* (map proc lst ...))
;;; for each list execute proc, then append all the lists
;(define (patch-block b)
;  (match b
;    [(Block '() instrs)
;     (Block '() (append-map patch-instr instrs))]))
;
;(define (patch-instructions p)
;   (match p
;    [(X86Program info B-list)
;     (X86Program info (map
;                       (lambda (x) `(,(car x) . ,(patch-block (cdr x))))
;                       B-list))]))
;;-----

(define (patch-instructions-instrs instr)
  (match instr
    [(Instr op (list (Deref r1 n1) (Deref r2 n2)))
     (list (Instr 'movq (list (Deref r1 n1) (Reg 'rax)))
           (Instr op (list (Reg 'rax) (Deref r2 n2))))]
    [(Instr 'movq (list (Reg r1) (Reg r2)))
     (cond
       [(equal? r1 r2) '()]
       [else (list instr)])]
    [(Instr 'cmpq (list  arg1 (Imm n)))
     (list (Instr 'movq (list (Imm n) (Reg 'rax)))
           (Instr 'cmpq (list arg1 (Reg 'rax))))]
    [(Instr 'movzbq (list  arg1 (Imm n)))
         (list (Instr 'movq (list (Imm n) (Reg 'rax)))
               (Instr 'mvzbq (list arg1 (Reg 'rax))))]
    [_ (list instr)]))

(define (patch-instructions-block block)
  (match block
    [(Block info instrs)
     (Block info (flatten (for/list ([instr instrs]) 
                            (patch-instructions-instrs instr))))]))

(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (X86Program info (for/list ([block blocks]) 
                          (cons (car block) (patch-instructions-block (cdr block)))))]))



;;--------------
;; 问题
;; 1. main里面的，一条命令里面有两个栈引用，是否需要修改
;; 2. main和conclusion的固定格式的原因是什么？
(define make-prelude
  (lambda ()
    (cons 'main
                (Block '() (list (Instr 'pushq (list (Deref 'rbp 0)))
                                 (Instr 'movq (list (Deref 'rsp 0) (Deref 'rbp 0)))
                                 (Instr 'subq (list (Imm 16) (Deref 'rsp 0)))
                                 (Jmp 'start))))))

(define make-conclusion
  (lambda ()
    (cons 'conclusion
                (Block '() (list (Instr 'addq (list (Imm 16) (Deref 'rsp 0)))
                                 (Instr 'popq (list (Deref 'rbp 0)))
                                 (Retq))))))

(define (prelude-and-conclusion p)
  (match p
    [(X86Program info `((start . ,bs)))
     (X86Program info (list (make-prelude) `(start . ,bs) (make-conclusion)))]))
;     (X86Program info (map
;                       (lambda (x) `(,(car x) . ,(patch-block (cdr x))))
;                       (list (make-prelude B-list (make-conclusion))))]))
    

;; prelude-and-conclusion : x86 -> x86
;(define (prelude-and-conclusion p)
;  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
     ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
     ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
     ("optimize jumps" ,optimize-jumps ,interp-Cif ,type-check-Cif)
     ("instruction selection" ,select-instructions ,interp-x86-1)
     ;;("assign homes" ,assign-homes ,interp-x86-0)
     ;;("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))


