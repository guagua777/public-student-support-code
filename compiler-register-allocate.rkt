#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require graph)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
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

;; 想一想环境中保存的是什么
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
     ;; 想一想返回的应该是什么？
     ;; 最后的表达式，以及最后表达式中变量和原子表达式的对应关系列表
     ;; 变成atom之后的表达式，以及中间变量与对应的atom表达式的对应列表
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

;(define (make-lets bs e)
;  (match bs
;    [`() e]
;    [`((,x . ,e^) . ,bs^)
;     (Let x e^ (make-lets bs^ e))]))

;; rco-exp : exp -> exp
;; 最后会变成一个let
;; 返回最后的结果
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
;; The explicate_tail function takes an exp in LVar as input
;; and produces a tail in CVar (see figure 2.13). 
(define (explicate-tail exp)
  (match exp
    [(Var x) (values (Return (Var x)) '())]
    [(Int n) (values (Return (Int n)) '())]
    ;; 先想想应该返回的是什么
    ;; 应该返回的是顺序的赋值表达式列表，是个Seq，对let中变量和值进行赋值
    [(Let lhs rhs body)
     ;; the right-hand side of a let executes before its body
;     (let*-values
;         ([(body-c0 body-vars) (explicate-tail body)]
;          [(new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0)])
;       (values new-tail (cons lhs (append new-rhs-vars body-vars))))
     ;; body-vars为body中的变量
     ;; body-c0为tail，即为(Return exp) 或者是 (Seq stmt tail)
     (define-values (body-c0 body-vars) (explicate-tail body))
     ;; (printf "exp is ~a , body-c0 is ------ ~a \n" exp body-c0)
     (define-values (new-tail new-rhs-vars) (explicate-assign rhs (Var lhs) body-c0))
     (values new-tail (cons lhs (append new-rhs-vars body-vars)))
     ]
    [(Prim op es)
     (values (Return (Prim op es)) '())]))

;; The explicate_assign function takes an exp in LVar,
;; the variable to which it is to be assigned,
;; and a tail in CVar for the code that comes after the assignment.
;; The explicate_assign function returns a tail in CVar.
;; the c parameter is used for accumulating the output
;; 把r1exp赋值给变量v
;;想想返回值是什么？
;; 对变量进行赋值后，形成的Seq
(define (explicate-assign r1exp v c)
  (match r1exp
    [(Int n)
     ;; 在c的前面加上，这样就反过来了，最里面的会跑到最外面来
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
     ;; 想一想为什么不是(append let-binds^ let-binds)
     ;(values tail^ (cons x (append let-binds^ let-binds)))]
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
       (define-values (tail let-binds) (explicate-tail body))
       ;;(printf "-=-=-=-=-=-=-= ~a ~a \n" tail vars)
       ;; contains an alist that associates the symbol locals with a list of all the variables used in the program. 
       (CProgram (cons (cons 'locals let-binds) info)
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
    ;; one of the args is the same as the left hand side Var
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
    [(CProgram info (list (cons 'start t)))
     (X86Program info
       (list (cons 'start (Block '() (select-instr-tail t)))))]))

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
  (match instr
    [(Instr 'movq (list s d)) (free-vars s)]
    [(Instr name arg*)
     (apply set-union (for/list ([arg arg*]) (free-vars arg)))]
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity)
    ;; (apply set-union (for/list ([a arity]) (free-vars a)))]
    [(Jmp label) (set)]
    [else (error "read-vars unmatched" instr)]))

(define (write-vars instr)
  (match instr
    [(Instr 'movq (list s d)) (free-vars d)]
    [(Instr name arg*) (free-vars (last arg*))]
    [(Jmp label) (set)]
    ;;[(Callq f) (set)]
    [(Callq f arity) (set)]
    ;;[(Callq f arity) 
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

;; what is args of the uncover-list
;; what is the ast
;; it is the result of the instruction selection
(define (uncover-live ast)
  (match ast
    [(X86Program info (list (cons 'start block)))
     (define new-block (uncover-live-block block (set)))
     (X86Program info (list (cons 'start new-block)))]))

;; (define h #hash((a . "apple") (b . "banana")))
;; (for/list ([(k v) (in-dict h)])
;;   (format "~a = ~s" k v))

;(for/list ([i '(1 2 3)]
;             [j "abc"]
;             #:break (not (odd? i))
;             [k #(#t #f)])
;    (cons i j))

;(define test-uncover-match
;  (lambda (x86p)
;    (match x86p
;      [(X86Program info (list (cons 'start bs)))
;       (printf "~a " bs)]
;      [else (error "no match" x86p)])))
  

;; the result of the instruction selection
;(X86Program
; '((locals a708913 b708914)
;   (locals-types (b708914 . Integer) (a708913 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 42) (Var 'a708913)))
;     (Instr 'movq (list (Var 'a708913) (Var 'b708914)))
;     (Instr 'movq (list (Var 'b708914) (Reg 'rax)))
;     (Jmp 'conclusion))))))


;(uncover-live (X86Program
; '((locals a708913 b708914)
;   (locals-types (b708914 . Integer) (a708913 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 42) (Var 'a708913)))
;     (Instr 'movq (list (Var 'a708913) (Var 'b708914)))
;     (Instr 'movq (list (Var 'b708914) (Reg 'rax)))
;     (Jmp 'conclusion)))))))

;;==========
;; 55 minutes
;; build-interference: live-after x graph -> pseudo-x86* -> pseudo-x86*
;; *annotate program with interference graph

(define (build-interference-instr live-after G)
  (lambda (ast)
    (verbose "build-interference-instr " ast live-after)
    (match ast
      [(Instr 'movq (list s d))
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
         (for ([u caller-save-for-alloc])
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
     (define new-info (dict-set info 'conflicts G))
     (X86Program new-info new-Blocks)]))

;(define (build-interference ast)
;  (verbose "build-interference " ast)
;  (match ast
;    [(Program info (CFG cfg))
;     (define locals (dict-ref info 'locals))
;     (define G (undirected-graph '()))
;     (for ([v locals])
;       (add-vertex! G v))
;     (define new-CFG
;       (for/list ([(label block) (in-dict cfg)])
;         (cons label (build-interference-block block G))))
;     (print-dot G "./interfere.dot")
;     (define new-info (dict-set info 'conflicts G))
;     (Program new-info (CFG new-CFG))]))

;(define interference-test
;  (lambda (ast)
;    (match ast
;      [(X86Program info (list (cons 'start block)))
;       ;;(printf "~a " info)])))
;       (printf "~a " (dict-ref info 'locals))])))

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

;(dict-ref
;   (list (list 'lives (set) (set 'a708913) (set 'b708914) (set) (set)))
;   'lives)
      

;(X86Program
; '((locals a708913 b708914) (locals-types (b708914 . Integer) (a708913 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    (list (list 'lives (set) (set 'a708913) (set 'b708914) (set) (set)))
;    (list
;     (Instr 'movq (list (Imm 42) (Var 'a708913)))
;     (Instr 'movq (list (Var 'a708913) (Var 'b708914)))
;     (Instr 'movq (list (Var 'b708914) (Reg 'rax)))
;     (Jmp 'conclusion))))))

;(define for/list-test
;  (lambda (s)
;    s))
;
;(for/list ([i '(a b c)])
;  i)
;  ;;(for/list-test i))


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

;(define/public (build-move-graph ast)
;  (match ast
;    [(Program info (CFG cfg))
;     ;; (define MG (make-graph (dict-ref iinfo 'locals)))
;     (define MG (undirected-graphj '()))
;     (for ([v (dict-ref info 'locals)])
;       (add-vertex! MG v))
;
;     (define new-CFG
;       (for/list ([(label block) (in-dict cfg)])
;         (cons label (build-move-block block MG))))
;     (define new-info (dict-set info 'move-graph MG))
;     (Program new-info (CFG new-CFG))]))


;(build-move-graph (X86Program
; '((locals a708913 b708914)
;   (locals-types (b708914 . Integer) (a708913 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 42) (Var 'a708913)))
;     (Instr 'movq (list (Var 'a708913) (Var 'b708914)))
;     (Instr 'movq (list (Var 'b708914) (Reg 'rax)))
;     (Jmp 'conclusion)))))))

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


;(define/public (allocate-registers ast)
;  (match ast
;    [(Program info (CFG G))
;     (define locals (dict-ref info 'locals))
;     (define IG (dict-ref info 'conflicts))
;     (define MG (dict-ref info 'move-graph))
;     (define-values (color num-spills) (color-graph IG MG info))
;     (define homes
;       (for/hash ([x locals])
;         (define home (identify-home (num-used-callee locals color)
;                                     (hash-ref color x)))
;         (vomit "home of ~a is ~a" x home)
;         (values x home)))
;
;     (define new-CFG
;       (for/list ([(label block) (in-dict G)])
;         (cons label (assign-homes-block homes) block)))
;
;     (define new-info (dict-remove-all
;                       (dict-set (dict-set info 'num-spills num-spills)
;                                 'used-callee
;                                 (used-callee-reg locals color))
;                       (list 'locals 'conflicts 'move-graph)))
;     (Program new-info (CFG new-CFG))]))
                  

;(allocate-registers  (build-interference (build-move-graph
;   (uncover-live (X86Program
; '((locals a708913 b708914)
;   (locals-types (b708914 . Integer) (a708913 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 42) (Var 'a708913)))
;     (Instr 'movq (list (Var 'a708913) (Var 'b708914)))
;     (Instr 'movq (list (Var 'b708914) (Reg 'rax)))
;     (Jmp 'conclusion))))))))))

;> (reg-colors)
;'((r14 . 10)
;  (r13 . 9)
;  (r12 . 8)
;  (rbx . 7)
;  (r10 . 6)
;  (r9 . 5)
;  (r8 . 4)
;  (rdi . 3)
;  (rsi . 2)
;  (rdx . 1)
;  (rcx . 0)
;  (rax . -1)
;  (rsp . -2)
;  (rbp . -3)
;  (r11 . -4)
;  (r15 . -5)
;  (__flag . -6))
;> (use-minimal-set-of-registers! #t)
;> (reg-colors)
;'((rbx . 2)
;  (rdi . 1)
;  (rsi . 0)
;  (rax . -1)
;  (rsp . -2)
;  (rbp . -3)
;  (r11 . -4)
;  (r15 . -5)
;  (__flag . -6))
;> (register->color 'rbx)
;2
;>

; (let ([iii 10])
;    (while (> iii 0)
;           (printf "~a \n" iii)
;           (set! iii (- iii 1))))


;(X86Program
; '((locals v1910087 w1910088 x1910089 y1910090 z1910091 tmp1910092)
;   (locals-types
;    (w1910088 . Integer)
;    (v1910087 . Integer)
;    (tmp1910092 . Integer)
;    (z1910091 . Integer)
;    (y1910090 . Integer)
;    (x1910089 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 1) (Var 'v1910087)))
;     (Instr 'movq (list (Imm 42) (Var 'w1910088)))
;     (Instr 'movq (list (Var 'v1910087) (Var 'x1910089)))
;     (Instr 'addq (list (Imm 7) (Var 'x1910089)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'y1910090)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'z1910091)))
;     (Instr 'addq (list (Var 'w1910088) (Var 'z1910091)))
;     (Instr 'movq (list (Var 'y1910090) (Var 'tmp1910092)))
;     (Instr 'negq (list (Var 'tmp1910092)))
;     (Instr 'movq (list (Var 'z1910091) (Reg 'rax)))
;     (Instr 'addq (list (Var 'tmp1910092) (Reg 'rax)))
;     (Jmp 'conclusion))))))


;(allocate-registers  (build-interference (build-move-graph
;   (uncover-live (X86Program
; '((locals v1910087 w1910088 x1910089 y1910090 z1910091 tmp1910092)
;   (locals-types
;    (w1910088 . Integer)
;    (v1910087 . Integer)
;    (tmp1910092 . Integer)
;    (z1910091 . Integer)
;    (y1910090 . Integer)
;    (x1910089 . Integer)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 1) (Var 'v1910087)))
;     (Instr 'movq (list (Imm 42) (Var 'w1910088)))
;     (Instr 'movq (list (Var 'v1910087) (Var 'x1910089)))
;     (Instr 'addq (list (Imm 7) (Var 'x1910089)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'y1910090)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'z1910091)))
;     (Instr 'addq (list (Var 'w1910088) (Var 'z1910091)))
;     (Instr 'movq (list (Var 'y1910090) (Var 'tmp1910092)))
;     (Instr 'negq (list (Var 'tmp1910092)))
;     (Instr 'movq (list (Var 'z1910091) (Reg 'rax)))
;     (Instr 'addq (list (Var 'tmp1910092) (Reg 'rax)))
;     (Jmp 'conclusion))))))))))
;home of v1910087 is #<Reg: rsi> 
;home of w1910088 is #<Reg: rbx> 
;home of x1910089 is #<Reg: rsi> 
;home of y1910090 is #<Reg: rsi> 
;home of z1910091 is #<Reg: rdi> 
;home of tmp1910092 is #<Reg: rsi> 
;(X86Program
; (list
;  '(locals-types
;    (w1910088 . Integer)
;    (v1910087 . Integer)
;    (tmp1910092 . Integer)
;    (z1910091 . Integer)
;    (y1910090 . Integer)
;    (x1910089 . Integer))
;  '(num-spills . 0)
;  (cons 'used-callee (set 'rbx)))
; (list
;  (cons
;   'start
;   (Block
;    '()
;    (list
;     (Instr 'movq (list (Imm 1) (Var 'v1910087)))
;     (Instr 'movq (list (Imm 42) (Var 'w1910088)))
;     (Instr 'movq (list (Var 'v1910087) (Var 'x1910089)))
;     (Instr 'addq (list (Imm 7) (Var 'x1910089)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'y1910090)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'z1910091)))
;     (Instr 'addq (list (Var 'w1910088) (Var 'z1910091)))
;     (Instr 'movq (list (Var 'y1910090) (Var 'tmp1910092)))
;     (Instr 'negq (list (Var 'tmp1910092)))
;     (Instr 'movq (list (Var 'z1910091) (Reg 'rax)))
;     (Instr 'addq (list (Var 'tmp1910092) (Reg 'rax)))
;     (Jmp 'conclusion))))))



;; info中存储了：
;; num-spills
;; used-callee
;(X86Program
; (list
;  '(locals-types
;    (w1910088 . Integer)
;    (v1910087 . Integer)
;    (tmp1910092 . Integer)
;    (z1910091 . Integer)
;    (y1910090 . Integer)
;    (x1910089 . Integer))
;  '(num-spills . 0)
;  (cons 'used-callee (set 'rbx)))
; (list
;  (cons
;   'start
;   (Block
;    (list
;     (cons
;      'assign-homes
;      (hash
;       'tmp1910092
;       (Reg 'rsi)
;       'v1910087
;       (Reg 'rsi)
;       'w1910088
;       (Reg 'rbx)
;       'x1910089
;       (Reg 'rsi)
;       'y1910090
;       (Reg 'rsi)
;       'z1910091
;       (Reg 'rdi))))
;    (list
;     (Instr 'movq (list (Imm 1) (Var 'v1910087)))
;     (Instr 'movq (list (Imm 42) (Var 'w1910088)))
;     (Instr 'movq (list (Var 'v1910087) (Var 'x1910089)))
;     (Instr 'addq (list (Imm 7) (Var 'x1910089)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'y1910090)))
;     (Instr 'movq (list (Var 'x1910089) (Var 'z1910091)))
;     (Instr 'addq (list (Var 'w1910088) (Var 'z1910091)))
;     (Instr 'movq (list (Var 'y1910090) (Var 'tmp1910092)))
;     (Instr 'negq (list (Var 'tmp1910092)))
;     (Instr 'movq (list (Var 'z1910091) (Reg 'rax)))
;     (Instr 'addq (list (Var 'tmp1910092) (Reg 'rax)))
;     (Jmp 'conclusion))))))


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

(define (assign-homes p)
  (match p
    ;; The locals-types entry is an alist mapping all the variables in
    ;; the program to their types (for now, just Integer).
    ;; the locals-types entry is computed by type-check-Cvar in the support code,
    [(X86Program info (list (cons 'start es)))
     ;;(printf "info is ===== ~a \n" (cdr (car info)))
     (X86Program (list (cons 'stack-space (calc-stack-space (cdr (car info)))))
       (list (cons 'start (assign-homes-block es (car info)))))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
;(define (assign-homes p)
;  (error "TODO: code goes here (assign-homes)"))

(define (patch-instr instruction)
  (match instruction
    [(Instr op (list (Deref reg off) (Deref reg2 off2)))
     (list (Instr 'movq (list (Deref reg off) (Reg 'rax)))
           (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
    [else (list instruction)]))
    ;;[else instruction]))

;; append-map
;; (append* (map proc lst ...))
;; for each list execute proc, then append all the lists
(define (patch-block b)
  (match b
    [(Block '() instrs)
     (Block '() (append-map patch-instr instrs))]))

(define (patch-instructions p)
   (match p
    [(X86Program info B-list)
     (X86Program info (map
                       (lambda (x) `(,(car x) . ,(patch-block (cdr x))))
                       B-list))]))

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

;(define make-prelude
;  (lambda ()
;    (cons 'main
;                (Block '() (list (Instr 'pushq (list 'rbp))
;                                 (Instr 'movq (list 'rsp 'rbp))
;                                 (Instr 'subq (list (Imm 16) 'rsp))
;                                 (Jmp 'start))))))
;
;(define make-conclusion
;  (lambda ()
;    (cons 'conclusion
;                (Block '() (list (Instr 'addq (list (Imm 16) 'rsp))
;                                 (Instr 'popq (list 'rbp))
;                                 (Retq))))))

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
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))


;; patch-instructions : psuedo-x86 -> x86
;(define (patch-instructions p)
;  (error "TODO: code goes here (patch-instructions)"))

;
;(define (print-x86-imm e)
;  (match e
;    [(Deref reg i)
;     (format "~a(%~a)" i reg)]
;    [(Imm n) (format "$~a" n)]
;    [(Reg r) (format "%~a" r)]
;    ))
;
;(define (print-x86-instr e)
;  (verbose "R1/print-x86-instr" e)
;  (match e
;    [(Callq f)
;     (format "\tcallq\t~a\n" (label-name (symbol->string f)))]
;    [(Jmp label) (format "\tjmp ~a\n" (label-name label))]
;    [(Instr instr-name (list s d))
;     (format "\t~a\t~a, ~a\n" instr-name
;             (print-x86-imm s) 
;             (print-x86-imm d))]
;    [(Instr instr-name (list d))
;     (format "\t~a\t~a\n" instr-name (print-x86-imm d))]
;    [else (error "R1/print-x86-instr, unmatched" e)]
;    ))
;
;(define (print-x86-block e)
;  (match e
;    [(Block info ss)
;     (string-append* (for/list ([s ss]) (print-x86-instr s)))]
;    [else
;     (error "R1/print-x86-block unhandled " e)]))
;
;(define (print-x86 e)
;  (match e
;    [(Program info (CFG G))
;     (define stack-space (dict-ref info 'stack-space))
;     (string-append
;      (string-append*
;       (for/list ([(label block) (in-dict G)])
;         (string-append (format "~a:\n" (label-name label))
;                        (print-x86-block block))))
;      "\n"
;      (format "\t.globl ~a\n" (label-name "main"))
;      (format "~a:\n" (label-name "main"))
;      (format "\tpushq\t%rbp\n")
;      (format "\tmovq\t%rsp, %rbp\n")
;      (format "\tsubq\t$~a, %rsp\n" (align stack-space 16))
;      (format "\tjmp ~a\n" (label-name 'start))
;      (format "~a:\n" (label-name 'conclusion))
;      (format "\taddq\t$~a, %rsp\n" (align stack-space 16))
;      (format "\tpopq\t%rbp\n")
;      (format "\tretq\n")
;      )]
;    [else (error "print-x86, unmatched" e)]
;    ))

