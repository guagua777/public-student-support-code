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
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "type-check-Lvec.rkt")
(require "type-check-Cvec.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
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

;(pe-exp
; (Prim '+ (list (Int 1) (Prim '+ (list (Prim 'read '()) (Int 1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; prelude的最主要的事情是：向下移动栈指针
;; conclusion最主要的事情是：将prelude移动的指针移回去

;; prelude移动r15指针，the root stack pointer
;; conclusion移回r15指针

;; prelude第一步保存返回地址 return address
;; caller is map-vec
;; callee is add1

;; who ever called map-vec, 所以需要保存who的rbp

;In the context of a procedure call, the return address is the location of the instruction
;that immediately follows the call instruction on the caller side.
;The function call instruction, callq, pushes the return address onto the stack prior to jumping to the procedure.
;The register rbp is the base pointer and is used to access variables
;that are stored in the frame of the current procedure call.
;The base pointer of the caller is stored immediately after the return address. 

;; 35分钟 explicate control

;; conclusion
;; 1. move the stack point
;; 2. pop the callee saved register
;; 3. pop the rbp

;rdi rsi rdx rcx r8 r9

;The caller sets the stack pointer, register rsp, to the last data item in its frame.
;The callee must not change anything in the caller’s frame, that is, anything that is at or above the stack pointer.
;The callee is free to use locations that are below the stack pointer.

;; caller saved: rax rcx rdx rsi rdi r8 r9 r10 r11
;; callee saved: rsp rbp rbx r12 r13 r14 r15


;;------------------------------------------------------
;; the process of compiler
;shrink --- uniquify --- reveal functions --- limit functions --- expose allocation ---
;uncover get! --- remove complex operands --- explicate control --- ....

;; reveal 和 limit 倒换了下


;; -------------------------------------------------------------------------------------
;; shrink

(define shrink-exp
  (lambda (e)
    (match e
      [(Apply f es)
       (define new-f (shrink-exp f))
       (define new-es (for/list ([e es]) (shrink-exp e)))
       (Apply new-f new-es)]
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
      
      
;(define shrink
;  (lambda (p)
;    (match p
;      [(Program info e)
;       (Program info (shrink-exp e))])))


;(define (non-apply-ast)
;  (set-union (source-primitives)
;             (set 'eq? 'vector 'vector-ref 'vector-set! 'if 'let
;                  'define 'program 'void 'fun-ref 'has-type
;                  'collect 'allocate 'global-value)))
;
;(define (fun-def-name d)
;  (match d
;    [(Def f ps rt info body)
;     f]
;    [else
;     (error 'fun-def-name "ill-formed function definition in ~a" d)]))

;(define (shrink-exp e)
;  (match e
;    ;; 参考Lfun的抽象语法
;    [(Apply f es)
;     (define new-f (shrink-exp f))
;     (define new-es (for/list ([e es]) (shrink-exp e)))
;     (Apply new-f new-es)]
;    [else
;     (super shrink-exp e)]))

(define (shrink-def d)
  (match d
    [(Def f params rt info body)
     (Def f params rt info (shrink-exp body))]
    [else
     (error "shrink-def error" d)]))

(define (shrink e)
  (match e
    [(ProgramDefsExp info ds body)
     (define ds^ (for/list ([d ds]) (shrink-def d)))
     (define body^ (shrink-exp body))
     (define main (Def 'main '() 'Integer '() body^))
     (ProgramDefs info (append ds^ (list main)))]
    [else
     (error "shrink couldn't match" e)]))

;; 将body使用main函数包裹起来

;; shrink后将ProgramDefsExp变成了ProgramDefs，也就是多个函数的列表

;(shrink 
;(ProgramDefsExp
; '()
; (list
;  (Def
;   'map
;   '((f : (Integer -> Integer)) (v : (Vector Integer Integer)))
;   '(Vector Integer Integer)
;   '()
;   (HasType
;    (Prim
;     'vector
;     (list
;      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v) (Int 0)))))
;      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v) (Int 1)))))))
;    '(Vector Integer Integer)))
;  (Def 'inc '((x : Integer)) 'Integer '() (Prim '+ (list (Var 'x) (Int 1)))))
; (Prim
;  'vector-ref
;  (list
;   (Apply
;    (Var 'map)
;    (list
;     (Var 'inc)
;     (HasType
;      (Prim 'vector (list (Int 0) (Int 41)))
;      '(Vector Integer Integer))))
;   (Int 1)))))


;;--------------------------------------------------------------------------------------
;; partial-eval Lfun -> Lfun

;(define (pe-exp env) 
;  (lambda (e)
;    ;(copious "Lfun pe-exp" e)
;    (define recur (pe-exp env))
;    (match e
;      [(Apply f es)
;       (define new-es (map recur es))
;       (define new-f (recur f))
;       (Apply new-f new-es)]
;      [else
;       (super ((pe-exp env) e))])))
;
;(define (pe-def d)
;  (match d
;    [(Def f ps rt info body)
;     (Def f ps rt info ((pe-exp '()) body))]))
;
;(define (partial-eval e)
;  (match e
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds]) (pe-def d)))]))

;;----------------------------------------------------------------
;; uniquify

;; 环境中保存的是什么？
;; 1. 对应的实际数据
;; 2. 对应的类型
;; 3. 对应的别名


(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(SetBang x rhs)
       (SetBang (dict-ref env x) ((uniquify-exp env) rhs))]
      [(Begin es body)
       (Begin (for/list ([e es]) ((uniquify-exp env) e))
              ((uniquify-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(HasType e type)
       (HasType ((uniquify-exp env) e) type)]
      [(Let x e body)
       (let* ([new-sym (gensym x)]
              [new-env (dict-set env x new-sym)])
         (Let new-sym ((uniquify-exp env) e) ((uniquify-exp new-env) body)))]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(Apply f es)
       (define new-es (map (uniquify-exp env) es))
       (define new-f ((uniquify-exp env) f))
       (Apply new-f new-es)])))

(define (uniquify-def env)
  (lambda (d)
    (match d
      [(Def f (list `[,xs : ,ps] ...) rt info body)
       ;; 使用新的参数名替换老的参数名
       (define new-xs (for/list ([x xs]) (gensym x)))
       (define new-env (append (map cons xs new-xs) env))
       ;; 使用新的函数名替换老的函数名
       (Def (cdr (assq f env))
            (map (lambda (x p) `[,x : ,p]) new-xs ps)
            rt info
            ((uniquify-exp new-env) body))])))
       
;(define (uniquify p)
;  (match p
;    [(ProgramDefs info e)
;     (Program info ((uniquify-exp '()) e))]))

(define (uniquify p)
  (match p
    [(ProgramDefs info ds)
     (define new-env (for/list ([d ds])
                       (match d
                         [(Def f (list `[,xs : ,ps] ...) rt info body)
                          (define new-f (cond
                                          [(eq? f 'main) 'main]
                                          [else (gensym f)]))
                          (cons f new-f)]
                         [else (error "illegal def")])))
     (ProgramDefs info (for/list ([d ds]) ((uniquify-def new-env) d)))]))

;(define/override (uniquify-exp env)
;  (lambda (e)
;    (define recur (uniquify-exp env))
;    (match e
;      [(HasType e t)
;       (HasType (recur e) t)]
;      [(Apply f es)
;       (define new-es (map recur es))
;       (define new-f (recur f))
;       (Apply new-f new-es)]
;      [else
;       ((super uniquify-exp env) e)])))
;
;(define/public (uniquify-def env)
;  (lambda (d)
;    (match d
;      [(Def f (list `[,xs : ,ps] ...) rt info body)
;       (define new-xs (for/list ([x xs]) (gensym (racket-id->c-id x))))
;       (define new-env (append (map cons xs new-xs) env))
;       (Def (cdr (assq f env))
;            (map (lambda (x t) `[,x : ,t]) new-xs ps)
;            rt info ((uniquify-exp new-env) body))])))
;
;(define/override (uniquify e)
;  (match e
;    [(ProgramDefs info ds)
;     (define new-env
;       (for/list ([d ds])
;         (match d
;           [(Def f (list `[,xs : ,ps] ...) rt info body)
;            (define new-f
;              (cond
;                [(eq? f 'main) 'main]
;                [else (gensym (racket-id->c-id f))]))
;            (cons f new-f)]
;           [else
;            (error "ill def")])))
;     (ProgramDefs info (for/list ([d ds]) ((uniquify-def new-env) d)))]))

;(uniquify
; (ProgramDefs
;  '()
;  (list
;   (Def
;    'map
;    '((f : (Integer -> Integer))
;      (v : (Vector Integer Integer)))
;    '(Vector Integer Integer)
;    '()
;    (HasType
;     (Prim
;      'vector
;      (list
;       (Apply
;        (Var 'f)
;        (list (Prim 'vector-ref (list (Var 'v) (Int 0)))))
;       (Apply
;        (Var 'f)
;        (list (Prim 'vector-ref (list (Var 'v) (Int 1)))))))
;     '(Vector Integer Integer)))
;   (Def
;    'inc
;    '((x : Integer))
;    'Integer
;    '()
;    (Prim '+ (list (Var 'x) (Int 1))))
;   (Def
;    'main
;    '()
;    'Integer
;    '()
;    (Prim
;     'vector-ref
;     (list
;      (Apply
;       (Var 'map)
;       (list
;        (Var 'inc)
;        (HasType
;         (Prim 'vector (list (Int 0) (Int 41)))
;         '(Vector Integer Integer))))
;      (Int 1)))))))

;;--------------------------------------------------------------------------------------
;; reveal functions and application

(define (reveal-functions-exp funs)
  (lambda (e)
    (let* ([recur (reveal-functions-exp funs)])
      (match e
        [(Int n) (Int n)]
        [(Var x)
         (cond
           [(assq x funs);;(memq x funs)
            (define f-pcount (assq x funs))
            (FunRef (car f-pcount) (cdr f-pcount))]
           [else (Var x)])]
        [(Void) (Void)]
        [(Bool b) (Bool b)]
        [(HasType e t) (HasType (recur e) t)]
        [(Let x e body)
         (Let x (recur e) (recur body))]
        [(If cnd thn els)
         (If (recur cnd) (recur thn) (recur els))]
        [(Prim op es)
         (Prim op (map recur es))]
        [(Apply f es)
         (Apply (recur f) (map recur es))]
        [else
         (error "reveal error")]))))

(define (reveal-functions-def funs)
  (lambda (e)
    (match e
      [(Def f params rt info body)
       (Def f params rt info ((reveal-functions-exp funs) body))]
      [else
       (error "reveal def error")])))

(define (reveal-functions e)
  (match e
    [(ProgramDefs info ds)
     (define funs (for/list ([d ds])
                    (cons (Def-name d) (length (Def-param* d)))));;(Def-name d)))
     (ProgramDefs info (for/list ([d ds])
                         ((reveal-functions-def funs) d)))]
    [else
     (error "reveal error")]))

;(reveal-functions
;(uniquify
; (ProgramDefs
;  '()
;  (list
;   (Def
;    'map
;    '((f : (Integer -> Integer))
;      (v : (Vector Integer Integer)))
;    '(Vector Integer Integer)
;    '()
;    (HasType
;     (Prim
;      'vector
;      (list
;       (Apply
;        (Var 'f)
;        (list (Prim 'vector-ref (list (Var 'v) (Int 0)))))
;       (Apply
;        (Var 'f)
;        (list (Prim 'vector-ref (list (Var 'v) (Int 1)))))))
;     '(Vector Integer Integer)))
;   (Def
;    'inc
;    '((x : Integer))
;    'Integer
;    '()
;    (Prim '+ (list (Var 'x) (Int 1))))
;   (Def
;    'main
;    '()
;    'Integer
;    '()
;    (Prim
;     'vector-ref
;     (list
;      (Apply
;       (Var 'map)
;       (list
;        (Var 'inc)
;        (HasType
;         (Prim 'vector (list (Int 0) (Int 41)))
;         '(Vector Integer Integer))))
;      (Int 1))))))))

;;--------------------------------------------------------------------------------------
;; limit-functions

;; 需要改动的点
;; 1. 函数定义
;; 2. 对应的函数定义中的body，body里面的参数需要从改变后的vector中获取
;; 3. 函数调用


(define (limit-type t)
  (match t
    ;; 参数为vector
    [`(Vector ,ts ...)
     (define ts^ (for/list ([t ts]) (limit-type t)))
     `(Vector ,@ts^)]
    ;; 参数为函数
    [`(,ts ... -> ,rt)
     (define ts^ (for/list ([t ts]) (limit-type t)))
     (define rt^ (limit-type rt))
     (define n (vector-length arg-registers))
     (cond
       [(> (length ts^) n)
        (define-values (first-ts last-ts) (split-at ts^ (- n 1)))
        `(,@first-ts (Vector ,@last-ts) -> ,rt^)]
       [else
        `(,@ts^ -> ,rt^)])]
    ;; 普通类型
    [else t]))

(define (limit-functions-exp param-env)
  (lambda (e)
    (let ([recur (limit-functions-exp param-env)])
      (match e
        [(Int n) e]
        [(Var x)
         (let ([res (assq x param-env)])
           (cond
             [res
              (match res
                [`(,arg ,typ1 ,typ2 ,vec ,ind)
                 (Prim 'vector-ref (list vec (Int ind)))] ;; (Var xi) ⇒ (Prim 'vector-ref (list tup (Int k)))
                [else (error "res is unmatched")])]
             [else (Var x)]))]
        [(FunRef f n)
         (FunRef f n)]
        [(Let x e body)
         (Let x (recur e) (recur body))]
        [(Void) (Void)]
        [(Bool b) (Bool b)]
        [(If cnd thn els)
         (If (recur cnd) (recur thn) (recur els))]
        [(HasType e t) ;; 注意 看看HasType的BNF定义，hastype是怎么来的
         (HasType (recur e) (limit-type t))]
        [(Prim op es)
         (Prim op (map recur es))]
        [(Apply f es)
         (define n (vector-length arg-registers))
         (cond
           [(<= (length es) n)
            (Apply f (map recur es))]
           [else
            ;; pass the first n-1 arguments as normal, and the rest in a vector
            (define-values (first-es last-es)
              (cond
                [(> (length es) n)
                 (split-at es (- n 1))]
                [else
                 (values es '())]))
            ;(printf "last-es is ~a \n" last-es)
            ;; (e0 e1 ... en) ⇒ (e0 e1 ...e5 (vector e6 ...en))
            (define vector-val (Prim 'vector (map recur last-es))) 
            (Apply f (append (map recur first-es) (list vector-val)))])]
        [else
         (error "limit functions exp unmatched ~a" e)]))))

(define (limit-functions-def d)
  (match d
    [(Def f params rt info body)
     (define n (vector-length arg-registers))
     ;; update the parameter types
     (define new-params (for/list ([p params])
                          (match p
                            [`[,x : ,T]
                             `[,x : ,(limit-type T)]])))
     (cond
       [(<= (length new-params) n)
        (Def f new-params rt info ((limit-functions-exp '()) body))]
       [else
        (define vec-param (gensym 'vec-param))
        ;; separate the first n-1 parameters from the rest
        (define-values (first-params last-params)
          (cond
            [(> (length new-params) n)
             (split-at new-params (- n 1))]
            [else
             (values new-params '())]))
        ;; create the type for the new vector paramter
        (define vec-typ
          `(Vector ,@(map (lambda (e)
                            (match e
                              [`(,arg : ,typ)
                               typ])) last-params))) ;; 只要类型
        ;; create an environment for helping to translate parameters to vector references
        (define param-env
          (map (lambda (e i)
                 (match e
                   [`(,arg : ,typ)
                    `(,arg ,typ ,vec-typ ,(Var vec-param) ,i)]))
               last-params (range (length last-params))))
        ;(printf "param-env ======= is ~a \n" param-env)
        (define new-body ((limit-functions-exp param-env) body))
        (Def f (append first-params `((,vec-param : ,vec-typ))) rt info new-body)])]))
          
         
(define (limit-functions e)
  (match e
    [(ProgramDefs info ds)
     (ProgramDefs info (for/list ([d ds]) (limit-functions-def d)))]
    [else
     (error "def is error")]))


;((v5540345 (Vector Integer Integer Integer Integer Integer Integer Integer)
;           (Vector
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer))
;           (Var: vec-param540349) 0)
;
; (v6540346 (Vector Integer Integer Integer Integer Integer Integer Integer)
;           (Vector
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer))
;           (Var: vec-param540349) 1)
; (v7540347 (Vector Integer Integer Integer Integer Integer Integer Integer)
;           (Vector
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer)
;            (Vector Integer Integer Integer Integer Integer Integer Integer))
;           (Var: vec-param540349) 2))

#;(limit-functions
(uniquify
(shrink
(ProgramDefsExp
 '()
 (list
  (Def
   'map
   '((f : (Integer -> Integer))
     (v1 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v2 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v3 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v4 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v5 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v6 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v7 : (Vector Integer Integer Integer Integer Integer Integer Integer)))
   '(Vector Integer Integer Integer Integer Integer Integer Integer)
   '()
   (HasType
    (Prim
     'vector
     (list
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v1) (Int 0)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v2) (Int 1)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v3) (Int 2)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v4) (Int 3)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v5) (Int 4)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v6) (Int 5)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v7) (Int 6)))))))
    '(Vector Integer Integer Integer Integer Integer Integer Integer)))
  (Def 'inc '((x : Integer)) 'Integer '() (Prim '+ (list (Var 'x) (Int 1)))))
 (Prim
  'vector-ref
  (list
   (Apply
    (Var 'map)
    (list
     (Var 'inc)
     (HasType
      (Prim
       'vector
       (list (Int 1) (Int 2) (Int 3) (Int 4) (Int 5) (Int 6) (Int 7)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list (Int 11) (Int 22) (Int 33) (Int 44) (Int 55) (Int 66) (Int 77)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111)
        (Int 222)
        (Int 333)
        (Int 444)
        (Int 555)
        (Int 666)
        (Int 777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111)
        (Int 2222)
        (Int 3333)
        (Int 4444)
        (Int 5555)
        (Int 6666)
        (Int 7777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111)
        (Int 22222)
        (Int 33333)
        (Int 44444)
        (Int 55555)
        (Int 66666)
        (Int 77777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111111)
        (Int 222222)
        (Int 333333)
        (Int 444444)
        (Int 555555)
        (Int 666666)
        (Int 777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111111)
        (Int 2222222)
        (Int 3333333)
        (Int 4444444)
        (Int 5555555)
        (Int 6666666)
        (Int 7777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111111)
        (Int 22222222)
        (Int 33333333)
        (Int 44444444)
        (Int 55555555)
        (Int 66666666)
        (Int 77777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))))
   (Int 5)))))))

#;(limit-functions
(uniquify
(shrink
(ProgramDefsExp
 '()
 (list
  (Def
   'map
   '((f : (Integer -> Integer)) (v : (Vector Integer Integer)))
   '(Vector Integer Integer)
   '()
   (HasType
    (Prim
     'vector
     (list
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v) (Int 0)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v) (Int 1)))))))
    '(Vector Integer Integer)))
  (Def 'inc '((x : Integer)) 'Integer '() (Prim '+ (list (Var 'x) (Int 1)))))
 (Prim
  'vector-ref
  (list
   (Apply
    (Var 'map)
    (list
     (Var 'inc)
     (HasType
      (Prim 'vector (list (Int 0) (Int 41)))
      '(Vector Integer Integer))))
   (Int 1)))))))



;;--------------------------------------------------------------------------------------
;; expose allocation

(define (expose-exp e)
  (match e
    [(HasType (Prim 'vector es) type)
     (let* ([len (length es)]
            [bytes (* 8 len)]
            ;; vector的变量名
            [vect (gensym 'vec)]
            ;; 生成n个变量
            [vars (generate-n-vars len)])
       ;; 只形成第一部分的let,其余的嵌在其中的do-allocate中
       ;; do-allocate中嵌入let-set的部分
       ;; let-set的中间嵌入最终的值(HasType (Var vect) type)
       (expend-into-lets vars ;; 该参数和对应的exps,形成部分1, a sequence of temporary variable bindings for the initializing expressions,
                         ;;vars 对应的 exps
                         ;; 想想sicp中的name,命名
                         (for/list ([e es]) (expose-exp e)) 
                         ;;部分2  a conditional call to collect,
                         (do-allocate vect len bytes ;;vector的变量名
                                      ;; the initialization of the tuple. 各种set
                                      (bulk-vector-set
                                       ;; 最终的返回值
                                       (HasType (Var vect) type)
                                       ;; 与第一部分let中对应的变量
                                       vars type)
                                      type)
                         type))]
    [(Let x v body)
     (Let x (expose-exp v) (expose-exp body))]
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [(FunRef f n) (FunRef f n)]
    [(Apply f es)
     (Apply f (for/list ([e es]) (expose-exp e)))]
    [else e]))
                 
(define (generate-n-vars n)
  (if (zero? n)
      '()
      (cons (gensym 'tmp) (generate-n-vars (sub1 n)))))

;; base改为continuation更合适
(define (expend-into-lets vars exps base base-type)
  (if (empty? exps)
      ;; 嵌入到其中的部分
      ;; 有三次嵌入,分别是allocate和let-set以及最终值
      base
      (HasType (Let (car vars) (car exps)
                    (expend-into-lets (cdr vars) (cdr exps) base base-type))
               base-type)))

;; base改为continuation更合适
(define (do-allocate vect len bytes base type)
  (Let '_ (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int bytes)))
                             (GlobalValue 'fromspace_end)))
              (Void)
              (Collect bytes))
       ;;body
       (Let vect (Allocate len type)
            ;; 嵌入其中的let-set
            base)))

;; vect为continuation
(define (bulk-vector-set vect vars type)
  (expend-into-lets (duplicate '_ (length vars)) (make-vector-set-exps vect 0 vars)
                    ;; base 嵌入到let-set中的部分,也就是最终的值
                    vect type))

(define (duplicate x n)
  (if (zero? n)
      '()
      (cons x (duplicate x (sub1 n)))))

(define (make-vector-set-exps vect accum vars) ;; accum 为index
  (if (empty? vars)
      '()
      (cons (Prim 'vector-set! (list vect (Int accum) (Var (car vars))))
            (make-vector-set-exps vect (add1 accum) (cdr vars)))))

(define (expose-allocation-def def)
  (match def
    [(Def f params t info e)
     (Def f params t info (expose-exp e))];(expose-alloc-exp e))]
    [else
     (error "expose allocation def error")]))


;(define (expose-p p)
;  (match p
;    [(Program info e)
;     (Program info (expose-exp e))]))

(define (expose-allocation e)
  (match e
    [(ProgramDefs info ds)
     (ProgramDefs info (for/list ([d ds]) (expose-allocation-def d)))]))

#;(expose-allocation
(limit-functions
(uniquify
(shrink
(ProgramDefsExp
 '()
 (list
  (Def
   'map
   '((f : (Integer -> Integer))
     (v1 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v2 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v3 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v4 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v5 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v6 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v7 : (Vector Integer Integer Integer Integer Integer Integer Integer)))
   '(Vector Integer Integer Integer Integer Integer Integer Integer)
   '()
   (HasType
    (Prim
     'vector
     (list
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v1) (Int 0)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v2) (Int 1)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v3) (Int 2)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v4) (Int 3)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v5) (Int 4)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v6) (Int 5)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v7) (Int 6)))))))
    '(Vector Integer Integer Integer Integer Integer Integer Integer)))
  (Def 'inc '((x : Integer)) 'Integer '() (Prim '+ (list (Var 'x) (Int 1)))))
 (Prim
  'vector-ref
  (list
   (Apply
    (Var 'map)
    (list
     (Var 'inc)
     (HasType
      (Prim
       'vector
       (list (Int 1) (Int 2) (Int 3) (Int 4) (Int 5) (Int 6) (Int 7)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list (Int 11) (Int 22) (Int 33) (Int 44) (Int 55) (Int 66) (Int 77)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111)
        (Int 222)
        (Int 333)
        (Int 444)
        (Int 555)
        (Int 666)
        (Int 777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111)
        (Int 2222)
        (Int 3333)
        (Int 4444)
        (Int 5555)
        (Int 6666)
        (Int 7777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111)
        (Int 22222)
        (Int 33333)
        (Int 44444)
        (Int 55555)
        (Int 66666)
        (Int 77777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111111)
        (Int 222222)
        (Int 333333)
        (Int 444444)
        (Int 555555)
        (Int 666666)
        (Int 777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111111)
        (Int 2222222)
        (Int 3333333)
        (Int 4444444)
        (Int 5555555)
        (Int 6666666)
        (Int 7777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111111)
        (Int 22222222)
        (Int 33333333)
        (Int 44444444)
        (Int 55555555)
        (Int 66666666)
        (Int 77777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))))
   (Int 5))))))))



;;----------------------------------------------------------
;; uncover-get

;We mark each read from a mutable variable with the form get! (GetBang in abstract syntax)

(define (collect-set! e)
  (match e
    [(Var x) (set)]
    [(Int n) (set)]
    [(Let x rhs body)
     (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs)
     (set-union (set var) (collect-set! rhs))]
    [(Prim 'read '()) (set)]
    [(Prim op es)
     (for/fold ([r (set)]) ([e es]) (set-union r (collect-set! e)))]
    [(If cnd thn els)
     (set-union (collect-set! cnd) (collect-set! thn) (collect-set! els))]
    [(Begin es body)
     (define es-set
       (for/fold ([r (set)]) ([e es]) (set-union r (collect-set! e))))
     (set-union es-set (collect-set! body))]
    [(WhileLoop cnd body)
     (set-union (collect-set! cnd) (collect-set! body))]))


;; for 返回值为void
;; for/list 返回值为list
;; for/lists 返回多个list
;; for/fold 返回值为收集的结果

(define ((uncover-get!-exp set!-vars) e)
  (match e
    [(Var x)
     (if (set-member? set!-vars x)
         (GetBang x)
         (Var x))]
    [(Int n) (Int n)]
    [(Let x rhs body)
     (Let x ((uncover-get!-exp set!-vars) rhs) ((uncover-get!-exp set!-vars) body))]
    [(SetBang var rhs)
     (SetBang var ((uncover-get!-exp set!-vars) rhs))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim op es)
     (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]
    [(If cnd thn els)
     (If ((uncover-get!-exp set!-vars) cnd)
         ((uncover-get!-exp set!-vars) thn)
         ((uncover-get!-exp set!-vars) els))]
    [(Begin es body)
     (Begin
      (for/list ([e es]) ((uncover-get!-exp set!-vars) e))
      ((uncover-get!-exp set!-vars) body))]
    [(WhileLoop cnd body)
     (WhileLoop ((uncover-get!-exp set!-vars) cnd)
                ((uncover-get!-exp set!-vars) body))]))

(define uncover-get!
  (lambda (exp)
    (match exp
      [(Program info e)
       (define set-coll (collect-set! e))
       (Program info ((uncover-get!-exp set-coll) e))])))    

;;----------------------------------------------------------------
;; remove complex

;(define (remove-complex-opera* p)
;    (match p
;      [(Program info e)
;       (Program info (rco-exp e))]))

(define (remove-complex-opera* e)
  (match e
    [(ProgramDefs info ds)
     (ProgramDefs info (for/list ([d ds]) (rco-def d)))]))

(define (rco-atom e)
  ;(printf "e is ===== ~a \n" e)
  (match e
    [(Var x) (values (Var x) '())]
    [(Int n) (values (Int n) '())]
    [(Bool b) (values (Bool b) '())]
    [(HasType e^ type)
     (define new-e (rco-exp e^))
     (values (HasType new-e type) '())]
    [(GlobalValue x)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (GlobalValue x))))]
    [(Collect n) ;`(collect ,n)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (Collect n))))]
    [(Allocate amount type) ;`(allocate ,n ,type)
     (define tmp (gensym 'tmp))
     (values (Var tmp) (list (cons tmp (Allocate amount type))))]
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
    [(Void)
     (values (Void) '())]
    [(FunRef f n)
     (define tmp (gensym 'tmp))
     (values (Var tmp) `((,tmp . ,(FunRef f n))))]
    [(Apply f es)
     (define-values (new-f f-ss) (rco-atom f))
     (define-values (new-es sss) (for/lists (ls1 ls2) ([e es]) (rco-atom e)))
     (define fun-apply (Apply new-f new-es))
     (define tmp (gensym 'tmp))
     (values (Var tmp) (append (append f-ss (append* sss))
                               `((,tmp . ,fun-apply))))]
    ))

(define (make-lets^ bs e)
  (match bs
    [`() e]
    [`((,x . ,e^) . ,bs^)
     (Let x e^ (make-lets^ bs^ e))]))

(define (rco-exp e)
  ;(printf "exp is =======  ~a \n" e)
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
    [(HasType e^ type)
     (HasType (rco-exp e^) type)]
    [(Void) (Void)]
    [(Allocate amount type) e]
    [(FunRef label n)
     (FunRef label n)]
    [(Apply f es)
     (define-values (new-f f-ss) (rco-atom f))
     (define-values (new-es sss) (for/lists (ls1 ls2) ([e es])
                                   (rco-atom e)))
     (make-lets (append f-ss (append* sss))
                (Apply new-f new-es))]
    ))


(define (rco-def d)
  (match d
    [(Def f params ty info e)
     (Def f params ty info (rco-exp e))]))

;; Recall that an atomic expression ends up as an immediate argument of an x86 instruction.

;(define/override (roc-atom e)
;  (match e
;    [(FunRef f n)
;     (define tmp (gensym 'tmp))
;     (values (Var tmp) `((,tmp . ,(FunRef f n))))]
;    [(Apply f es)
;     (define-values (new-f f-ss) (rco-atom f))
;     (define-values (new-es sss) (for/lists (ls1 ls2) ([e es]) (rco-atom e)))
;     (define fun-apply (Apply new-f new-es))
;     (define tmp (gensym 'tmp))
;     (values (Var tmp) (append (append f-ss (append* sss))
;                               `((,tmp . ,fun-apply))))]
;    [else
;     (super rco-atom e)]))
;
;(define/override (rco-exp e)
;  (match e
;    [(FunRef label n)
;     (FunRef label n)]
;    [(Apply f es)
;     (define-values (new-f f-ss) (rco-atom f))
;     (define-values (new-es sss) (for/lists (ls1 ls2) ([e es])
;                                   (rco-atom e)))
;     (make-lets (append f-ss (append* sss))
;                (Apply new-f new-es))]
;    [else
;     (super rco-exp e)]))
;
;(define/override (rco-pred e)
;  (match e
;    [(Apply f es)
;     (define-values (new-f ss) (rco-atom f))
;     (define-values (new-es sss)
;       (for/lists (l1 l2) ([e es]) (rco-atom e)))
;     (make-lets (append ss (append* sss))
;                (Apply new-f new-es))]
;    [else
;     (super rco-pred e)]))
;
;(define/public (rco-def d)
;  (match d
;    [(Def f params ty info e)
;     (Def f params ty info (rco-exp e))]))
;
;(define/override (remove-conplex-opera* e)
;  (match e
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds]) (rco-def d)))]))

(remove-complex-opera*
(expose-allocation
(limit-functions
(uniquify
(shrink
(ProgramDefsExp
 '()
 (list
  (Def
   'map
   '((f : (Integer -> Integer))
     (v1 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v2 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v3 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v4 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v5 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v6 : (Vector Integer Integer Integer Integer Integer Integer Integer))
     (v7 : (Vector Integer Integer Integer Integer Integer Integer Integer)))
   '(Vector Integer Integer Integer Integer Integer Integer Integer)
   '()
   (HasType
    (Prim
     'vector
     (list
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v1) (Int 0)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v2) (Int 1)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v3) (Int 2)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v4) (Int 3)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v5) (Int 4)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v6) (Int 5)))))
      (Apply (Var 'f) (list (Prim 'vector-ref (list (Var 'v7) (Int 6)))))))
    '(Vector Integer Integer Integer Integer Integer Integer Integer)))
  (Def 'inc '((x : Integer)) 'Integer '() (Prim '+ (list (Var 'x) (Int 1)))))
 (Prim
  'vector-ref
  (list
   (Apply
    (Var 'map)
    (list
     (Var 'inc)
     (HasType
      (Prim
       'vector
       (list (Int 1) (Int 2) (Int 3) (Int 4) (Int 5) (Int 6) (Int 7)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list (Int 11) (Int 22) (Int 33) (Int 44) (Int 55) (Int 66) (Int 77)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111)
        (Int 222)
        (Int 333)
        (Int 444)
        (Int 555)
        (Int 666)
        (Int 777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111)
        (Int 2222)
        (Int 3333)
        (Int 4444)
        (Int 5555)
        (Int 6666)
        (Int 7777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111)
        (Int 22222)
        (Int 33333)
        (Int 44444)
        (Int 55555)
        (Int 66666)
        (Int 77777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 111111)
        (Int 222222)
        (Int 333333)
        (Int 444444)
        (Int 555555)
        (Int 666666)
        (Int 777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 1111111)
        (Int 2222222)
        (Int 3333333)
        (Int 4444444)
        (Int 5555555)
        (Int 6666666)
        (Int 7777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))
     (HasType
      (Prim
       'vector
       (list
        (Int 11111111)
        (Int 22222222)
        (Int 33333333)
        (Int 44444444)
        (Int 55555555)
        (Int 66666666)
        (Int 77777777)))
      '(Vector Integer Integer Integer Integer Integer Integer Integer))))
   (Int 5)))))))))


;; ------------------------------------------------------------------------
;; explicate-control


;; block块列表
(define basic-blocks '())
;; 添加block块
(define (create-block tail)
  (match tail
    [(Goto label) (Goto label)]
    [else
     (let ([label (gensym 'block)])
       (set! basic-blocks (cons (cons label tail) basic-blocks))
       (Goto label))]))

#;(define (create-block tail)
  (delay
    ;; 获取真正的值
    (define t (force tail))
    (match t
      [(Goto label) t]
      [else
       (let ([label (gensym 'block)])
         (set! basic-blocks (cons (cons label tail) basic-blocks))
         (Goto label))])))
    

(define Explicate-CFG '())
;; 添加block块
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
       (values cnd-tail (append vars1 vars2 vars3))))]
    ;[(HasType e type)
    ; ...]
    ;[(GlobalValue ...)]
    ;[(Collect ...)]
    [(Apply f arg*)
     (values (TailCall f arg*) '())]
    ))

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
       (values cnd-tail (append vars3 vars1 vars2)))]
    [(Apply f arg*)
     (values (Seq (Assign (Var var) (Call f arg*)) tail) '())]
    ))

;; 返回的是values
;(define (explicate-pred e tail1 tail2)
;  (match e
;    [(Bool bool) (if bool (values tail1 '()) (values tail2 '()))]
;    [(Var v)
;     (define label1 (add-to-cfg tail1))
;     (define label2 (add-to-cfg tail2))
;     (values (IfStmt (Prim 'eq? (list (Var v) (Bool #t))) 
;                     (Goto label1) (Goto label2)) 
;             '())]
;    [(Prim rator (list exp1 exp2))
;     (define label1 (add-to-cfg tail1))
;     (define label2 (add-to-cfg tail2))
;     (define atm1 (gensym "rator-1-"))
;     (define atm2 (gensym "rator-2-"))
;     (let*-values ([(atm2-tail vars2) (explicate-assign exp2 atm2 (IfStmt (Prim rator (list (Var atm1) (Var atm2))) (Goto label1) (Goto label2)))]
;                    [(atm1-tail vars1) (explicate-assign exp1 atm1 atm2-tail)])
;        (values atm1-tail (cons atm1 (cons atm2 (append vars1 vars2)))))]
;    [(Prim 'not (list exp))
;     (define label1 (add-to-cfg tail1))
;     (define label2 (add-to-cfg tail2))
;     (values (IfStmt (Prim 'eq? (list exp (Bool #t))) (Goto label2) (Goto label1)) '())]
;    [(Let var exp body)
;      (define label1 (add-to-cfg tail1))
;      (define label2 (add-to-cfg tail2))
;      (define t (gensym "let-ec-"))
;      (let*-values ([(body-tail vars1) (explicate-assign body t (IfStmt (Prim 'eq? (list (Var t) (Bool #t))) (Goto label1) (Goto label2)))]
;                    [(exp-tail vars2) (explicate-assign exp var body-tail)])
;        (values exp-tail (cons t (cons var (append vars1 vars2)))))]
;    [(If cnd thn els)
;     (define label1 (add-to-cfg tail1))
;     (define label2 (add-to-cfg tail2))
;     (let*-values ([(thn-block vars2) (explicate-pred thn (Goto label1) (Goto label2))]
;                   [(els-block vars3) (explicate-pred els (Goto label1) (Goto label2))]
;                   [(thn-label) (add-to-cfg thn-block)]
;                   [(els-label) (add-to-cfg els-block)]
;                   [(result vars) (explicate-pred cnd (Goto thn-label) (Goto els-label))]
;                   )
;       (values result (append vars vars2 vars3)))]
;    ))


;; 这个和上面的有什么区别，返回的是单个值
(define (explicate-pred cnd thn-block els-block)
  (match cnd
    [(Apply f arg*)
;     (if (f arg*)
;         xxx
;         yyy)
     (define tmp (gensym 'tmp))
     (Seq (Assign (Var tmp) (Call f arg*))
          (IfStmt (Prim 'eq? (list (Var tmp) #t))
                  (create-block thn-block)
                  (create-block els-block)))]
    [(Var x)
     (generic-explicate-pred cnd thn-block els-block)]
    [(Bool #t)
     (create-block thn-block)]
    [(Bool #f)
     (create-block els-block)]
    [(Prim 'not (list e))
     (explicate-pred e els-block thn-block)]
    [(Prim op arg*)
     #:when (set-member? (comparison-ops) op)
     (IfStmt (Prim op arg*)
             (create-block thn-block)
             (create-block els-block))]
    [(Let x rhs body)
;     (if (let ([x rhs])
;           body)
;         xxx
;         yyy)
     (define body-block (explicate-pred body thn-block els-block))
     (explicate-assign rhs x body-block)]
    [(If cnd thn els)
;     (if (if cnd
;             thn
;             els)
;         xxx
;         yyy)
     ;; 要生成4个block
     ;; 这个是continuation,需要翻过来,所以先计算外面的,再计算里面的,然后把外面的放到里面,里面的放到外面
     (define thn-goto (create-block thn-block))
     (define els-goto (create-block els-block))
     (define new-thn (explicate-pred thn thn-goto els-goto))
     (define new-els (explicate-pred els thn-goto els-goto))
     (explicate-pred cnd new-thn new-els)]
    [else (error "explicate pred error")]))


(define (generic-explicate-pred cnd thn-block els-block)
  (IfStmt (Prim 'eq? (list cnd (Bool #t)))
          (create-block thn-block)
          (create-block els-block)))

(define (explicate-control-def d)
  (match d
    [(Def f params ty info body)
     (set! basic-blocks '())
     (define b-block (explicate-tail body))
     (define new-CFG (dict-set basic-blocks (symbol-append f 'start) ;;如果原来的symbol为'aaa,那么现在就变成了'aaastart
                               b-block))
     (Def f params ty info new-CFG)]))

;; 添加副作用 position
;(define (explicate-effect e tail)
;  (match e
;    [(WhileLoop cnd body)
;     (define loop
;     (Goto 


;; 参考Ctup
;; 新添加的stmt变成Seq中的一部分
;; 新添加的exp变成Assign中的一部分
;(define (explicate-control p)
;  (set! Explicate-CFG '())
;  (match p
;    [(Program info e)
;     (let-values ([(tail vars) (explicate-tail e)])
;       (CProgram
;        (cons (cons 'locals vars) info)
;        (cons (cons 'start tail) Explicate-CFG)))]
;    ))


(define (explicate-control p)
  (match p
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (explicate-control-def d)))
     (ProgramDefs info new-ds)]))


;; conditional.rkt
(define (arg? e)
  (match e
    [(or (Var _) (Int _) (Bool _))
     #t]
    [else #f]))

;; add-node 和 block->goto 共同构成了现在的create-block
;(define/public (add-node block)
;  (let ([label (gensym 'block)])
;    (set! control-flow-graph (cons (cons label block)
;                                   control-flow-graph))
;    ;; dictify this
;    label))

;(define/public (block->goto block)
;  (delay
;    (define b (force block))
;    (match b
;      [(Goto label) (Goto label)]
;      [else (Goto (add-node b))])))

;(define/override (basic-exp? e)
;  (match e
;    [(Bool b) #t]
;    [else (super basic-exp? e)]))
;
;(define/override (explicate-tail e)
;  (copious "explicate-tail" e)
;  (match e
;    [(If cnd thn els)
;     (explicate-pred cnd (explicate-tail thn) (explicate-tail els))]
;    [else (super explicate-tail e)]))
;
;;; explicate-assign: exp -> var -> tail -> tail
;;; side effect: adds nodes to the CFG
;(define/override (explicate-assign e x cont-block)
;  (match e
;    [(If cnd thn els)
;     (define cont (block->goto cont-block))
;     (explicate-pred cnd (explicate-assign thn x cont)
;                     (explicate-assign els x cont))]
;    [else (super explicate-assign e x cont-block)]))

;; precondition: cnd is atomic
;; 对cnd是t的特殊情况进行处理
;(define/public (generic-explicate-pred cnd thn-block els-block)
;  (IfStmt (Prim 'eq? (list cnd (Bool #t)))
;          (force (block->goto thn-block))
;          (force (block->goto els-block))))

;; (force (create-block thn-block))
;; (force (create-block els-block))

;;;48.32分
;;; explicate-pred: exp * tail * tail -> tail
;;; side effect: adds nodes to the CFG
;;; 问题：什么时候加delay，什么时候不加delay
;(define/public (explicate-pred cnd thn-block els-block)
;  (match cnd
;    [(Var x)
;     (delay (generic-explicate-pred cnd thn-block els-block))]
;    [(Bool #t)
;     thn-block]
;    [(Bool #f)
;     els-blcok]
;    [(Prim 'not (list e))
;     (explicate-pred e els-block thn-block)]
;    [(Prim op arg*)
;     #:when (set-member? (comparison-ops) op)
;     (delay (IfStmt (Prim op arg*)
;                    (force (block->goto thn-block))
;                    (force (block->goto els-block))))]
;    [(Lex x rhs body)
;     (define body-block (explicate-pred body thn-block els-block))
;     (explicate-assign rhs x body-block)]
;    [(If cnd thn els)
;     (define thn-goto (block->goto thn-block))
;     (define els-goto (block->goto els-block))
;     (define new-thn (explicate-pred thn thn-goto els-goto))
;     (define new-els (explicate-pred els thn-goto els-goto))
;     (explicate-pred cnd new-thn new-els)]
;    [else
;     (error "error" cnd)]))
;
;(define/override (explicate-control p)
;  (match p
;    [(Program info body)
;     (set! control-flow-graph '())
;     (define body-block (force (explicate-tail body)))
;     (Program info (CFG (dict-set control-flow-graph 'start body-block)))]))


;; Lint.rkt

;;  (delay (Return e))]
;; [(Let x rhs body)
;;  (explicate-assign ths x (explicate-tail body))]
;; [else (error "error" e)]))

;(define/public (explicate-assign e x cont-block)
;  (match e
;    [(? basic-exp?)
;     (delay (Seq (Assign (Var x) e) (force cont-block)))]
;    [(Let y rhs body)
;     (define new-body (explicate-assign body x cont-block))
;     (explicate-assign rhs y new-body)]
;    [else (error "error" e)]))
;
;(define/public (explicate-control p)
;  (match p
;    [(Program info body)
;     (define new-body (force (explicate-tail body))) ;; 真正使用的时候添加force
;     (Program info (CFG (list (cons 'start new-body))))]))


;; functions.rkt   
;(define/override (basic-exp? e)
;  (match e
;    [(FunRef label n) #t]
;    [else (super basic-exp? e)]))
;
;(define/public (basic-exp? e)
;  (match e
;    [(or (Var _) (Int _)) #t]
;    [(Prim op arg*) #t]
;    [else #f]))

;(define/override (explicate-assign e x cont-block)
;  (match e
;    [(Apply f arg*)
;     (delay (Seq (Assign (Var x) (Call f arg*))
;                 (force cont-block)))]
;    [else
;     (super explicate-assign e x cont-block)]))
;
;(define/public (explicate-assign e x cont-block)
;  (match e
;    [(? basic-exp?)
;     (delay (Seq (Assign (Var x) e) (force cont-block)))
;     [(Let y rhs body)
;      (define new-body (explicate-assign body x cont-block))
;      (explicate-assign rhs y new-body)]
;     [else
;      (error "error " e)]]))

;(define/override (explicate-tail e)
;  (match e
;    [(Apply f arg*)
;     (delay (TailCall f arg*))]
;    [else
;     (super explicate-tail e)]))
;
;(define/public (explicate-tail e)
;  (match e
;    [(? basic-exp?)
;     (delay (Return e))]
;    [(Let x rhs body)
;     (explicate-assign rhs x (explicate-tail body))]
;    [else
;     (error "explicate-tail error" e)]))

;(if (f a b ...)
;    xxx
;    yyy)
;=>
;tmp = (f arg*)
;if tmp
;   xxx
;   yyy
;(define/override (explicate-pred cnd thn-block els-block)
;  (match cnd
;    [(Apply f arg*)
;     (define tmp (gensym 'tmp))
;     (delay (Seq (Assign (Var tmp) (Call f arg*))
;                 (IfStmt (Prim 'eq? (list (Var tmp) (Bool #t)))
;                         (force (block->goto thn-block)) ;; (force (create-block thn-block))
;                         (force (block->goto els-block)))))]
;    [else
;     (super explicate-pred cnd thn-block els-block)]))

;(define/public (explicate-control-def d)
;  (match d
;    [(Def f params ty info body)
;     (set! control-flow-graph '())
;     (define body-block (force (explicate-tail body)))
;     (define new-CFG (dict-set control-flow-graph (symbol-append f 'start) ;;如果原来的symbol为'aaa，那么现在就变成了'aaastart
;                               body-block))
;     (Def f params ty info new-CFG)]))

;(define/override (explicate-control p)
;  (match p
;    [(ProgramDefs info ds)
;     (define new-ds (for/list ([d ds]) (explicate-control-def d)))
;     (ProgramDefs info new-ds)]))

(define symbol-append
  (lambda (s1 s2)
    (string->symbol (string-append (symbol->string s1) s2))))

(define comparison-ops
  (lambda ()
    (set '< '<= '.....)))
    
  

;; explicate-control
;; delay force在什么地方使用
;; 创建的时候delay，使用的时候force


;;------------------------------------------------------------------------
;; uncover-locals

(define (uncover-block tail)
  (match tail
    [(Seq (Assign var (HasType x type)) t)
     (cons `(,var . ,type) (uncover-block t))]
    [x '()]))

(define (uncover-locals p)
  (match p
    [(Program info B-list)
     (let ([locals (remove-duplicates
                     (append-map (lambda (x) 
                                    (uncover-block (cdr x))) B-list))])
       (Program `((locals . ,locals)) B-list))]))

;(remove-duplicates '(a b b a))
;; 先对每个元素进行map，然后对结果进行append
;(append-map vector->list '(#(1) #(2 3) #(4)))

;(Program
; '()
; (Let
;  'v
;  (HasType (Prim 'vector (list (Int 1) (Int 2))) '(Vector Integer Integer))
;  (Int 42)))

;;--------------------------------------------------------------

(define (analyze-dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref mapping node)))
                (dict-set! mapping node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)

;;------------------------------------
;; Optimize Jumps

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
      ;(printf "short cuts is ~a \n" short-cuts)
      (define not-short-cut (filter (lambda (b) (or (not (is-trivial? (cdr b)))
                                                    (equal? (car b) 'start))) blocks))
      ;(printf "not short cut is ~a \n" not-short-cut)
      (define patched (patch-gotos short-cuts not-short-cut))
      ;(printf "patched is ~a \n" patched)
      (define ref-graph (block-list->racketgraph patched))
      ;(printf "edges is ~a \n" (get-edges ref-graph))
      ;; what is the effect of this step?
      (define has-neighbors (filter (lambda (b) (or (has-vertex? ref-graph (car b))
                                                    (equal? (car b) 'start))) patched))
      ;(printf "has-neighbors is ~a \n" has-neighbors)
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

;;------------------------------------
;; select instructions
;; 52

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

;; We then initialize the tag and finally copy the address in r11 to the left-hand side
;; 结果为分配地址的首地址


;; load-effectiveaddress
;; instruction-pointer-relative addressing
;; That is, the arguments are passed in registers. We recommend turning the parameters into local variables


;; Lfun.rkt
;; 52.30
(define/override (select-instr-tail t)
  (match t
    [(TailCall f es)
     (unless (<= (length es) (vector-length arg-registers))
       (error "error arg params"))
     (define new-f (select-instr-arg f))
     (define new-es (for/list ([e es]) (select-instr-arg e)))
     (append (for/list ([arg new-es] [r arg-registers])
               (Instr 'movq (list arg (Reg r))))
             (list (TailJmp new-f (length es))))] ;; TailJmp包含参数个数
    [(Retrun e)
     (define ret-label (symbol-append (function-name) 'conclusion))
     (append (select-instr-stmt (Assign (Reg 'rax) e))
             (list (Jmp ret-label)))]
    [else
     (super select-instr-tail t)]))

(define/override (select-instr-stmt e)
  (verbose "select-instr-stmt" e)
  (match e
    [(Assign lhs (FunRef f n))
     (define new-lhs (select-instr-arg lhs))
     (list (Instr 'leaq (list (FunRef f n) new-lhs)))]
    [(Assign lhs (Call f es))
     (unless (<= (length es) (vector-length arg-registers))
       (error "select-instr-stmt: more arguments than arg-registers"))
     (define new-lhs (select-instr-arg lhs))
     (define new-f (select-instr-arg f))
     (define new-es (for/list ([e es]) (select-instr-arg e)))
     (append (for/list ([arg new-es] [r arg-registers])
               (Instr 'movq (list arg (Reg r))))
             (list (IndirectCallq new-f (length es))
                   (Instr 'movq (list (Reg 'rax) new-lhs))))]
    [else
     (super select-instr-stmt e)]))

;; https://beautifulracket.com/explainer/parameters.html

;> (define h #hash((a . "apple") (b . "banana")))
;> (for/list ([(k v) (in-dict h)])
;    (format "~a = ~s" k v))
;'("b = \"banana\"" "a = \"apple\"")

(define/public (select-instr-def d)
  (match d
    [(Def f (list `[,xs : ,ps] ...) rt info CFG) ;; CFG为block块
     (unless (<= (length xs) (vector-length arg-registers))
       (error "def error"))
     (define new-CFG
       (parameterize ([function-name f])
         (for/list ([(label tail) (in-dict CFG)])
           (cons label (Block '() (select-instr-tail tail))))))
     (define param-moves
       (for/list ([param xs] [r arg-registers])
         (Instr 'movq (list (Reg r) (Var param)))))
     (define start-label (symbol-append f 'start))
     (define new-start
       (match (dict-ref new-CFG start-label)
         [(Block info ss)
          (Block info (append param-moves ss))]
         [else
          (error "select instr def error")]))
     (define newer-CFG (dict-set new-CFG start-label new-start))
     (define new-info
       (dict-set-all
        info ;; parameters become locals
        `((locals-types . ,(append (map cons xs ps)
                                   (dict-ref info 'locals-types)))
          (num-params . ,(length xs)))))
     (Def f '() 'Integer new-info newer-CFG)]
    [else
     (error "select instr def " d)]))

(define/override (select-instructions e)
  (match e
    [(ProgramDefs info ds)
     (define new-ds (for/list ([d ds]) (select-instr-def d)))
     (ProgramDefs info new-ds)]
    [else
     (super select-instructions e)]))
     

;;==============================================================
;; live --- interference --- color
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


;; Lfun.rkt
;; 5757
;(define/override (free-vars a)
;  (match a
;    [(FunRef f n) (FunRef f n)]
;    [else
;     (super free-vars a)]))
;
;(define/override (read-vars instr)
;  (match instr
;    [(Instr 'leaq (list s d))
;     (free-vars s)]
;    [(IndirectCallq arg n)
;     (set-union (free-vars arg)
;                (vector->set (vector-take arg-registers n)))]
;    [(TailJmp arg n)
;     (set-union (free-vars arg)
;                (vector->set (vector-take arg-registers n)))]
;    [else
;     (super read-vars instr)]))
;
;(define/override (write-vars instr)
;  (match instr
;    [(IndirectCallq f n)
;     (caller-save-for-alloc)]
;    [(TailJmp f n)
;     (caller-save-for-alloc)]
;    [(Instr 'leaq (list s d))
;     (free-vars d)]
;    [else
;     (super write-vars instr)]))
;
;(define/public (uncover-live-def ast)
;  (match ast
;    [(Def f '() rt info CFG)
;     (Def f '() rt info (uncover-live-CFG CFG))]))
;
;(define/override (uncover-live ast)
;  (match ast
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds]) (uncover-live-def d)))]
;    [else
;     (error "uncover live error")]))


;;======================================================================
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


;; Lfun.rkt
;; 1.07.57

;(define/override (build-interference-instr live-after G loc-types)
;  (lambda (ast)
;    (match ast
;      [(Callq f _)
;       ;; The function might  call collect.
;       (for ([v live-after])
;         (cond
;           [(and (not (set-member? registers v))
;                 (root-type? (dict-ref loc-types v)))
;            (for ([u (callee-save-for-alloc)])
;              (add-edge! G u v))]))
;       ((super build-interference-instr live-after G loc-types) ast)]
;      [(IndirectCallq arg _)
;       ;; the function might all collect
;       (for ([v live-after])
;         (cond
;           [(and (not (set-member? registers v))
;                 (root-type? (dict-ref loc-types v)))
;            (for ([u (callee-save-for-alloc)])
;              (add-edge! G u v))]))
;       ((super build-interference-instr live-after G loc-types) ast)]
;      [else
;       ((super build-interference-instr live-after G loc-types) ast)])))
;
;(define/public (build-interference-def d)
;  (match d
;    [(Def f '() rt info CFG)
;     (define loc-types (lookup 'locals-types info))
;     (define IG (undirected-graph '()))
;     (for ([v (dict-keys loc-types)])
;       (add-vertex! IG v))
;     (define new-CFG
;       (for/list ([(label block) (in-dict CFG)])
;         (cons label ((build-interference-block IG loc-types) block))))
;     (print-dot IG (format "./~s-interference.dot" f))
;     (define new-info (dict-set info 'conflicts IG))
;     (Def f '() rt new-info new-CFG)]
;    [else
;     (error "" d)]))
;
;(define/override (build-interference ast)
;  (match ast
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds])
;                         (build-interference-def d)))]
;    [else
;     (error "")]))


;;====================================================
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


;;Lfun.rkt
;(define/public (build-move-graph-def d)
;  (match d
;    [(Def f '() rt info CFG)
;     (define MG (undirected-graph '()))
;     (for ([v (dict-keys (dict-ref info 'locals-types))])
;       (add-vertex! MG v))
;     (define new-CFG
;       (for/list ([(label block) (in-dict CFG)])
;         (cons label (build-move-block block MG))))
;     (print-dot MG (format "./~s-move.dot" f))
;     (define new-info (dict-set info 'move-graph MG))
;     (Def f '() rt new-info new-CFG)]))
;
;(define/override (build-move-graph ast)
;  (match ast
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds]) (build-move-graph-def d)))]
;    [else
;     (error "error" ast)])) 
     
;;---------------------------------------------------------
;; assign homes

;(define/override (instructions)
;  (set-union (super instructions)
;             (set 'leaq)))
;
;(define/override (assign-homes-imm homes)
;  (lambda (e)
;    (match e
;      [(FunRef f n)
;       (FunRef f n)]
;      [else
;       ((super assign-homes-imm homes) e)])))
;
;(define/override (assign-homes-instr homes)
;  (lambda (e)
;    (match e
;      [(IndirectCallq f n)
;       (IndirectCallq ((assign-homes-imm homes) f) n)]
;      [(TailJmp f n)
;       (TailJmp ((assign-homes-imm homes) f) n)]
;      [else
;       ((super assign-homes-instr homes) e)])))


;; =======================================================
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


;; tuple 寄存器分配
;(define (assign-nat n type)
;  (let [(last-reg (sub1 (length reg-colors)))]
;    (cond [(<= n last-reg)
;           (Reg (rev-match-alist n reg-colors))]
;          [(list? type) ;; vector-type?
;           (Deref 'r15 (* 8 (add1 (- n last-reg))))]
;          [else
;           (Deref 'rbp (* (add1 (- n last-reg)) (- 8)))]
;          )))
;
;(define (generate-assignments locals colors)
;  (cond [(empty? locals) '()]
;        [else (match (car locals)
;                [`(,(Var v) . ,type)
;                 (cons `(,v . ,(assign-nat (match-alist v colors) type)) 
;                       (generate-assignments (cdr locals) colors))])]))


;; register-allocate.rkt
;; 1.11.40  

;(define/public (used-callee-reg locals color)
;  (for/set ([x locals] #:when (callee-color? (hash-ref color x)))
;    (color->register (hash-ref color x))))
;
;(define/public (num-used-callee locals color)
;  (set-count (used-callee-reg locals color)))
;
;(define/public (allocate-registers ast)
;  (match ast
;    [(Program info (CFG G))
;     (define locals (dict-keys (dict-ref info 'locals-types)))
;     (define IG (dict-ref info 'conflicts))
;     (define MG (dict-ref info 'move-graph))
;     (define-values (color num-spills) (color-graph IG MG info))
;     (define homes
;       (for/hash ([x locals])
;         (define home (identify-home (num-used-callee locals color)
;                                     (hash-ref color x)))
;         ...))]))

;; Lfun.rkt
;; 1.14.31

;(define/public (allocate-registers-def d)
;  (match d
;    [(Def f '() rt info CFG)
;     (define locals (dict-keys (dict-ref info 'locals-types)))
;     ...]))


;; ------------------------------------------------------------------

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
                              ;; 将指令组合在一起
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



;; Lfun.rkt
;(define/public (remove-jumps-def ast)
;  (match ast
;    [(Def f '() rt info CFG)
;     (Def f '() rt info (remove-jumps-CFG f CFG))]))
;
;(define/override (remove-jumps ast)
;  (match ast
;    [(ProgramDefs info ds)
;     (ProgramDefs info (for/list ([d ds]) (remove-jumps-def d)))]
;    [else
;     (error "")]))
  



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


;;-----------------

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


;;--------------------------------------------------------------------

;(define (make-main stack-size used-regs root-spills)
;  (let* ([extra-pushes (filter (lambda (reg)
;                                (match reg
;                                  [(Reg x) (index-of callee-registers x)]
;                                  [x false]))
;                              used-regs)]
;         [push-bytes (* 8 (length extra-pushes))]
;         [stack-adjust (- (round-stack-to-16 (+ push-bytes stack-size)) push-bytes)])
;    (Block '()
;      (append (list (Instr 'pushq (list (Reg 'rbp)))
;                    (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
;              (map (lambda (x) (Instr 'pushq (list x))) extra-pushes) 
;              (list (Instr 'subq (list (Imm stack-adjust) (Reg 'rsp)))) 
;              (initialize-garbage-collector root-spills)
;              (list (Jmp 'start))))))
;
;(define (initialize-garbage-collector root-spills)
;  (list (Instr 'movq (list (Imm root-stack-size) (Reg 'rdi)))
;        (Instr 'movq (list (Imm heap-size) (Reg 'rsi)))
;        (Callq 'initialize)
;        (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))
;        (Instr 'movq (list (Imm 0) (Deref (Reg 'r15) 0))
;        ...
;        (Instr 'movq (list (Imm 0) (Deref (Reg 'r15) k))
;        (Instr 'addq (list (Imm root-spills) (Reg 'r15)))))))


;-----------------------------------------------------------------------        

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
     ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
     ("reveal-functions" ,reveal-functions ,interp-Lfun ,type-check-Lfun)
     ("limit-functions" ,limit-functions ,interp-Lfun ,type-check-Lfun)
     ("expose-allocation" ,expose-allocation ,interp-Lfun ,type-check-Lfun)
     ;; Uncomment the following passes as you finish them.
     ;;("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
     ;;("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
     ;;("optimize jumps" ,optimize-jumps ,interp-Cif ,type-check-Cif)
     ;;("instruction selection" ,select-instructions ,interp-x86-1)
     ;;("assign homes" ,assign-homes ,interp-x86-0)
     ;;("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

;; Lstructe
;; function-call syntax

;(let ([A (make-vector 2 2)])
;  (let ([B (make-vector 2 3)])
;    (let ([i 0])
;      (let ([prod 0])
;        (begin
;          (while (< i n)
;                 (begin
;                   (set! prod (+ prod (* (vector-ref A i)
;                                         (vector-ref B i))))
;                   (set! i (+ i 1))))
;          prod)))))


;All the call-live variables are suppose to have edges in the interference graph to the caller-saved registers because we don’t save anything on the caller side leading up to a call. (See page 37.)
;
;So the call-live tuple-typed variables already have interference edges with the caller-saved registers because they are a subset of the call-live variables, i.e., the previous sentence applies to them.
;
;To make sure that the call-live tuple-typed variables get spilled, we need there to be interference edges between them and all the registers. So we add edges to the rest of the registers, i.e., the callee-saved registers.



