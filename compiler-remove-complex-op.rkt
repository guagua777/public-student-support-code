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
(require "utilities.rkt")
(require "interp.rkt")
(require "graph-printing.rkt")
(require "priority_queue.rkt")

(provide (all-defined-out))

;(+ 5 (- 10))
;(- 10) 为 (- atm)
;(+ 5 (- 10)) 为 (+ atm exp)，需要变换为 (+ atm atm) 的形式
;(+ 5 tmp1) 但是不能把(- 10)给丢了，需要将其保存起来，且tmp1代表(- 10)
;变成：
;tmp1 -> (- 10)
;(+ 5 tmp1)

(define remove-complex-op
  (lambda (p)
    (match p
      [(Program info exp)
       (Program info (rco exp))])))

(define rco
  (lambda (exp)
    (match exp
      [(Int n) (Int n)]
      [(Var x) (Var x)]
      [(Let x v body)
       (Let x (rco v) (rco body))]
      [(Prim op args)
       (define-values (v-exps atoms)
         (for/lists (v-es as) ([a args]) (rco-atm a)))
       ;;(make-new-let op v-exps atoms)])))
       (make-new-let op (append* v-exps) atoms)])))
       
       ;;(define m-args (for/list ([a args]) (rco-atm a)))
       ;;(define new-args (for/list ([a m-args])
       ;;                   (cons (append* (car a)) (append* (cdr a)))))
       ;;(make-new-let op new-args)])))

(define rco-atm
  (lambda (e)
    (match e
      [(Int n) (values '() (Int n))]
      [(Var x) (values '() (Var x))]
      [(Let x v body)
       (values '() (Let x (rco v) (rco body)))]
      [(Prim op args);; (op args)： (- 10) => tmp1
       (define-values (v-exps as)
         (for/lists (var-exps atoms) ([a args]) (rco-atm a)))
       ;; v-exps 为list的list
       ;; list-v-exps 为list
       (define list-v-exps (append* v-exps))
       (define tmp (gensym 'tmp))
       (values (append list-v-exps `((,tmp . ,(Prim op as))))
               (Var tmp))])))
       ;;(values (append list-v-exps `((,tmp . ,(Prim op as)))) tmp)])))
       ;;(cons (append (car new-args) (cons tmp (Prim op (cdr new-args)))) tmp)])))

(define make-new-let
  (lambda (op v-exps atoms)
    ;;(printf "v-exps is ~a " v-exps)
    (match v-exps
      [`()
       (Prim op atoms)]
      [;;`((,v . ,exp) . ,v-exps^)
       ;; 匹配list的时候要用cons
       (cons (cons v exp) v-exps^)
      ;;[`((,v . ,exp) ,v-exps^)
       (Let v exp (make-new-let op v-exps^ atoms))])))
;    (cond
;      [(eq? '() v-exps)
;       (Prim op atoms)]
;      [else
;       (Let (car (car v-exps)) (cdr (car v-exps))
;            (make-new-let op (cdr v-exps) atoms))])))

;> (list (cons 1 2) '())
;'((1 . 2) ())
;> (cons (cons 1 2) '())
;'((1 . 2))
         

;(define make-new-let
;  (lambda (op middle-args)
;    (cond
;      [(eq? '() (car middle-args))
;       (Prim op (cdr middle-args))]
;      [else
;       (Let (car (car (car middle-args))) (cdr (car (car middle-args)))
;            (make-new-let op (cons (cdr (car middle-args)) (cdr middle-args))))])))


(remove-complex-op (Program '() (Prim '+ (list (Int 5) (Prim '- (list (Int 6)))))))

(remove-complex-op (Program
 '()
 (Let 'a5079164 (Int 42) (Let 'b5079165 (Var 'a5079164) (Var 'b5079165)))))


(list (cons 'tmp5096417 (Prim '- (list (Int 6)))))

(remove-complex-op
   (Program
 '()
 (Let
  'a5135352
  (Prim
   '+
   (list
    (Int 10)
    (Prim '- (list (Prim '+ (list (Int 12) (Prim '- (list (Int 13)))))))))
  (Prim '+ (list (Prim '- (list (Var 'a5135352))) (Prim '- (list (Int 19))))))))

(Program
 '()
 (Let
  'a5135352
  (Let
   'tmp5138063
   (Prim '- (list (Int 13)))
   (Let
    'tmp5138064
    (Prim '+ (list (Int 12) (Var 'tmp5138063)))
    (Let 'tmp5138065 (Prim '- (list (Var 'tmp5138064))) (Prim '+ (list (Int 10) (Var 'tmp5138065))))))
  (Let
   'tmp5138066
   (Prim '- (list (Var 'a5135352)))
   (Let 'tmp5138067 (Prim '- (list (Int 19))) (Prim '+ (list (Var 'tmp5138066) (Var 'tmp5138067)))))))
                 
       
       


       
       


