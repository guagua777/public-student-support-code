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

;; 1. 每个block的live-before为空集合
;; 2. 在上次live-before的基础上，对每个block分析liveness，得到新的live-before
;; 3. 如果只有某个block的live-before变化了，那么下次只分析该block的前置block
;; 4. 直到最后收敛

;the control-flow graph G,
;a function transfer that applies the analysis to one block,
;and the bottom
;and join operators for the lattice of abstract states.

;; the inputs to the transfer function come from the predecessor nodes in the control-flow graph

;; b5 -> m
;; b7 -> b5
;; b8 -> b5
;; b5 -> b7
;; con -> b8
(define (analyze-dataflow G transfer bottom join)
  (define mapping (make-hash))
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  ;; main -> b5 
  ;; b5 -> b7
  ;; b5 -> b8
  ;; b7 -> b5
  ;; b8 -> conclusion
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         ;; assume node is b5
         (define node (dequeue! worklist))
         ;; The live-after for block5 is the union of the live-before sets for block7 and block8, which is {i, rsp, sum}. 
         (define input (for/fold ([state bottom])
                                 ;; pred is b7 and b8
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref mapping pred))))
         ;; So the liveness analysis for block5 computes {i, rsp, sum}. 
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref mapping node)))
                ;; update mapping
                (dict-set! mapping node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)
