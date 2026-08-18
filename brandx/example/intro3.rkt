#lang racket/base
(require racket/contract
         racket/match
         racket/math
         brandx
         rackunit)

(define-signature worklist
  ([worklist/c contract?]
   [empty #:dep (worklist/c) worklist/c]
   [empty? #:dep (worklist/c) (-> worklist/c boolean?)]
   [enqueue #:dep (worklist/c) (-> worklist/c any/c worklist/c)]
   [dequeue #:dep (worklist/c) (-> worklist/c (values any/c worklist/c))]))

(define stack@
  (bundle
   #:export ([worklist #:prefix %])
   (define %worklist/c list?)
   (define %empty null)
   (define %empty? null?)
   (define (%enqueue st v) (cons v st))
   (define (%dequeue st)
     (match st [(cons v st) (values v st)]))))

;; ----------------------------------------

(define-signature traversal
  ([traverse (-> any/c (-> any/c (listof any/c)) (listof any/c))]))

(define traversal@
  (bundle
   #:export ([traversal #:prefix %])
   #:import (worklist)

   (define (%traverse v get-next)
     (define q (enqueue empty v))
     (let loop ([q q])
       (cond [(empty? q)
              null]
             [else
              (define-values (v q2) (dequeue q))
              (define q3 (enqueue-all q2 (get-next v)))
              (cons v (loop q3))])))

   ;; TODO: turn into aux bundle, but problem: how to contract?
   (define (enqueue-all q xs)
     (for/fold ([q q]) ([x (in-list xs)]) (enqueue q x)))
   ))

;; ----------------------------------------

(define (halfsies n)
  (define half (quotient n 2))
  (cond [(<= n 1) null]
        [(even? n) (list half)]
        [else (list half (add1 half))]))

(define/invoke-bundles #:bind ([traversal #:prefix dfs:]) stack@ traversal@)

(check-pred list? (dfs:traverse 100 halfsies))

;; ----------------------------------------

(define queue@
  (bundle
   #:export ([worklist #:prefix %])
   (struct queue (r w))
   (define %worklist/c queue?)
   (define %empty (queue null null))
   (define (%empty? q)
     (match q [(queue '() '()) #t] [_ #f]))
   (define (%enqueue q v)
     (match q
       [(queue r w) (queue r (cons v w))]))
   (define (%dequeue q)
     (match q
       [(queue '() '()) (error 'remove "empty queue")]
       [(queue (cons v r) w) (values v (queue r w))]
       [(queue '() w) (%dequeue (queue (reverse w) '()))]))))

(define/invoke-bundles #:bind ([traversal #:prefix bfs:]) queue@ traversal@)

(check-pred list? (bfs:traverse 100 halfsies))
