#lang racket/base
(require rackunit)

(module aaa racket/base
  (require racket/contract
           brandx)
  (provide (interface-out AE)
           (struct-out num))

  ;; make sure this runs w/o internal "used before initialization"
  ;; error from module-boundary contract machinery
  (define (go)
    (void (ev (num 1))))

  (define-interface AE
    ([ev (-> AE? exact-integer?)]))

  (struct num (x)
    #:properties
    (method-properties
     #:export ([AE #:all #:prefix %])
     (define (%ev self)
       (num-x self))))

  (go))

(module bbb racket/base
  (require brandx
           (submod ".." aaa))
  (provide (struct-out plus))

  (struct plus (a b)
    #:properties
    (method-properties
     #:export ([AE #:all #:prefix %])

     (define (%ev self)
       (+ (ev (plus-a self))
          (ev (plus-b self)))))))

(require 'aaa 'bbb)

(check-equal? (ev (num 1))
              1)

(check-equal? (ev (plus (num 1) (num 2)))
              3)

(check-exn
 #rx"broke its own contract.*blaming: \\([^\n]* aaa\\)"
 (lambda ()
   (ev (plus (num 1) (num 3.14)))))

(check-exn
 #rx"contract violation.*blaming: \\([^\n]* bbb\\)"
 (lambda ()
   (ev (plus (num 1) 6))))
