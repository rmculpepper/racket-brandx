#lang racket/base
(require racket/contract
         racket/match
         racket/math
         brandx
         rackunit)

(define-interface can-greet
  ([greet (-> can-greet? string?)]))

(define-interface can-eat
  ([food/c (-> can-eat? contract?)]
   [eat (->i ([self can-eat?] [food (self) (food/c self)])
             [_ void?])]))

(struct dog ([weight #:mutable] [happiness #:mutable])
  #:transparent
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %]
             [can-eat #:all #:prefix %])
   (define-struct-abbrevs dog)
   (define (%greet self) (if (>= (.weight self) 10) "woof" "bark"))
   (define (%food/c self) (or/c 'dog-food 'cheese 'treat))
   (define (%eat self food)
     (case food
       [(treat) (.happiness-set! self (add1 (.happiness self)))]
       [else (.weight-set! self (add1 (.weight self)))]))))

(define barkly (dog 8 5))
(check-equal? (greet barkly)
              "bark")
(eat barkly 'dog-food)
(eat barkly 'cheese)
(eat barkly 'treat)
(check-equal? (greet barkly)
              "woof")
(check-exn #rx"contract violation"
           (lambda ()
             (eat barkly 'lettuce)))

;; ----------------------------------------

(struct loud-dog dog ()
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %])
   #:import ([can-greet #:super])
   (define (%greet self)
     (define greeting (super-greet self))
     (string-append greeting " " greeting " " greeting))))

(define princess (loud-dog 2 1))
(check-equal? (greet princess)
              "bark bark bark")
(eat princess 'treat)

;; ----------------------------------------

(define loud@
  (bundle
   #:export ([can-greet #:all #:prefix %])
   #:import ([can-greet #:super])
   (define (%greet self)
     (define greeting (super-greet self))
     (string-append greeting " " greeting " " greeting))))

(struct cat ()
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %]
             [can-eat #:all #:prefix %])
   (define (%greet self) "meow")
   (define (%food/c self) (or/c 'cat-food 'fish 'bird 'mouse))
   (define (%eat self food) (void))))

(struct loud-cat cat ()
  #:properties
  (method-properties
   #:compound (list loud@)))

(check-equal? (greet (loud-cat))
              "meow meow meow")
