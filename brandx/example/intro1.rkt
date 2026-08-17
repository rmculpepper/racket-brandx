#lang racket/base
(require racket/contract
         racket/match
         racket/math
         brandx
         rackunit)

(define-interface shape
  ([contains? (-> shape? real? real? boolean?)]
   [area (-> shape? (>=/c 0))]))

(struct rectangle (x1 y1 x2 y2) ;; x1 <= x2, y1 <= y2
  #:properties
  (method-properties
   #:export ([shape #:all #:prefix %])

   (define (%area self)
     (match-define (rectangle x1 y1 x2 y2) self)
     (* (- x2 x1) (- y2 y1)))

   (define (%contains? self x y)
     (match-define (rectangle x1 y1 x2 y2) self)
     (and (<= x1 x x2) (<= y1 y y2)))
   ))

(check-equal? (contains? (rectangle 0 0 10 20) 5 12)
              #t)
(check-equal? (area (rectangle 1 2 11 22))
              200)

(check-exn #rx"contract violation"
           (lambda ()
             (contains? (rectangle 0 0 10 20) 0 'center)))

(check-exn #rx"broke its own contract"
           (lambda ()
             (area (rectangle 5 0 0 10))))

;; ----

(struct circle (xc yc r)
  #:properties
  (method-properties
   #:export ([shape #:all #:prefix %])
   (define-struct-abbrevs circle)

   (define (%area self)
     (* pi (sqr (.r self))))

   (define (%contains? self x y)
     (<= (dist-from-center self x y) (.r self)))

   (define (dist-from-center self x y)
     (dist (.xc self) x (.yc self) y))

   (define (dist x1 y1 x2 y2)
     (sqrt (+ (sqr (- x2 x1)) (sqr (- y2 y1)))))
   ))

(check-equal? (contains? (circle 0 0 10) 3 4)
              #t)

(check-equal? (area (circle 0 0 1))
              pi)

;; ----

(struct union (s1 s2)
  #:properties
  (method-properties
   #:export ([shape #:prefix %])

   (define (%contains? self x y)
     (match-define (union s1 s2) self)
     (or (contains? s1 x y) (contains? s2 x y)))
   ))

(check-equal? (shape? (union (circle 0 0 1) (rectangle 0 0 1 1)))
              #t)
(check-equal? (contains? (union (circle 0 0 1) (rectangle 0 0 1 1)) 1/2 1/2)
              #t)

(check-exn #rx"not implemented"
           (lambda ()
             (area (union (circle 0 0 1) (rectangle 0 0 1 1)))))

;; ----

(struct disjoint-union union ()
  ;; sub-shapes must be disjoint; not checked!
  #:properties
  (method-properties
   #:export ([shape #:except (contains?) #:prefix %])
   (define-struct-abbrevs disjoint-union)

   (define (%area self)
     (+ (area (.s1 self)) (area (.s2 self))))
   ))

(check-equal? (contains? (disjoint-union (rectangle 0 0 1 1) (rectangle 1 1 2 2)) 1/2 1/2)
              #t)

(check-equal? (area (disjoint-union (rectangle 0 0 1 1) (rectangle 1 1 2 2)))
              2)
