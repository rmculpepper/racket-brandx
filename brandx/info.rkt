#lang info

;; ========================================
;; pkg info

(define collection "brandx")
(define deps
  '("base" "brandx-lib"))
(define implies
  '("brandx-lib"))
(define build-deps
  '("racket-doc"
    "scribble-lib"))
(define pkg-authors '(ryanc))

;; ========================================
;; collect info

(define name "brandx")
(define scribblings
  '(["brandx.scrbl" ()]))
