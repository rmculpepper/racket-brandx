#lang racket/base
(require racket/contract
         racket/match
         racket/math
         syntax/macro-testing
         brandx
         rackunit)

(define-syntax-rule (convert-syntax-error/body body ...)
  (convert-syntax-error
   (let () body ... (void))))

;; ----------------------------------------
;; syntax errors

(check-exn
 #rx"duplicate member name"
 (lambda ()
   (convert-syntax-error/body
    (define-interface I (a a)))))

(check-exn
 #rx"duplicate member name"
 (lambda ()
   (convert-syntax-error/body
    (define-signature I (a a)))))

(check-exn
 #rx"duplicate member name"
 (lambda ()
   (convert-syntax-error/body
    (define-interface I (a))
    (define-interface J #:super (I) (a)))))

(check-exn
 #rx"expected name defined as interface"
 (lambda ()
   (convert-syntax-error/body
    (define-signature S (a))
    (define-interface I #:super (S) (b)))))

(check-exn
 #rx"unexpected key in fallbacks"
 (lambda ()
   (convert-syntax-error/body
    (define-interface I (x)
      #:fallbacks (hasheq 'y void)))))

(check-exn
 #rx"not a member name"
 (lambda ()
   (convert-syntax-error/body
    (define-signature S
      (a [b #:dep (xyz) any/c])))))

(check-exn
 #rx"duplicate identifier in dependency list"
 (lambda ()
   (convert-syntax-error/body
    (define-signature S
      (a [b #:dep (a a) any/c])))))

(define-signature S1 (a b))
(define-interface I1 (f g) #:generics-prefix $)

(check-exn
 #rx"not allowed with signature"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([S1 #:except (a)])
     (define b 2)))))

(check-exn
 #rx"name is not member of interface"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([I1 #:except (x)])
     (void)))))



;; ----------------------------------------
;; contracts
