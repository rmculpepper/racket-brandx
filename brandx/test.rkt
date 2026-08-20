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
;; errors

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
   (define-interface I (a)
     #:fallbacks (hasheq 'b void))
   (void)))

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

(check-exn
 #rx"incompatible exports; prefixes differ"
 (lambda ()
   (define-interface I2 #:super (I1) (h))
   (convert-syntax-error
    (bundle
     #:export ([I1 #:prefix %]
               [I2 #:prefix &])))))

(check-exn
 #rx"incompatible exports; export exceptions differ"
 (lambda ()
   (define-interface I2 #:super (I1) (h))
   (convert-syntax-error
    (bundle
     #:export (I1 [I2 #:except (g)])))))

(check-exn
 #rx"incompatible import/export.*name collision"
 (lambda ()
   (define-interface I2 (f))
   (convert-syntax-error
    (bundle
     #:export (I1 I2)))))

(check-exn
 #rx"does not match any export"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([I1 #:prefix %])
     (define %f void)
     (define %g void)
     (define %bad void)))))

(check-exn
 #rx"member name is defined but"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([I1 #:except (g)])
     (define f void)
     (define g void)))))

(check-exn
 #rx"required member name is not defined: g"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([I1 #:all])
     (define f void)))))

(check-exn
 #rx"attempt to mutate exported variable"
 (lambda ()
   (convert-syntax-error
    (bundle
     #:export ([I1 #:all])
     (define f void)
     (define g void)
     (void (set! f void))))))

(check-exn
 #rx"import not initialized"
 (lambda ()
   (define/invoke-bundles
     #:bind ()
     (bundle #:import (S1) (void a))
     (bundle #:export (S1) (define a 1) (define b 2)))
   (void)))

(check-exn
 #rx"illegal export with reserved super tag"
 (lambda ()
   (bundle #:export ([I1 #:tag (super)]))))

(check-exn
 #rx"duplicate export"
 (lambda ()
   (define/invoke-bundles
     #:bind ()
     (bundle #:export (I1))
     (bundle #:export (I1)))
   (void)))

(check-exn
 #rx"illegal import of signature with super tag"
 (lambda ()
   (bundle #:import ([S1 #:tag (super)]))))

(check-exn
 #rx"import missing matching export"
 (lambda ()
   (define/invoke-bundles
     #:bind ()
     (bundle #:import (S1)))
   (void)))

(check-exn
 #rx"tagged signature not exported"
 (lambda ()
   (define/invoke-bundles
     #:bind (S1)
     (bundle))
   (void)))

(check-exn
 #rx"bad target for super method"
 (lambda ()
   (define-interface I (f))
   (define xf #f)
   (struct s ()
     #:properties
     (method-properties
      #:export (I)
      (define f void)))
   (struct s2 s ()
     #:properties
     (method-properties
      #:export (I)
      #:import ([I #:super])
      (set! xf super-f)
      (define f void)))
   (xf 'blah)))
