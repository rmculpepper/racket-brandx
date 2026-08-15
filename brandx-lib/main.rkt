;; Copyright 2026 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

;; Restrictions and limitations:
;; - dispatch on first positional argument
;; - sub-interface cannot "override" super-interface methods
;; - `augment` methods not supported, since call not tied to `this`
;; - interface contracts cannot refer to interface members

;; TODO:
;; - no-generics implies no prop
;; - drop #:dynamic-public, pubnames
;; - add ordering constraints, eg import with #:prereq
;; - add inspector, add reflective operations
;;   - util to check no unimplemented methods (except given list)
;; - make impl/c collapsible?
;; - add option to disable internal (import/export) contracts?

#lang racket/base
(require (for-syntax racket/base
                     racket/match
                     racket/list
                     racket/syntax
                     racket/struct-info
                     syntax/parse
                     syntax/datum
                     syntax/stx
                     syntax/id-table
                     syntax/transformer)
         racket/contract
         racket/list
         racket/match)
(provide define-interface
         interface?
         unimplemented?
         interface->predicate
         interface-out
         bundle
         bundle?
         bundles->properties
         method-properties
         define/invoke-bundles
         dynamic-invoke-bundles)

(module util racket/base
  (require racket/match racket/list)
  (provide (all-defined-out))

  ;; closure : (Listof X) (Listof Y) (X -> (Listof X))
  ;;        -> (values (Listof X) (Hasheq X (Listof Y)))
  ;; Given initial xs and corresponding ys, returns xs closed under get-next,
  ;; along with mapping of x to originating y. BFS order.
  (define (closure xs ys get-next)
    (define (add y ys) (if (memq y ys) ys (cons y ys)))
    (define (loop xys seen acc nextxyss)
      (match xys
        [(cons (cons x y) xys)
         (define seen* (hash-update seen x (lambda (ys) (add y ys)) null))
         (cond [(hash-has-key? seen x)
                (loop xys seen* acc nextxyss)]
               [else
                (define acc* (cons x acc))
                (define nextxs (get-next x))
                (define nextxys (map (lambda (x) (cons x y)) nextxs))
                (define nextxyss* (cons nextxys nextxyss))
                (loop xys seen* acc* nextxyss*)])]
        ['()
         (cond [(pair? nextxyss)
                (loop (append* (reverse nextxyss)) seen acc null)]
               [else (values (reverse acc) seen)])]))
    (loop (map cons xs ys) (hash) null null)))

(require (submod "." util)
         (for-syntax (submod "." util)))

;; contract for checking implementations of an interface member
(define (impl/c vname ctc)
  (define ctc-get-proj (get/build-late-neg-projection ctc))
  (define important (format "~a (impl)" vname))
  (define message (format "the ~s implementation for" vname))
  (make-contract
   #:name (list 'impl/c (list 'quote vname) (contract-name ctc))
   #:first-order (contract-first-order ctc)
   #:late-neg-projection
   (lambda (blame)
     (define swapped-blame
       ;; #:important resets blame to "produced"!
       (blame-add-context blame message
                          #:important important #:swap? #t))
     (define proj (ctc-get-proj swapped-blame))
     (lambda (v neg-party)
       (proj v neg-party)))
   #:list-contract? (list-contract? ctc)))

(begin-for-syntax
  (define-syntax-class body-term
    #:attributes () #:commit #:opaque
    (pattern _:expr)))

;; stage-contract : (U Contract #f) Party -> (Any Any Party Location -> Any)
(define (stage-contract ctc pos-party)
  ;; pos-party represents interface
  (cond [ctc
         (lambda (value value-name neg-party loc)
           (contract ctc value pos-party neg-party value-name loc))]
        [else
         (lambda (value value-name neg-party src)
           value)]))

;; Opaque wrapper for struct type property values.
(struct prop-val-wrapper (v))

;; ============================================================
;; Interfaces

;; ----------------------------------------
;; Run time

;; RtInterface:
(struct rtif
  (name         ;; Symbol
   uid          ;; InterfaceKey
   supers       ;; (Listof RtInterface)
   vnames       ;; (Listof Symbol)
   pubnames     ;; (Listof Symbol) -- subset of vnames
   ctcv         ;; (Vectorof (U Contract #f)) -- needed by module boundary
   in-ctcv      ;; (Vectorof (Any Party Location -> Any)) -- used to check impls
   out-ctcv     ;; (Vectorof (Any Party Location -> Any))
   fallbacks    ;; VarHash
   vprop        ;; (StructTypeProperty #:in (StructType -> VarHash) #:out VarVector)
   vprop?       ;; (Any -> Boolean)
   vprop-ref    ;; (vprop? -> VarVector)
   )
  #:property prop:custom-write
  (lambda (self out mode)
    (fprintf out "#<interface:~.s>" (rtif-name self))))

(define (interface? v) (rtif? v))

;; InterfaceKey = Symbol, unique to interface (not interned)
;; VarHash = (Hasheq Symbol Value)
;; VarVector = (vector VarHash Value ...)

;; rtifs-closure : (Listof RtInterface) -> (Listof RtInterface)
(define (rtifs-closure ifcs)
  (define-values (ifcs* _h) (closure ifcs ifcs rtif-supers))
  ifcs*)

;; create-rtif : Symbol Symbol (Listof Symbol) (Listof Symbol)
;;               (Vectorof (U Contract #f)) DeriveProps VarHash
;;            -> RtInterface
(define (create-rtif iname uid supers vnames pubnames ctcv derives fallbacks)
  (define len (length vnames))
  (define-values (vprop vprop? vprop-ref)
    (make-interface-property iname vnames derives))
  (define ifc-party (list 'interface iname))
  (define in-ctcv
    (apply vector-immutable
           (for/list ([ctc (in-vector ctcv)] [vname (in-list vnames)])
             (stage-contract (and ctc (impl/c vname ctc)) ifc-party))))
  (define out-ctcv
    (apply vector-immutable
           (for/list ([ctc (in-vector ctcv)] [vname (in-list vnames)])
             (stage-contract ctc ifc-party))))
  (define fallbacks*
    (for/fold ([vh (hasheq)]) ([vname (in-list vnames)])
      (hash-set vh vname (hash-ref fallbacks vname (lambda () (unimplemented iname vname))))))
  (for ([key (in-hash-keys fallbacks)] #:when (not (hash-has-key? fallbacks* key)))
    (error 'interface "unexpected key in fallbacks\n  key: ~e\n  interface: ~e"
           key iname))
  (rtif iname uid supers vnames pubnames ctcv in-ctcv out-ctcv
        fallbacks* vprop vprop? vprop-ref))

(define (make-interface-property iname vnames derives)
  (define (vprop-guard in-val st-info)
    (match-define (prop-val-wrapper initializer) in-val)
    (define super-stype (list-ref st-info 6))
    (define vh (initializer super-stype))
    (apply vector-immutable vh
           (for/list ([vname (in-list vnames)])
             (hash-ref vh vname))))
  (make-struct-type-property iname vprop-guard derives))

(define (rtif-apply-out-ctcs ifc vs bnames neg-party loc)
  (define out-ctcv (rtif-out-ctcv ifc))
  (for/list ([v (in-list vs)]
             [bname (in-list bnames)]
             [staged-out-ctc (in-vector out-ctcv)])
    (staged-out-ctc v bname neg-party loc)))

;; rtif-lookup-definer : RtInterface Symbol -> (U RtInterface #f)
(define (rtif-lookup-definer ifc seek-name)
  (let loop ([ifc ifc])
    (cond [(memq seek-name (rtif-vnames ifc)) ifc]
          [else (ormap loop (rtif-supers ifc))])))

;; rtif-get-stype-vh : RtInterface (U StructType #f) -> VarHash
(define (rtif-get-stype-vh ifc stype)
  (define vprop? (rtif-vprop? ifc))
  (define vprop-ref (rtif-vprop-ref ifc))
  (cond [(vprop? stype) (vector-ref (vprop-ref stype) 0)]
        [else (rtif-fallbacks ifc)]))

(struct unimplemented (iname vname)
  #:property prop:procedure
  (make-keyword-procedure
   (lambda (kws kwargs self . args)
     (match-define (unimplemented iname vname) self)
     (error vname "not implemented\n  interface: ~a" iname))
   (lambda (self . args)
     (match-define (unimplemented iname vname) self)
     (error vname "not implemented\n  interface: ~a" iname))))

;; interface->predicate : RtInterface (U Symbol #f) -> (Any -> Boolean)
(define (interface->predicate ifc [vname #f]
                              #:accept-struct-type? [stype-ok? #f])
  (define who 'interface->predicate)
  (unless (interface? ifc)
    (raise-argument-error who "interface?" ifc))
  (unless (or (eq? vname #f) (symbol? vname))
    (raise-argument-error who "(or/c #f symbol?)" vname))
  (define vprop? (rtif-vprop? ifc))
  (define predicate-name
    (string->symbol (format "~a?" (rtif-name ifc))))
  (cond [vname
         (define difc (rtif-lookup-definer ifc vname))
         (unless difc
           (error who "~a\n  interface: ~e\n  name: ~e"
                  "name not found in interface" ifc vname))
         (define dvprop-ref (rtif-vprop-ref difc))
         (procedure-rename
          (lambda (v)
            (and (vprop? v)
                 (or stype-ok? (not (struct-type? v)))
                 (let ([vh (vector-ref (dvprop-ref v) 0)])
                   (not (unimplemented? (hash-ref vh vname #f))))))
          predicate-name)]
        [else
         (procedure-rename
          (lambda (v)
            (and (vprop? v)
                 (or stype-ok? (not (struct-type? v)))))
          predicate-name)]))

(define fallbacks/c (hash/c symbol? any/c))

;; ----------------------------------------
;; Compile time

(begin-for-syntax
  ;; CtInterface:
  (struct ctif
    (name       ;; Identifier
     uid        ;; InterfaceKey
     rt         ;; Id[RtInterface]
     supers     ;; (Listof CtInterface)
     vnames     ;; (Listof Symbol)
     ginfo      ;; (Listof Identifier) or #f
     )
    #:property prop:custom-write
    (lambda (self out mode)
      (fprintf out "#<ctif:~s>" (syntax-e (ctif-name self))))
    #:property prop:procedure
    (lambda (self stx)
      ((make-variable-like-transformer (ctif-rt self)) stx)))

  (define (create-ctif info-stx)
    (define/with-syntax (iname rtname (super-id ...) (vname ...) ginfo)
      info-stx)
    (define uid (string->uninterned-symbol (symbol->string (syntax-e #'iname))))
    ;; FIXME: check no duplicate names
    (define supers (map syntax-local-value (datum (super-id ...))))
    (let ()
      (define seen (make-hasheq))
      (define-values (all-supers super-h) (closure supers supers ctif-supers))
      (for ([ifc (in-list all-supers)])
        (define oifc (car (hash-ref super-h ifc)))
        (for ([vname (in-list (ctif-vnames ifc))])
          (cond [(hash-ref seen vname #f)
                 => (lambda (oifc1)
                      (raise-syntax-error
                       #f "duplicate name in interface" #'iname #f
                       (list (ctif-name oifc1) (ctif-name oifc))))]
                [else (hash-set! seen vname oifc)])))
      (for ([vname (in-list (datum (vname ...)))])
        (cond [(hash-ref seen (syntax-e vname) #f)
               => (lambda (src1)
                    (raise-syntax-error
                     #f "duplicate name in interface" #'iname vname))]
              [else (hash-set! seen vname #t)])))
    (define ginfo*
      (syntax-parse #'ginfo
        [(gname:id ...) (datum (gname ...))]
        [#f #f]))
    (ctif #'iname uid #'rtname supers (syntax->datum #'(vname ...)) ginfo*))

  (define-syntax-class interface-ref
    #:attributes (value)
    (pattern (~var n (static ctif? "name defined as interface"))
             #:attr value (datum n.value))))

(define-syntax (create-rtif-from-ctif stx)
  (syntax-parse stx
    [(_ ifc:interface-ref pubnames:expr ctcv:expr fallbacks:expr derives:expr)
     (define ct (datum ifc.value))
     (match-define (ctif iname _ uid _ supers vnames _) (datum ifc.value))
     (with-syntax ([iname iname] [uid uid] [vnames vnames])
       (with-syntax ([(super-ifcvar ...) (map ctif-rt supers)])
         #`(create-rtif (quote iname) (quote uid) (list super-ifcvar ...)
                        (quote vnames) pubnames ctcv derives fallbacks)))]))

(define-syntax (define-interface stx)
  (define-syntax-class var-decl
    #:attributes (name src ctc get-public?)
    (pattern name:id
             #:with src #'name
             #:attr ctc #f
             #:attr get-public? (lambda (all-public?) all-public?))
    (pattern [name:id
              (~optional ctc:expr)
              (~optional (~seq #:dynamic-public (~bind [public? #t])))]
             #:with src (datum->syntax #f (list #'name '....) this-syntax)
             #:attr get-public? (lambda (all-public?) (or all-public? (datum public?)))))
  (define-splicing-syntax-class maybe-super
    (pattern (~seq #:super (super:interface-ref ...)))
    (pattern (~seq) #:with (super ...) null))
  (define-splicing-syntax-class derive-clause
    #:attributes (kvpair)
    (pattern (~seq #:derive-property prop prop-value:expr)
             #:declare prop (expr/c #'struct-type-property?)
             #:with kvpair #'(cons prop.c (lambda (v) prop-value))))
  (syntax-parse stx
    [(_ iname:id s:maybe-super (~optional (~seq #:predicate predicate:id))
        (d:var-decl ...)
        (~alt
         (~optional (~seq #:dynamic-public (~bind [all-public? #t]))
                    #:name "dynamic-public clause")
         (~optional (~seq #:fallbacks (~var fallbacks (expr/c #'fallbacks/c)))
                    #:name "fallbacks clause")
         (~optional (~seq #:generics-prefix gprefix:id)
                    #:name "generics prefix clause")
         (~optional (~seq #:no-generics (~bind [no-generics? #t]))
                    #:name "no-generics clause")
         dc:derive-clause)
        ...)
     (when (datum no-generics?)
       (when (datum gprefix)
         (wrong-syntax "cannot use both #:no-generics and #:generics-prefix"))
       (when (datum predicate)
         (wrong-syntax "cannot use both #:no-generics and #:predicate")))
     (define public?s
       (for/list ([get-public? (in-list (datum (d.get-public? ...)))])
         (get-public? (datum all-public?))))
     (define/with-syntax (rtname) (generate-temporaries #'(iname)))
     (define/with-syntax (vname ...) #'(d.name ...))
     (define/with-syntax (pubname ...)
       (for/list ([vname (in-list (datum (vname ...)))]
                  [public? (in-list public?s)]
                  #:when public?)
         vname))
     (define/with-syntax (ctcname ...)
       (generate-temporaries (datum (vname ...))))
     (define/with-syntax ((early-def ...) (late-def ...) ginfo)
       (cond [(datum no-generics?)
              (list null null #'#f)]
             [else
              (define/with-syntax iname?
                (or (datum predicate) (format-id #'iname "~a?" #'iname)))
              (define/with-syntax (gname ...)
                (cond [(datum gprefix)
                       (for/list ([vname (in-list (datum (vname ...)))])
                         (format-id vname "~a~a" #'gprefix vname))]
                      [else #'(vname ...)]))
              (define/with-syntax (vctc? ...)
                (map syntax? (datum ((~? d.ctc #f) ...))))
              #'[[(define (iname? v) ;; define early, available for ctcs
                    (and (not (struct-type? v)) ((rtif-vprop? rtname) v)))]
                 [(define-interface-generics iname ((vctc? gname vname) ...))]
                 (iname? gname ...)]]))
     (define/with-syntax (pre-def ...)
       ;; fixes unbound-identifier errors when used at top level
       (cond [(eq? (syntax-local-context) 'top-level)
              (list #'(define-syntaxes (rtname) (values)))]
             [else null]))
     #'(begin
         pre-def ...
         (define-syntax iname
           (create-ctif
            (quote-syntax
             (iname rtname (s.super ...) (vname ...) ginfo))))
         early-def ...
         (define rtname
           (let ([ctcname (~? (coerce-contract 'define-interface d.ctc) #f)] ...)
             (create-rtif-from-ctif iname (quote (pubname ...))
                                    (vector-immutable ctcname ...)
                                    (~? fallbacks.c (hasheq))
                                    (list dc.kvpair ...))))
         late-def ...)]))

(define-syntax (define-interface-generics stx)
  (syntax-parse stx
    [(_ iname:interface-ref ((ctc? gname vname) ...))
     (define ifc (datum iname.value))
     (define ctc?s (syntax->datum #'(ctc? ...)))
     (define/with-syntax rtname (ctif-rt ifc))
     (define/with-syntax (uname ...) ;; unprotected
       (generate-temporaries #'(gname ...)))
     (define/with-syntax (bname ...)
       (for/list ([gname (in-list (datum (gname ...)))])
         (format-id #f "~a (generic)" gname #:source gname)))
     (define/with-syntax (lname ...) ;; w/ staged out-contracts
       (generate-temporaries #'(gname ...)))
     (define/with-syntax (mname ...) ;; w/ module-boundary contracts
       (generate-temporaries #'(gname ...)))
     (define/with-syntax (quoted-mname-if-defined ...)
       (for/list ([mname (in-list (datum (mname ...)))]
                  [ctc? (in-list ctc?s)])
         (if ctc? #`(quote-syntax #,mname) #'(quote #f))))
     (define/with-syntax (mbc-def ...)
       (cond [(eq? (syntax-local-context) 'module)
              ;; defined name must not be used within defining module because
              ;; support might not be initialized yet; see generic-transformer
              (for/list ([index (in-naturals 0)]
                         [uname (in-list (datum (uname ...)))]
                         [mname (in-list (datum (mname ...)))]
                         [bname (in-list (datum (bname ...)))]
                         [ctc? (in-list (syntax->datum #'(ctc? ...)))]
                         #:when ctc?)
                (with-syntax ([index index] [uname uname] [mname mname] [bname bname])
                  #'(define-module-boundary-contract mname
                      uname (vector-ref (rtif-ctcv rtname) (quote index))
                      #:name-for-blame bname
                      #:pos-source (quote (interface iname)))))]
             [else null]))
     #'(begin
         (define uname
           (make-generic* rtname (quote vname) (quote gname) #f #t))
         ...
         (define-values (lname ...)
           (apply values
                  (rtif-apply-out-ctcs rtname (list uname ...) (quote (bname ...))
                                       (current-contract-region) #f)))
         mbc-def
         ...
         (define-syntax gname
           (generic-transformer
            #'uname
            (quote-syntax lname)
            quoted-mname-if-defined))
         ...)]))

(begin-for-syntax
  ;; (generic-transformer Id (U Id #f) (U Id #f))
  ;; Automatically selects between name bound by module-boundary contract vs
  ;; name bound by with-contract vs unprotected name.
  (struct generic-transformer (uname lname mname)
    #:property prop:procedure
    (lambda (self stx)
      (case (syntax-local-context)
        [(expression)
         (define (can-use-mname?)
           (define id (if (stx-pair? stx) (stx-car stx) stx))
           (match (identifier-binding id)
             [(list* def-mpi _ from-mpi _)
              ;; Candidate criteria for when safe to use mname (if exists):
              ;; 1. reference occurs in other module (def-mpi is not self-mpi)
              ;; 2. reference originates in other modules (def-mpi != from-mpi)
              ;; Second seems more consistent with module-boundary behavior.
              (not (equal? def-mpi from-mpi))]
             [_ #f]))
         (match-define (generic-transformer uname lname mname) self)
         (define replacement-id
           (cond [(and mname (can-use-mname?)) mname]
                 [lname lname]
                 [else uname]))
         ((make-variable-like-transformer replacement-id) stx)]
        [else #`(#%expression #,stx)]))))

(require (for-syntax racket/provide-transform))

(define-syntax interface-out
  (make-provide-transformer
   (lambda (stx modes)
     (syntax-parse stx
       [(_ iname:interface-ref)
        (define ifc (datum iname.value))
        (define/with-syntax predicate (ctif-predicate ifc))
        (define ginfo (ctif-ginfo ifc))
        ;; FIXME: could store and just use mbc names here
        (define/with-syntax (gname ...) (or ginfo null))
        (expand-export
         #'(combine-out iname predicate gname ...)
         modes)]))))

;; ============================================================
;; Generic Functions

;; make-generic : RtInterface Symbol -> (Instance Any ... -> Any)
(define (make-generic ifc name)
  (unless (interface? ifc) (raise-argument-error 'make-generic "interface?" ifc))
  (unless (symbol? name) (raise-argument-error 'make-generic "symbol?" name))
  (or (make-generic* ifc name name #t #f)
      (error/no-method 'make-generic ifc name)))

;; make-generic* : RtInterface Symbol Boolean Boolean
;;              -> (Instance Any ... -> Any) or #f
(define (make-generic* ifc seek-name name ctc? allow-private?)
  (let loop ([ifc ifc])
    (or (for/first ([vname (in-list (rtif-vnames ifc))]
                    [index (in-naturals 1)]
                    [staged-out-ctc (in-vector (rtif-out-ctcv ifc))]
                    #:when (and (eq? vname seek-name)
                                (or allow-private?
                                    (memq seek-name (rtif-pubnames ifc)))))
          (define iname (rtif-name ifc))
          (define vprop? (rtif-vprop? ifc))
          (define vprop-ref (rtif-vprop-ref ifc))
          (define (get-method obj)
            (unless (and (vprop? obj) (not (struct-type? obj)))
              (raise-argument-error name (format "~a?" iname) obj))
            (vector-ref (vprop-ref obj) index))
          (define proc
            (make-keyword-procedure
             (lambda (kws kwargs obj . args)
               (keyword-apply (get-method obj) kws kwargs obj args))
             (procedure-rename
              (lambda (obj . args)
                (apply (get-method obj) obj args))
              name)))
          (if ctc? (staged-out-ctc proc (format "~a (generic)" name) #f #f) proc))
        (ormap loop (rtif-supers ifc)))))

(define (error/no-method who ifc name)
  (error who
         (string-append "no dynamic-public member found"
                        "\n  interface: ~e\n  name: ~e")
         ifc name))


;; ============================================================
;; Bundles

;; Linkage = (Hash InterfaceKey (Box VarHash))
;; LinkageKey = (cons InterfaceKey Tag)
;; Tag = (Listof Symbol)

;; TaggedInterface = (cons RtInterface Tag)
;; Two tags have special significance:
;; - '() -- default; exports with empty tag are bound to struct-type-properties
;; - '(super) -- reserved for importing super-struct or fallbacks implementation
;;               disallowed as export; automatically initialized by linker
;;               note: import super allowed even if no export to ifc in bundle

(define (tagged-interface? v)
  (and (pair? v) (rtif? (car v)) (list? (cdr v)) (andmap symbol? (cdr v))))

(define (tagged-interface->linkage-key ti)
  (match ti [(cons ifc tag) (cons (rtif-uid ifc) tag)]))

(define (tagged-interfaces-closure tis)
  (define (ti-next ti)
    (match-define (cons ifc tag) ti)
    (map (lambda (ifc) (cons ifc tag)) (rtif-supers ifc)))
  (define-values (closed-tis _h) (closure tis tis ti-next))
  closed-tis)

(define (tagged-interface->string ti)
  ;; also accepts symbol in car
  (cond [(null? (cdr ti)) (format "~.s" (car ti))]
        [else (format "~.s #:tag (~.s)" (car ti) (cdr ti))]))

;; Bundle = Bundle1 | (compound-bundle (Listof BundlePart))
(define (bundle? v) (or (bundle1? v) (compound-bundle? v)))

(struct compound-bundle (parts)
  #:reflection-name 'bundle)
(struct bundle1
  (exports    ;; (Listof TaggedInterface), closed
   imports    ;; (Listof TaggedInterface), closed
   init!      ;; Linkage -> Void
   ) #:reflection-name 'bundle)

;; flatten-bundles : (Listof Bundle) -> (Listof Bundle1)
(define (flatten-bundles bs)
  (append* (for/list ([b (in-list bs)])
             (match b
               [(compound-bundle bs) (flatten-bundles bs)]
               [(? bundle1?) (list b)]))))

(define listof-bundle/c (listof bundle?))

;; ----------------------------------------

;; make-bundle : #:{export,import} (Listof TaggedInterface) (Lookup -> NameHash)
;;            -> Bundle
;; where Lookup = (TaggedInterface Symbol -> Any)
(define (make-bundle make-table
                     #:export [exports0 null]
                     #:import [imports0 null]
                     #:link [linked-bs null])
  (define exports1 (convert-tagged-interfaces exports0))
  (unless exports1
    (raise-argument-error 'make-bundle "(listof tagged-interface?)" exports0))
  (define imports1 (convert-tagged-interfaces imports0))
  (unless imports1
    (raise-argument-error 'make-bundle "(listof tagged-interface?)" imports0))
  (unless (and (list? linked-bs) (andmap bundle? linked-bs))
    (raise-argument-error 'make-bundle "(listof bundle?)" linked-bs))
  (unless (and (procedure? make-table) (procedure-arity-includes? make-table 1))
    (raise-argument-error 'make-bundle "(procedure-arity-includes/c 1)" make-table))
  (define exports (tagged-interfaces-closure exports1))
  (define imports (tagged-interfaces-closure imports1))
  (define (init! linkage)
    (define lookup* ;; mutated
      (make-linkage-lookup linkage))
    (define (lookup ifc seek-name)
      (lookup* ifc seek-name))
    (define nh (make-table lookup))
    (unless (and (hash? nh) (for/and ([key (in-hash-keys nh)]) (symbol? key)))
      (error 'make-bundle "procedure result is not hash with symbol keys\n  result: ~e" nh))
    (when #t
      (for ([name (in-hash-keys nh)])
        (unless (for/or ([export (in-list exports)])
                  (memq name (rtif-vnames (car export))))
          (error 'make-bundle "unexpected key in result\n  key: ~e" name))))
    (set! lookup*
          (lambda (ifc seek-name)
            (error 'lookup "~a\n  interface: ~e\n  name: ~e"
                   "cannot call after linking is complete" ifc seek-name)))
    (for ([export (in-list exports)])
      (define lkey (tagged-interface->linkage-key export))
      (define super-lkey (cons (car lkey) '(super)))
      (define super-vh (unbox (hash-ref linkage super-lkey)))
      (define export-box (hash-ref linkage lkey))
      (set-box! export-box
                (for/fold ([vh super-vh])
                          ([vname (in-list (rtif-vnames (car export)))]
                           #:when (hash-has-key? nh vname))
                  (hash-set vh vname (hash-ref nh vname))))))
  (define b1 (bundle1 exports imports init!))
  (make-bundle* b1 linked-bs))

;; make-linkage-lookup : Linkage -> TaggedInterface Symbol -> Any
(define ((make-linkage-lookup linkage) ti0 seek-name)
  (define ti1 (convert-tagged-interface ti0))
  (unless ti1 (raise-argument-error 'lookup "tagged-interface?" ti0))
  (unless (symbol? seek-name) (raise-argument-error 'lookup "symbol?" seek-name))
  (match-define (cons ifc0 tag) ti0)
  (define difc (rtif-lookup-definer ifc0 seek-name))
  (cond [difc
         (define linkage-key (cons (rtif-uid difc) tag))
         (cond [(hash-ref linkage linkage-key #f)
                => (lambda (vhbox)
                     (unless (unbox vhbox)
                       (error 'lookup "~a\n  tagged interface: ~e"
                              "imported interface not initialized" ti0))
                     (hash-ref (unbox vhbox) seek-name))]
               [else (error 'lookup "~a\n  tagged interface: ~e"
                            "interface not imported" ti0)])]
        [else (error 'lookup "~a\n  interface: ~e\n  name: ~e"
                     "not found in interface" ifc0 seek-name)]))

(define (make-bundle* b1 bs)
  (if (null? bs) b1 (compound-bundle (append bs (list b1)))))

(define (convert-tagged-interfaces vs)
  (and (list? vs)
       (let ([tis (map convert-tagged-interface vs)])
         (and (andmap values tis) tis))))
(define (convert-tagged-interface v)
  (match v
    [(? interface? ifc) (list ifc)]
    [(cons (? interface?) (list (? symbol?) ...)) v]
    [_ #f]))

;; ----------------------------------------

(begin-for-syntax
  (struct impexp (ostx ifc tag prefix) #:transparent)

  (define-syntax-class export-spec
    #:attributes (ast)
    (pattern ifc:interface-ref
             #:attr ast
             (let ([prefix (format-id #'ifc "")])
               (impexp this-syntax (datum ifc.value) '() prefix)))
    (pattern [ifc:interface-ref
              (~alt
               (~optional (~seq #:tag (tagp:id ...))
                          #:name "tag clause")
               (~optional (~seq #:prefix prefix:id)
                          #:name "prefix clause"))
              ...]
             #:attr ast
             (let ([tag (syntax->datum #'(~? (tagp ...) ()))]
                   [prefix (or (datum prefix) (format-id #'ifc ""))])
               (impexp this-syntax (datum ifc.value) tag prefix))))

  (define-syntax-class import-spec
    #:attributes (ast)
    (pattern ifc:interface-ref
             #:attr ast
             (let ([prefix (format-id #'ifc "")])
               (impexp this-syntax (datum ifc.value) '() prefix)))
    (pattern [ifc:interface-ref
              (~alt
               (~optional t:import-tag-clause
                          #:name "tag clause")
               (~optional (~seq #:prefix prefix:id)
                          #:name "prefix clause"))
              ...]
             #:attr ast
             (let ([tag (or (datum t.tag) null)]
                   [prefix (or (datum prefix)
                               (format-id #'ifc (or (datum t.prefix) "")))])
               (impexp this-syntax (datum ifc.value) tag prefix))))

  (define-splicing-syntax-class import-tag-clause
    #:attributes (tag prefix)
    (pattern (~seq #:super)
             #:attr tag '(super)
             #:attr prefix "super-")
    (pattern (~seq #:tag (t:id ...))
             #:attr tag (syntax->datum #'(t ...))
             #:attr prefix #f))

  (define (impexp-supers ie)
    (match-define (impexp ostx ifc tag prefix) ie)
    (for/list ([super-ifc (in-list (ctif-supers ifc))])
      (impexp ostx super-ifc tag prefix)))

  (define (impexp->ti ie) (cons (impexp-ifc ie) (impexp-tag ie)))

  (define (impexp-compat? ie1 ie2)
    (match-define (impexp _ ifc1 tag1 prefix1) ie1)
    (match-define (impexp _ ifc2 tag2 prefix2) ie2)
    (and (eq? ifc1 ifc2) (equal? tag1 tag2)
         (bound-identifier=? prefix1 prefix2)))

  (define (ct-ti-supers ti)
    (match-define (cons ifc tag) ti)
    (map (lambda (v) (cons v tag)) (ctif-supers ifc)))

  (define (ct-ti->string ti)
    (match ti
      [(cons ifc '()) (format "~.s" (syntax-e (ctif-name ifc)))]
      [(cons ifc tag) (format "~.s #:tag ~.s" (syntax-e (ctif-name ifc)) tag)]))

  (define (check-impexps ies check-names? stx whats)
    (define tis (map impexp->ti ies))
    (define-values (all-tis ti=>ies) (closure tis ies ct-ti-supers))
    ;; each ti must have one prefix; if so, map to one import (first occurring in BFS)
    (define ti=>ie (make-hash))
    (for ([ti (in-list all-tis)])
      (define ies (reverse (hash-ref ti=>ies ti)))
      (define ie0 (car ies))
      (define prefix0 (impexp-prefix ie0))
      (for ([ie (in-list (cdr ies))])
        (unless (bound-identifier=? prefix0 (impexp-prefix ie))
          (define ti-string (ct-ti->string ti))
          (raise-syntax-error
           #f (format "incompatible ~a; prefixes differ\n  interface: ~a" whats ti-string)
           stx #f (list (impexp-ostx ie0) (impexp-ostx ie)))))
      (hash-set! ti=>ie ti ie0))
    ;; make sure each prefixed name has only one binding
    (when check-names?
      (define id=>ie (make-bound-id-table))
      (for ([ti (in-list all-tis)])
        (define ie (hash-ref ti=>ie ti))
        (match-define (impexp ostx _ tag prefix) ie)
        (for ([vname (in-list (ctif-vnames (car ti)))])
          (define id (format-id prefix "~a~a" prefix vname))
          (define already-ie (bound-id-table-ref id=>ie id #f))
          (when already-ie
            (raise-syntax-error
             #f (format "incompatible ~a\n  name collision: ~.s" whats (syntax-e id))
             stx #f (list (impexp-ostx already-ie) ostx)))
          (bound-id-table-set! id=>ie id ie))))
    ;; ----
    (for/list ([ti (in-list all-tis)])
      (cons ti (hash-ref ti=>ie ti))))

  (define (ti+ie-extract ti+ie)
    (match-define (cons (cons ifc tag) (impexp ostx _ _ prefix)) ti+ie)
    (list #`(cons #,(ctif-rt ifc) (quote #,tag))
          prefix (ctif-vnames ifc) ostx))

  (struct bctx (ostxs tis prefixes vnamess lname=>vname vname=>ref [lname=>t #:mutable]))

  (define (make-bctx einfo-stx)
    (define/with-syntax ((eostx ti-expr eprefix (evname ...)) ...) einfo-stx)
    (define lname=>vname (make-bound-id-table))
    (for ([eprefix (in-list (datum (eprefix ...)))]
          [evnames (in-list (datum ((evname ...) ...)))]
          #:when #t
          [evname (in-list evnames)])
      (define localname (format-id eprefix "~a~a" eprefix evname))
      (bound-id-table-set! lname=>vname localname (syntax-e evname)))
    (define vname=>ref (make-hasheq))
    (define (nonempty-id? id) ;; empty includes '|| but also empty non-interned symbols
      (not (zero? (string-length (symbol->string (syntax-e id))))))
    (define prefixes*
      (let* ([prefixes (remove-duplicates (datum (eprefix ...)) bound-identifier=?)])
        (filter values (for/list ([prefix (in-list prefixes)])
                         (define str (symbol->string (syntax-e prefix)))
                         (and (positive? (string-length str))
                              (cons str prefix))))))
    (bctx (datum (eostx ...)) (datum (ti-expr ...)) prefixes*
          (syntax->datum #'((evname ...) ...)) lname=>vname vname=>ref #f))

  (define (bctx-add-seen! ctx ids stx)
    (match-define (bctx _ _ prefixes _ lname=>vname vname=>ref lname=>t) ctx)
    (define (prefixed-id? id) ;; starts with a prefix and has right scopes
      (define sym (syntax-e id))
      (define str (symbol->string sym))
      (for/or ([prefixp (in-list prefixes)])
        (match-define (cons pstr pid) prefixp)
        (and (<= (string-length pstr) (string-length str))
             (equal? pstr (substring str 0 (string-length pstr)))
             (let ([id* (datum->syntax pid sym)])
               (bound-identifier=? id id*)))))
    (for ([id (in-list ids)])
      (cond [(bound-id-table-ref lname=>vname id #f)
             => (lambda (vname) (hash-set! vname=>ref vname id))]
            [(prefixed-id? id)
             (raise-syntax-error
              #f "defined name has export prefix but does not match any export" stx id)]
            [else (void)])))

  (define (bctx-exported-var? ctx id)
    (unless (bctx-lname=>t ctx)
      ;; must wait until pass2 to build free-id-table,
      ;; because identifier-binding-symbol may change
      (define lname=>t (make-free-id-table))
      (for ([ref (in-hash-values (bctx-vname=>ref ctx))])
        (free-id-table-set! lname=>t ref #t))
      (set-bctx-lname=>t! ctx lname=>t))
    (define lname=>t (bctx-lname=>t ctx))
    (and (free-id-table-ref lname=>t id #f) #t))

  (void))

(define-syntax (method-properties stx)
  (case (syntax-local-context)
    [(expression)
     #`(bundles->properties
        #:who 'method-properties
        (bundle* #,stx))]
    [else #`(#%expression #,stx)]))

(define-syntax (bundle stx)
  (case (syntax-local-context)
    [(expression)
     #`(bundle* #,stx)]
    [else #`(#%expression #,stx)]))

(define-syntax (bundle* outer-stx)
  (define stx (syntax-parse outer-stx [(_ expr) #'expr]))
  (syntax-parse stx
    [(_ #:link (~var link-bs (expr/c #'listof-bundle/c)))
     #'(compound-bundle link-bs.c)]
    [(_ (~alt
         (~optional (~seq #:export (e:export-spec ...))
                    #:name "export clause")
         (~optional (~seq #:import (i:import-spec ...))
                    #:name "import clause")
         (~optional (~seq #:link (~var link-bs (expr/c #'listof-bundle/c)))
                    #:name "link clause"))
        ...
        body:body-term ...)
     (define eti+ie-list (check-impexps (datum (~? (e.ast ...) ())) #f stx "exports"))
     (define iti+ie-list (check-impexps (datum (~? (i.ast ...) ())) #t stx "imports"))
     (define/with-syntax ((eti eprefix evnames eostx) ...)
       (map ti+ie-extract eti+ie-list))
     (define/with-syntax ((iti iprefix ivnames iostx) ...)
       (map ti+ie-extract iti+ie-list))
     #`(make-bundle*
        (bundle1
         (list eti ...) (list iti ...)
         (lambda (linkage)
           (define-names #:lazy iprefix ivnames iti linkage iostx)
           ...
           (define-syntaxes (the-bctx)
             (make-bctx (quote-syntax ((eostx eti eprefix evnames) ...))))
           (bundle-body-wrap the-bctx body) ...
           (#%expression (bundle-body-result the-bctx linkage))))
        (~? link-bs.c null))]))

(define-syntax (bundle-body-wrap stx)
  (syntax-parse stx
    [(_ ctx-id body)
     (define ctx (syntax-local-value #'ctx-id))
     (define ee (local-expand #'body (syntax-local-context) #f))
     (syntax-parse ee
       #:literal-sets (kernel-literals)
       [(begin ~! form ...)
        #'(begin (bundle-body-wrap ctx-id form) ...)]
       [(define-values ~! (var:id ...) rhs:expr)
        (let ([vars (syntax->list (syntax-local-introduce #'(var ...)))])
          (bctx-add-seen! ctx vars ee))
        #'(define-values (var ...) (bundle-expr-wrap ctx-id rhs))]
       [(define-syntaxes ~! (var:id ...) . _)
        (let ([vars (syntax->list (syntax-local-introduce #'(var ...)))])
          (bctx-add-seen! ctx vars ee))
        ee]
       [_ #`(#%expression (bundle-expr-wrap ctx-id #,ee))])]))

(define-syntax (bundle-expr-wrap stx)
  (syntax-parse stx
    [(_ ctx-id e)
     (define ctx (syntax-local-value #'ctx-id))
     (define (loop e)
       (define (loop* es)
         (for-each loop (syntax->list es)))
       (syntax-parse e
         #:literal-sets (kernel-literals)
         [(#%plain-lambda formals e ...)
          (loop* #'(e ...))]
         [(case-lambda [formals e ...] ...)
          (loop* #'(e ... ...))]
         [(if e ...)
          (loop* #'(e ...))]
         [(begin e ...)
          (loop* #'(e ...))]
         [(begin0 e ...)
          (loop* #'(e ...))]
         [(let-values ([vars rhs] ...) body ...)
          (loop* #'(rhs ... body ...))]
         [(letrec-values ([vars rhs] ...) body ...)
          (loop* #'(rhs ... body ...))]
         [(with-continuation-mark e ...)
          (loop* #'(e ...))]
         [(#%plain-app e ...)
          (loop* #'(e ...))]
         [(set! var rhs)
          (when (bctx-exported-var? ctx (syntax-local-introduce #'var))
            (raise-syntax-error #f "attempt to mutate exported variable" e #'var))
          (loop #'rhs)]
         [_ (void)]))
     (define-values (ee opaque)
       (syntax-local-expand-expression #'e))
     (loop ee)
     opaque]))

(define-syntax (bundle-body-result stx)
  (syntax-parse stx
    [(_ ctx-id linkage)
     (define ctx (syntax-local-value #'ctx-id))
     (match-define (bctx eostxs etis _ evnamess _ vname=>ref _) ctx)
     #`(begin
         #,@(for/list ([eostx (in-list eostxs)]
                       [eti (in-list etis)]
                       [evnames (in-list evnamess)])
              (define/with-syntax ((def-vname def-index def-localname) ...)
                (for/list ([evname (in-list evnames)]
                           [index (in-naturals)]
                           #:when (hash-has-key? vname=>ref evname))
                  (define localname (syntax-local-introduce (hash-ref vname=>ref evname)))
                  (list evname index localname)))
              #`(linkage-set! linkage #,eti (current-contract-region) (quote-syntax #,eostx)
                              '(def-vname ...) '(def-index ...)
                              (list def-localname ...)))
         (void))]))

(define (linkage-set! linkage ti impl-party src-stx vnames vindexes vvalues)
  (define lkey (tagged-interface->linkage-key ti))
  (define super-lkey (cons (car lkey) '(super)))
  (define vhbox (hash-ref linkage lkey))
  (define supervh (unbox (hash-ref linkage super-lkey)))
  (define iname (rtif-name (car ti)))
  (define in-ctcv (rtif-in-ctcv (car ti)))
  (set-box! vhbox
            (for/fold ([vh supervh])
                      ([vname (in-list vnames)]
                       [vindex (in-list vindexes)]
                       [vvalue (in-list vvalues)])
              (define staged-in-ctc (vector-ref in-ctcv vindex))
              (define checked-value (staged-in-ctc vvalue #f impl-party src-stx))
              (hash-set vh vname checked-value))))

(define-syntax (define-names stx)
  (syntax-parse stx
    [(_ mode prefix:id (vname:id ...) ti:expr linkage:expr ostx)
     (define/with-syntax (varvar ...)
       (generate-temporaries #'(vname ...)))
     (define/with-syntax (prefixedname ...)
       (for/list ([name (in-list (datum (vname ...)))])
         (format-id #'prefix "~a~a" #'prefix name)))
     (case (syntax->datum #'mode)
       [(#:strict)
        (define/with-syntax (index ...)
          (for/list ([i (in-range (length (datum (vname ...))))]) i))
        #`(begin
            (define-values (varvar ...)
              (let* ([lkey (tagged-interface->linkage-key ti)]
                     [vh (unbox (hash-ref linkage lkey))])
                (apply values
                       (vh-extract vh (car ti) (quote (vname ...))
                                   (current-contract-region) (quote-syntax ostx)
                                   "import"))))
            (define-syntax prefixedname
              (make-variable-like-transformer
               (quote-syntax varvar)))
            ...)]
       [(#:lazy)
        #`(begin
            (define varvar (box #f))
            ...
            (define init! ;; mutated
              (let* ([lkey (tagged-interface->linkage-key ti)]
                     [vhbox (hash-ref linkage lkey)])
                (lambda (who)
                  (vh-init! who ti (current-contract-region) (quote-syntax ostx)
                            vhbox '(vname ...) (list varvar ...))
                  (set! init! #f))))
            (define-syntax prefixedname
              (make-variable-like-transformer
               (quote-syntax
                (begin (when init! (init! (quote prefixedname)))
                       (unbox varvar)))))
            ...)])]))

(define (vh-extract vh ifc vnames neg-party src-stx what)
  (define out-ctcv (rtif-out-ctcv ifc))
  (define pos-party (list 'interface (rtif-name ifc)))
  (define src-stx (quote-syntax ostx))
  (for/list ([vname (in-list vnames)]
             [staged-out-ctc (in-vector out-ctcv)])
    (define v (hash-ref vh vname))
    (define bname (format "~s (~a)" vname what))
    (staged-out-ctc v bname neg-party src-stx)))

(define (vh-init! who ti neg-party src-stx vhbox vnames varboxes)
  (define pos-party (list 'interface (rtif-name (car ti))))
  (define out-ctcv (rtif-out-ctcv (car ti)))
  (unless (unbox vhbox)
    (error who "import not initialized\n  import: ~a"
           (tagged-interface->string ti)))
  (define vh (unbox vhbox))
  (for ([vname (in-list vnames)]
        [varbox (in-list varboxes)]
        [staged-out-ctc (in-vector out-ctcv)])
    (define v (hash-ref vh vname))
    (define bname (format "~s (import)" vname))
    (define v* (staged-out-ctc v bname neg-party src-stx))
    (set-box! varbox v*)))


;; ============================================================
;; Linking Bundles

;; dummy property to use when no other prop needs updating
(define dummy-prop
  (let-values ([(prop prop? prop-ref)
                (make-interface-property 'unused null null)])
    prop))

;; bundles->properties : Bundle ...
;;                    -> (Listof (cons VarProp (Wrap (StructType -> VarHash))))
(define (bundles->properties #:who [who 'bundles->properties] . bs0)
  (unless (and (list? bs0) (andmap bundle? bs0))
    (raise-argument-error who "(listof bundle?)" bs0))
  (define bs (flatten-bundles bs0))
  (define-values (exports linkage initialize-supers!)
    (bundles-prepare-linkage who bs))
  (define (initialize! stype) ;; mutated
    (initialize-supers! stype)
    (run-bundles bs linkage)
    (set! initialize! void))
  (define properties
    (for/list ([export (in-list exports)] #:when (null? (cdr export)))
      (define ifc (car export))
      (define uid (rtif-uid ifc))
      (cons (rtif-vprop ifc)
            (prop-val-wrapper
             (lambda (super-stype)
               (initialize! super-stype)
               (unbox (hash-ref linkage (cons uid '()))))))))
  (cond [(pair? properties) properties]
        [else
         ;; use dummy to run bundles even if no real properties attached
         (list (cons dummy-prop
                     (prop-val-wrapper
                      (lambda (super-stype)
                        (initialize! super-stype)
                        (hasheq)))))]))

;; bundles-prepare-linkage : Symbol (Listof Bundle1)
;;                        -> (values (Listof TaggedInterface)
;;                                   Linkage
;;                                   (StructType/#f -> Void))
(define (bundles-prepare-linkage who bs)
  (define exports (tagged-interfaces-closure (append* (map bundle1-exports bs))))
  (define exported-ifcs (remove-duplicates (map car exports)))
  (define pre-linkage (build-linkage who bs))
  (define imp-super-ifcs (check-linkage who bs pre-linkage))
  (define super-ifcs (remove-duplicates (append exported-ifcs imp-super-ifcs)))
  (define linkage
    (for/fold ([linkage pre-linkage]) ([ifc (in-list super-ifcs)])
      (define super-lkey (cons (rtif-uid ifc) '(super)))
      (hash-set linkage super-lkey (box #f))))
  (define (initialize-supers! stype)
    (for ([ifc (in-list super-ifcs)])
      (define super-vh (rtif-get-stype-vh ifc stype))
      (define super-lkey (cons (rtif-uid ifc) '(super)))
      (set-box! (hash-ref linkage super-lkey) super-vh)))
  (values exports linkage initialize-supers!))

;; build-linkage : Symbol (Listof BundlePart1) -> Linkage*
;; Returns linkage with exports in boxes, must clear after checking.
(define (build-linkage who bs)
  ;; handle-bundle : Bundle1 Linkage -> Linkage
  (define (handle-bundle b linkage)
    (foldl handle-export linkage (bundle1-exports b)))
  ;; handle-export : TaggedInterface Linkage -> Linkage
  (define (handle-export export linkage)
    (define lkey (tagged-interface->linkage-key export))
    (cond [(super-linkage-key? lkey)
           (error who "illegal export with reserved super tag\n  export: ~a"
                  (tagged-interface->string export))]
          [(hash-ref linkage lkey #f)
           => (lambda (link-box)
                (error who "duplicate export: ~a"
                       (tagged-interface->string (unbox link-box))))]
          [else (hash-set linkage lkey (box export))]))
  (foldl handle-bundle (empty-linkage) bs))

;; check-linkage : Symbol (Listof BundlePart1) Linkage* -> (Listof RtInterface)
;; Checks all imports satisfied, except '(super) tagged.
;; Returns interfaces with '(super) imports. Also clears linkage boxes.
(define (check-linkage who bs linkage)
  ;; check-bundle : Bundle1 (Listof RtInterface) -> Void
  (define (check-bundle b acc)
    (foldl check-import acc (bundle1-imports b)))
  ;; check-import : TaggedInterface (Listof RtInterface) -> Void
  (define (check-import import acc)
    (define lkey (tagged-interface->linkage-key import))
    (cond [(super-linkage-key? lkey) (cons (car import) acc)]
          [(hash-has-key? linkage lkey) acc]
          [else (error who "import missing matching export\n  import: ~a"
                       (tagged-interface->string import))]))
  (begin0 (remove-duplicates (foldl check-bundle null bs))
    (for ([b (in-hash-values linkage)]) (set-box! b #f))))

;; empty-linkage : -> Linkage
;; Must use equal? hash because keys are lists.
(define (empty-linkage) (hash))

;; super-linkage-key? : LinkageKey -> Boolean
(define (super-linkage-key? v)
  (match v [(list _ 'super) #t] [_ #f]))

;; run-bundles : (Listof Bundle1) Linkage -> Void
(define (run-bundles bs linkage)
  (for ([b (in-list bs)])
    ((bundle1-init! b) linkage)))

;; ----------------------------------------

(define-syntax (define/invoke-bundles stx)
  (when (eq? (syntax-local-context) 'expression)
    (raise-syntax-error #f "not allowed in expression context" stx))
  (syntax-parse stx
    [(_ (~optional (~seq #:export (e:export-spec ...)))
        (~var b (expr/c #'bundle?)) ...)
     (define eti+ie-list (check-impexps (datum (~? (e.ast ...) ())) #f stx "exports"))
     (define/with-syntax ((eti eprefix evnames eostx) ...)
       (map ti+ie-extract eti+ie-list))
     #'(begin
         (define linkage
           (invoke-bundles* 'define/invoke-bundles (list eti ...) (list b.c ...)))
         (define-names #:strict eprefix evnames eti linkage eostx) ...
         (define-values () (begin (set! linkage #f) (values))))]))

;; invoke-bundles* : Symbol (Listof TaggedInterface) (Listof Bundle) -> Void
;; PRE: binds is closed
(define (invoke-bundles* who binds bs0)
  ;; FIXME: check for var collisions
  (define bs (flatten-bundles bs0))
  (define-values (exports linkage initialize-supers!)
    (bundles-prepare-linkage 'invoke-bundles bs))
  (for ([bind (in-list binds)])
    (define lkey (tagged-interface->linkage-key bind))
    (unless (hash-has-key? linkage lkey)
      (error 'invoke-bundles "~a\n  tagged interface: ~a"
             "tagged interface not exported"
             (tagged-interface->string bind))))
  (initialize-supers! #f)
  (run-bundles bs linkage)
  linkage)

;; dynamic-invoke-bundles : #:bind (Listof TaggedInterface) (Listof Bundle) -> VarHash
(define (dynamic-invoke-bundles #:bind binds0
                                #:flatten? [flatten? #t]
                                . bs0)
  (define who 'dynamic-invoke-bundles)
  (define binds1 (convert-tagged-interfaces binds0))
  (unless binds1 (raise-argument-error who "(listof tagged-interface/c)" binds0))
  (for ([b (in-list bs0)])
    (unless (bundle? b) (raise-argument-error who "bundle?" b)))
  (define linkage (invoke-bundles* who binds1 bs0))
  (if flatten?
      (linkage->flat-vh who linkage binds1)
      (linkage->nested-vh who linkage binds1)))

(define (linkage->flat-vh who linkage binds1)
  (define binds (tagged-interfaces-closure binds1))
  (for/fold ([h (hasheq)]) ([bind (in-list binds)])
    (define ifc (car bind))
    (define lkey (tagged-interface->linkage-key bind))
    (define bindvh (unbox (hash-ref linkage lkey)))
    (define vnames (rtif-vnames (car bind)))
    (define neg-party 'dynamic-invoke-bundles)
    (define vvalues (vh-extract bindvh ifc vnames neg-party #f "dynamic export"))
    (for/fold ([h h]) ([vname (in-list vnames)] [vvalue (in-list vvalues)])
      (hash-set h vname vvalue))))

(define (linkage->nested-vh who linkage binds1)
  (for/fold ([tih (hash)]) ([bind (in-list binds1)])
    (define tag (cdr bind))
    (define vh
      (let loop ([ifc (car bind)] [vh (hasheq)])
        (define lkey (tagged-interface->linkage-key (cons ifc tag)))
        (define bindvh (unbox (hash-ref linkage lkey)))
        (define vnames (rtif-vnames ifc))
        (define neg-party 'dynamic-invoke-bundles)
        (define vvalues (vh-extract bindvh ifc vnames neg-party #f "dynamic export"))
        (define vh*
          (for/fold ([vh vh])
                    ([ifc (in-list (rtif-supers ifc))])
            (loop ifc vh)))
        (for/fold ([vh vh*])
                  ([vname (in-list vnames)]
                   [vvalue (in-list vvalues)])
          (hash-set vh vname vvalue))))
    (hash-set tih bind vh)))
