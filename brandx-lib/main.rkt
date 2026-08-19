;; Copyright 2026 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

;; Restrictions and limitations:
;; - dispatch on first positional argument
;; - sub-interface cannot "override" super-interface methods
;; - `augment` methods not supported, since call not tied to `this`
;; - interface contracts cannot refer to interface members

;; TODO:
;; - define-signature: add abbrev for repeated #:dep clauses
;; - define-signature: add #:require (sig ...) option
;;   - required signature member names are available for dep contracts
;;   - at link time, export of sig (w/ same tags) must be in linkage graph

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
                     syntax/transformer
                     racket/provide-transform)
         racket/contract
         racket/contract/collapsible
         racket/list
         racket/vector
         racket/match)
(provide define-interface
         define-signature
         interface-out
         bundle
         bundle?
         bundles->properties
         method-properties
         define/invoke-bundles
         define-struct-abbrevs)

;; ============================================================
;; Prelude

(module closure racket/base
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

(require (submod "." closure)
         (for-syntax (submod "." closure)))

(begin-for-syntax
  (define-syntax-class body-term
    #:attributes () #:commit #:opaque
    (pattern _:expr)))

;; Opaque wrapper for struct type property values.
(struct prop-val-wrapper (v))

;; ============================================================
;; Signatures and Interfaces

;; RtSig = RtDepSig | RtInterface

(struct rtsig
  (name         ;; Symbol
   uid          ;; SigKey
   supers       ;; (Listof RtSig)
   vnames       ;; (Listof Symbol)
   ))

;; Subtypes place further restrictions on fields.
;; Subtypes handle import, export, and linkage initialization differently.

;; SigKey = Symbol, unique to interface (not interned)

;; rtsigs-closure : (Listof RtSig) -> (Listof RtSig)
(define (rtsigs-closure sigs)
  (define-values (sigs* _h) (closure sigs sigs rtsig-supers))
  sigs*)

;; ------------------------------------------------------------
;; Dependent Signatures

;; Import/export: apply contracts in two passes: non-dep, then dep (using
;; indy-protected dependencies).
;; Exports must be complete; no super table.

;; RtDepSig:
(struct rtdepsig rtsig
  (;; supers    ;; always empty
   ctcv         ;; (Vectorof (U #f Contract (cons (Listof Symbol) (Any ... -> Contract))))
   )
  #:property prop:custom-write
  (lambda (self out mode)
    (fprintf out "#<signature:~.s>" (rtsig-name self))))

(define (create-rtdepsig signame uid vnames ctcv)
  (rtdepsig signame uid null vnames ctcv))

;; rtdepsig-apply-contracts : RtDepSig VarHash Boolean Party Location -> VarHash
(define (rtdepsig-apply-contracts sig vh0 impl? neg-party src-stx)
  (define pos-party (list 'signature (rtsig-name sig)))
  (define ctc-party (list 'signature-contract (rtsig-name sig))) ;; ??
  (define (apply-contract vname ctc v [neg-party neg-party])
    (let ([ctc (if impl? (impl/c vname ctc) ctc)])
      ((stage-contract ctc pos-party) v vname neg-party src-stx)))
  (define vnames (rtsig-vnames sig))
  (define ctcv (rtdepsig-ctcv sig))
  (define vh1 ;; apply non-dependent contracts first, for neg-party
    ;; Do this before any indy contracts to make error order more predictable.
    (for/fold ([vh vh0])
              ([vname (in-list vnames)]
               [ctce (in-vector ctcv)]
               #:when (and ctce (not (pair? ctce))))
      (hash-set vh vname (apply-contract vname ctce (hash-ref vh vname)))))
  (define vh-i ;; apply indy contracts (with contract as neg party)
    ;; TODO: make this lazy?
    (for/fold ([vh vh0])
              ([vname (in-list vnames)]
               [ctce (in-vector ctcv)]
               #:when (and ctce (not (pair? ctce))))
      (hash-set vh vname (apply-contract vname ctce (hash-ref vh vname) ctc-party))))
  (define vh2
    (for/fold ([vh vh1])
              ([vname (in-list vnames)]
               [ctce (in-vector ctcv)]
               #:when (pair? ctce))
      (match-define (cons deps make-ctc) ctce)
      (define depvs (for/list ([dep (in-list deps)]) (hash-ref vh-i dep)))
      (define ctc (apply make-ctc depvs))
      (hash-set vh vname (apply-contract vname ctc (hash-ref vh vname)))))
  vh2)


;; ------------------------------------------------------------
;; Interfaces

;; Import/export: apply contract (via {in,out}-ctcv) to value.
;; Export table is formed by starting with super table, replacing mappings
;; with (contract-wrapped) definitions.

;; RtInterface:
(struct rtif rtsig
  (;; supers    ;; (Listof RtInterface)
   ctcv         ;; (Vectorof (U Contract #f)), used by module boundary
   in-ctcv      ;; (Vectorof (Any Party Location -> Any)) -- used to check impls
   out-ctcv     ;; (Vectorof (Any Party Location -> Any))
   fallbacks    ;; VarHash
   vprop        ;; (StructTypeProperty #:in (StructType -> VarHash) #:out VTable)
   vprop?       ;; (Any -> Boolean)
   vprop-ref    ;; (vprop? -> VTable)
   )
  #:property prop:custom-write
  (lambda (self out mode)
    (fprintf out "#<interface:~.s>" (rtsig-name self))))

;; VarHash = (Hasheq Symbol Value)
;; VTable = (vector VarHash Ancestry Value ...)
(define (vtable-vh vv) (vector-ref vv 0))
(define (vtable-ancestry vv) (vector-ref vv 1))
(define VSTART 2)

;; create-rtif : Symbol Symbol (Listof Symbol)
;;               (Vectorof (U Contract #f)) DeriveProps VarHash
;;            -> RtInterface
(define (create-rtif iname uid supers vnames ctcv derives fallbacks)
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
  (rtif iname uid supers vnames
        ctcv in-ctcv out-ctcv fallbacks* vprop vprop? vprop-ref))

(define (make-interface-property iname vnames derives)
  (define (vprop-guard in-val st-info)
    (match-define (prop-val-wrapper initializer) in-val)
    (define super-stype (list-ref st-info 6))
    (define vh (initializer super-stype))
    (define super-anc
      (if (vprop? super-stype)
          (vtable-ancestry (vprop-ref super-stype))
          empty-ancestry))
    (apply vector-immutable vh (ancestry-extend super-anc)
           (for/list ([vname (in-list vnames)])
             (hash-ref vh vname))))
  (define-values (vprop vprop? vprop-ref)
    ;; workaround for racket/racket#5562
    ((values make-struct-type-property) iname vprop-guard derives))
  (values vprop vprop? vprop-ref))

(define (rtif-apply-out-ctcs ifc vs bnames neg-party loc)
  (define out-ctcv (rtif-out-ctcv ifc))
  (for/list ([v (in-list vs)]
             [bname (in-list bnames)]
             [staged-out-ctc (in-vector out-ctcv)])
    (staged-out-ctc v bname neg-party loc)))

;; rtif-get-stype-vh : RtInterface (U StructType #f) -> VarHash
(define (rtif-get-stype-vh ifc stype)
  (define vprop? (rtif-vprop? ifc))
  (define vprop-ref (rtif-vprop-ref ifc))
  (cond [(vprop? stype)
         (define vt (vprop-ref stype))
         (define anc (vtable-ancestry vt))
         (define vh (vtable-vh vt))
         (chaperone-super-vh vprop? vprop-ref anc vh)]
        [else (rtif-fallbacks ifc)]))

;; ----------------------------------------

(struct unimplemented (iname vname)
  #:property prop:procedure
  (make-keyword-procedure
   (lambda (kws kwargs self . args)
     (match-define (unimplemented iname vname) self)
     (error vname "not implemented\n  interface: ~a" iname))
   (lambda (self . args)
     (match-define (unimplemented iname vname) self)
     (error vname "not implemented\n  interface: ~a" iname))))

(define fallbacks/c (hash/c symbol? any/c))

;; ------------------------------------------------------------
;; Compile time

(begin-for-syntax
  ;; CtSig:
  (struct ctsig
    (name       ;; Identifier
     uid        ;; InterfaceKey
     rt         ;; Id[RtSig]
     supers     ;; (Listof CtSig)
     vnames     ;; (Listof Symbol)
     )
    #:property prop:custom-write
    (lambda (self out mode)
      (fprintf out "#<ctsig:~s>" (syntax-e (ctsig-name self))))
    #:property prop:procedure
    (lambda (self stx)
      ((make-variable-like-transformer (ctsig-rt self)) stx)))

  (define (ctsig-all-vnames sig)
    (define-values (all-sigs _h) (closure (list sig) (list #f) ctsig-supers))
    (apply append (map ctsig-vnames all-sigs)))

  (define (help-create-ctsig info-stx what)
    (define/with-syntax (name rtname (super-id ...) (vname ...) extra)
      info-stx)
    (define uid (string->uninterned-symbol (symbol->string (syntax-e #'name))))
    ;; FIXME: check no duplicate names
    (define supers (map syntax-local-value (datum (super-id ...))))
    (let ()
      (define seen (make-hasheq))
      (define-values (all-supers super-h) (closure supers supers ctsig-supers))
      (for ([sig (in-list all-supers)])
        (define osig (car (hash-ref super-h sig)))
        (for ([vname (in-list (ctsig-vnames sig))])
          (cond [(hash-ref seen vname #f)
                 => (lambda (osig1)
                      (raise-syntax-error
                       #f (format "duplicate name in ~a" what) #'name #f
                       (list (ctsig-name osig1) (ctsig-name osig))))]
                [else (hash-set! seen vname osig)])))
      (for ([vname (in-list (datum (vname ...)))])
        (cond [(hash-ref seen (syntax-e vname) #f)
               => (lambda (src1)
                    (raise-syntax-error
                     #f (format "duplicate name in ~a" what) #'name vname))]
              [else (hash-set! seen vname #t)])))
    (define vnames (syntax->datum #'(vname ...)))
    (values #'name uid #'rtname supers vnames #'extra))

  (define-syntax-class sig-ref
    #:attributes (value)
    (pattern (~var n (static ctsig? "name defined as interface or signature"))
             #:attr value (datum n.value))))

;; ----------------------------------------
;; Dependent Signatures

(begin-for-syntax
  ;; CtDepSig:
  (struct ctdepsig ctsig
    (;; supers  ;; always empty
     ))

  (define (create-ctdepsig info-stx)
    (define-values (iname uid rtname supers vnames extra)
      (help-create-ctsig info-stx "interface"))
    (ctdepsig iname uid rtname supers vnames))

  (define-syntax-class depsig-ref
    #:attributes (value)
    (pattern (~var n (static ctdepsig? "name defined as signature"))
             #:attr value (datum n.value))))

(define-syntax (define-signature stx)
  (define-syntax-class var-decl
    #:attributes (name ctce [dep 1])
    (pattern name:id
             #:with (dep ...) null
             #:with ctce #'#f)
    (pattern [name:id (~optional :contract-spec)]))
  (define-splicing-syntax-class contract-spec
    #:attributes (ctce [dep 1])
    (pattern (~seq #:dep (dep:id ...) ctc:expr)
             #:with ctce #'(cons (quote (dep ...))
                                 (lambda (dep ...)
                                   (coerce-contract 'define-signature ctc))))
    (pattern ctc:expr
             #:with (dep ...) null
             #:with ctce #'(coerce-contract 'define-signature ctc)))
  (syntax-parse stx
    [(_ signame:id (d:var-decl ...))
     (let ([dup (check-duplicates (datum (d.name ...)) #:key syntax-e)])
       (when dup (wrong-syntax dup "duplicate member name")))
     (let ([vnames (syntax->datum #'(d.name ...))])
       (for ([deps (in-list (datum ((d.dep ...) ...)))])
         (for ([dep (in-list deps)])
           (unless (memq (syntax-e dep) vnames)
             (wrong-syntax dep "not a signature member")))
         (let ([dup (check-duplicate-identifier deps)])
           (when dup (wrong-syntax dup "duplicate identifier in dependency list")))))
     (define/with-syntax (rtname) (generate-temporaries #'(signame)))
     (define/with-syntax (pre-def ...)
       ;; fixes unbound-identifier errors when used at top level
       (cond [(eq? (syntax-local-context) 'top-level)
              #'[(define-syntaxes (rtname) (values))]]
             [else null]))
     #'(begin
         pre-def ...
         (define-syntax signame
           (create-ctdepsig (quote-syntax (signame rtname () (d.name ...) ()))))
         (define rtname
           (create-rtdepsig-from-ctdepsig signame (vector-immutable d.ctce ...))))]))

(define-syntax (create-rtdepsig-from-ctdepsig stx)
  (syntax-parse stx
    [(_ sig:depsig-ref ctcv:expr)
     (match-define (ctdepsig signame uid _ _ vnames) (datum sig.value))
     (with-syntax ([signame signame] [uid uid] [vnames vnames])
       #'(create-rtdepsig (quote signame) (quote uid) (quote vnames) ctcv))]))

;; ----------------------------------------
;; Interfaces

(begin-for-syntax
  ;; CtInterface:
  (struct ctif ctsig
    (;; supers  ;; (Listof CtInterface)
     dnames     ;; (Listof Identifier) -- defined = (iname? gname ...)
     ))

  (define (create-ctif info-stx)
    (define-values (iname uid rtname supers vnames extra)
      (help-create-ctsig info-stx "interface"))
    (define/with-syntax (dname ...) extra)
    (ctif iname uid rtname supers vnames (datum (dname ...))))

  (define-syntax-class interface-ref
    #:attributes (value)
    (pattern (~var n (static ctif? "name defined as interface"))
             #:attr value (datum n.value))))

(define-syntax (define-interface stx)
  (define-syntax-class var-decl
    #:attributes (name src ctc)
    (pattern name:id
             #:with src #'name
             #:attr ctc #f)
    (pattern [name:id
              (~optional ctc:expr)]
             #:with src (datum->syntax #f (list #'name '....) this-syntax)))
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
         (~optional (~seq #:fallbacks (~var fallbacks (expr/c #'fallbacks/c)))
                    #:name "fallbacks clause")
         (~optional (~seq #:generics-prefix gprefix:id)
                    #:name "generics prefix clause")
         dc:derive-clause)
        ...)
     (define/with-syntax (rtname) (generate-temporaries #'(iname)))
     (define/with-syntax (vname ...) #'(d.name ...))
     (let ([dup (check-duplicates (datum (vname ...)) #:key syntax-e)])
       (when dup (wrong-syntax dup "duplicate member name")))
     (define/with-syntax (ctcname ...)
       (generate-temporaries (datum (vname ...))))
     (define/with-syntax iname?
       (or (datum predicate) (format-id #'iname "~a?" #'iname)))
     (define/with-syntax (gname ...)
       (cond [(datum gprefix)
              (for/list ([vname (in-list (datum (vname ...)))])
                (format-id vname "~a~a" #'gprefix vname))]
             [else #'(vname ...)]))
     (define/with-syntax (vctc? ...)
       (map syntax? (datum ((~? d.ctc #f) ...))))
     (define/with-syntax (pre-def ...)
       ;; fixes unbound-identifier errors when used at top level
       (cond [(eq? (syntax-local-context) 'top-level)
              #'[(define-syntaxes (rtname iname? gname ...) (values))]]
             [else null]))
     #'(begin
         pre-def ...
         (define-syntax iname
           (create-ctif
            (quote-syntax
             (iname rtname (s.super ...) (vname ...) (iname? gname ...)))))
         (define (iname? v) ;; define early, available for ctcs
           (and (not (struct-type? v)) ((rtif-vprop? rtname) v)))
         (define rtname
           (let ([ctcname (~? (coerce-contract 'define-interface d.ctc) #f)] ...)
             (create-rtif-from-ctif iname (vector-immutable ctcname ...)
                                    (~? fallbacks.c (hasheq))
                                    (list dc.kvpair ...))))
         (define-interface-generics iname ((vctc? gname vname) ...)))]))

(define-syntax (create-rtif-from-ctif stx)
  (syntax-parse stx
    [(_ ifc:interface-ref ctcv:expr fallbacks:expr derives:expr)
     (define ct (datum ifc.value))
     (match-define (ctif iname uid _ supers vnames _) (datum ifc.value))
     (with-syntax ([iname iname] [uid uid] [vnames vnames])
       (with-syntax ([(super-ifcvar ...) (map ctsig-rt supers)])
         #`(create-rtif (quote iname) (quote uid) (list super-ifcvar ...)
                        (quote vnames) ctcv derives fallbacks)))]))

(define-syntax (define-interface-generics stx)
  (syntax-parse stx
    [(_ iname:interface-ref ((ctc? gname vname) ...))
     (define ifc (datum iname.value))
     (define ctc?s (syntax->datum #'(ctc? ...)))
     (define/with-syntax rtname (ctsig-rt ifc))
     (define/with-syntax (uname ...) ;; unprotected
       (generate-temporaries #'(gname ...)))
     (define/with-syntax (bname ...)
       (for/list ([gname (in-list (datum (gname ...)))])
         (format-id #f "~a (generic)" gname #:source gname)))
     (cond [(eq? (syntax-local-context) 'module)
            (define/with-syntax (lname ...) ;; w/ staged out-contracts
              (generate-temporaries #'(gname ...)))
            (define/with-syntax (mname ...) ;; w/ module-boundary contracts
              (generate-temporaries #'(gname ...)))
            (define/with-syntax (quoted-mname-if-defined ...)
              (for/list ([mname (in-list (datum (mname ...)))]
                         [ctc? (in-list ctc?s)])
                (if ctc? #`(quote-syntax #,mname) #'(quote #f))))
            (define/with-syntax (mbc-def ...)
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
                      #:pos-source (quote (interface iname))))))
            #'(begin
                (define uname
                  (make-generic* rtname (quote vname) (quote gname) #f))
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
                ...)]
           [else
            ;; to make things "work" better at top-level, define gnames as
            ;; ordinary variables
            #'(begin
                (define uname
                  (make-generic* rtname (quote vname) (quote gname) #f))
                ...
                (define-values (gname ...)
                  (apply values
                         (rtif-apply-out-ctcs rtname (list uname ...) (quote (bname ...))
                                              (current-contract-region) #f))))])]))

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

(define-syntax interface-out
  (make-provide-transformer
   (lambda (stx modes)
     (syntax-parse stx
       [(_ iname:interface-ref)
        (define ifc (datum iname.value))
        (define/with-syntax (dname ...) (ctif-dnames ifc))
        (expand-export #'(combine-out iname dname ...) modes)]))))

;; ------------------------------------------------------------
;; Generic Functions

;; make-generic* : RtInterface Symbol Boolean
;;              -> (Instance Any ... -> Any) or #f
(define (make-generic* ifc seek-name name ctc?)
  (let loop ([ifc ifc])
    (or (for/first ([vname (in-list (rtsig-vnames ifc))]
                    [index (in-naturals VSTART)]
                    [staged-out-ctc (in-vector (rtif-out-ctcv ifc))]
                    #:when (eq? vname seek-name))
          (define iname (rtsig-name ifc))
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
        (ormap loop (rtsig-supers ifc)))))

;; ============================================================
;; Bundles

;; Linkage = (Hash LinkageKey (Box VarHash))
;; LinkageKey = (cons SigKey Tag)
;; Tag = (Listof Symbol)

;; TaggedSig = (cons RtSig Tag)
;; Two tags have special significance:
;; - '() -- default; exports with empty tag are bound to struct-type-properties
;; - '(super) -- reserved for importing super-struct or fallbacks implementation
;;               disallowed as export; automatically initialized by linker
;;               note: import super allowed even if no export to ifc in bundle

(define (tagged-sig? v)
  (and (pair? v) (rtsig? (car v)) (list? (cdr v)) (andmap symbol? (cdr v))))

(define (tagged-sig->linkage-key tsig)
  (match tsig [(cons sig tag) (cons (rtsig-uid sig) tag)]))

(define (tagged-sigs-closure tsigs)
  (define (get-next tsig)
    (match-define (cons sig tag) tsig)
    (map (lambda (sig) (cons sig tag)) (rtsig-supers sig)))
  (define-values (closed-tsigs _h) (closure tsigs tsigs get-next))
  closed-tsigs)

(define (tagged-sig->string tsig)
  ;; also accepts symbol in car
  (cond [(null? (cdr tsig)) (format "~.s" (car tsig))]
        [else (format "~.s #:tag (~.s)" (car tsig) (cdr tsig))]))

;; Bundle = Bundle1 | (compound-bundle (Listof BundlePart))
(define (bundle? v) (or (bundle1? v) (compound-bundle? v)))

(struct compound-bundle (parts)
  #:reflection-name 'bundle)
(struct bundle1
  (exports    ;; (Listof TaggedSig), closed
   imports    ;; (Listof TaggedSig), closed
   init!      ;; Linkage -> Void
   ) #:reflection-name 'bundle)

;; flatten-bundles : (Listof Bundle) -> (Listof Bundle1)
(define (flatten-bundles bs)
  (append* (for/list ([b (in-list bs)])
             (match b
               [(compound-bundle bs) (flatten-bundles bs)]
               [(? bundle1?) (list b)]))))

(define listof-bundle/c (listof bundle?))

(define (make-bundle* b1 bs)
  (if (null? bs) b1 (compound-bundle (append bs (list b1)))))

;; ----------------------------------------

(begin-for-syntax
  (struct impexp (ostx sig tag prefix excepts) #:transparent)

  (define-syntax-class export-spec
    #:attributes (ast)
    (pattern sig:sig-ref
             #:attr ast
             (let ([prefix (format-id #'sig "")])
               (impexp this-syntax (datum sig.value) '() prefix
                       (if (ctif? (datum sig.value)) #f null))))
    (pattern [sig:sig-ref
              (~alt
               (~optional (~seq #:tag (tagp:id ...))
                          #:name "tag clause")
               (~optional xc:export-except-clause
                          #:name "except clause")
               (~optional (~seq #:prefix prefix:id)
                          #:name "prefix clause"))
              ...]
             #:attr ast
             (let ([tag (syntax->datum #'(~? (tagp ...) ()))]
                   [excepts (datum (~? (xc.xname ...) #f))]
                   [prefix (or (datum prefix) (format-id #'sig ""))])
               (when (and excepts (pair? excepts))
                 (unless (ctif? (datum sig.value))
                   (wrong-syntax (car (datum xc)) "not allowed with signature"))
                 (define all-vnames (ctsig-all-vnames (datum sig.value)))
                 (for ([except-id (in-list excepts)])
                   (unless (memq (syntax-e except-id) all-vnames)
                     (wrong-syntax except-id "name is not member of interface or signature"))))
               (impexp this-syntax (datum sig.value) tag prefix
                       (if (ctif? (datum sig.value))
                           (and excepts (map syntax-e excepts))
                           null)))))

  (define-splicing-syntax-class export-except-clause
    #:attributes ([xname 1])
    (pattern (~seq #:all) #:with (xname ...) null)
    (pattern (~seq #:except (xname:id ...))))

  (define-syntax-class import-spec
    #:attributes (ast)
    (pattern sig:sig-ref
             #:attr ast
             (let ([prefix (format-id #'sig "")])
               (impexp this-syntax (datum sig.value) '() prefix #f)))
    (pattern [sig:sig-ref
              (~alt
               (~optional t:import-tag-clause
                          #:name "tag clause")
               (~optional (~seq #:prefix prefix:id)
                          #:name "prefix clause"))
              ...]
             #:attr ast
             (let ([tag (or (datum t.tag) null)]
                   [prefix (or (datum prefix)
                               (format-id #'sig (or (datum t.prefix) "")))])
               (impexp this-syntax (datum sig.value) tag prefix #f))))

  (define-splicing-syntax-class import-tag-clause
    #:attributes (tag prefix)
    (pattern (~seq #:super)
             #:attr tag '(super)
             #:attr prefix "super-")
    (pattern (~seq #:tag (t:id ...))
             #:attr tag (syntax->datum #'(t ...))
             #:attr prefix #f))

  (define (impexp->tsig ie) (cons (impexp-sig ie) (impexp-tag ie)))

  (define (ct-tsig-supers tsig)
    (match-define (cons sig tag) tsig)
    (map (lambda (v) (cons v tag)) (ctsig-supers sig)))

  (define (ct-tsig->string tsig)
    (match tsig
      [(cons sig '()) (format "~.s" (syntax-e (ctsig-name sig)))]
      [(cons sig tag) (format "~.s #:tag ~.s" (syntax-e (ctsig-name sig)) tag)]))

  ;; elaborate-impexps : (Listof ImpExp) String -> (Listof ImpExp)
  ;; Elaborate list to all super interfaces, check for consistency.
  (define (elaborate-impexps ies whats)
    (define-values (all-tsigs tsig=>ies)
      (closure (map impexp->tsig ies) ies ct-tsig-supers))
    ;; each tsig must have consistent prefix and except-list;
    ;; if so, map to one import (first occurring in BFS)
    (for/list ([tsig (in-list all-tsigs)])
      (define ies (reverse (hash-ref tsig=>ies tsig)))
      (define ie1 (car ies))
      (for ([ie2 (in-list (cdr ies))])
        (check-compat-impexps ie1 ie2 whats))
      (match-define (impexp ostx _ tag prefix excepts) ie1)
      (impexp ostx (car tsig) tag prefix excepts)))

  (define (check-compat-impexps ie1 ie2 whats)
    (define (tsig-string) (ct-tsig->string (impexp->tsig ie1)))
    (unless (bound-identifier=? (impexp-prefix ie1) (impexp-prefix ie2))
      (raise-syntax-error
       #f (format "incompatible ~a; prefixes differ\n  interface: ~a" whats (tsig-string))
       (current-syntax-context) #f (list (impexp-ostx ie1) (impexp-ostx ie2))))
    (unless (equal? (impexp-excepts ie1) (impexp-excepts ie2)) ;; FIXME: refine
      (raise-syntax-error
       #f (format "incompatible ~a; export exceptions differ\n  interface: ~a"
                  whats (tsig-string))
       (current-syntax-context) #f (list (impexp-ostx ie1) (impexp-ostx ie2)))))

  (define (check-impexps-for-collisions all-ies)
    ;; make sure each prefixed name has only one binding
    (define id=>ie (make-bound-id-table))
    (for ([ie (in-list all-ies)])
      (match-define (impexp ostx sig _ prefix _) ie)
      (for ([vname (in-list (ctsig-vnames sig))])
        (define id (format-id prefix "~a~a" prefix vname))
        (define already-ie (bound-id-table-ref id=>ie id #f))
        (when already-ie
          (raise-syntax-error
           #f (format "incompatible import/export\n  name collision: ~.s" (syntax-e id))
           (current-syntax-context) #f (list (impexp-ostx already-ie) ostx)))
        (bound-id-table-set! id=>ie id ie))))

  (define (impexp-extract ie)
    (match-define (impexp ostx sig tag prefix excepts) ie)
    (list #`(cons #,(ctsig-rt sig) (quote #,tag))
          prefix (ctsig-vnames sig) excepts ostx))

  (struct bctx (add-seen! exported-var? build-result))

  (define (make-bctx einfo-stx)
    (define/with-syntax ((eostx tsig-expr eprefix (evname ...) eexcepts) ...) einfo-stx)
    (define eostxs (datum (eostx ...)))
    (define etsigs (datum (tsig-expr ...)))
    (define eprefixes (datum (eprefix ...)))
    (define evnamess (syntax->datum #'((evname ...) ...)))
    (define eexceptss (syntax->datum #'(eexcepts ...)))
    (define lname=>vname (make-bound-id-table))
    (define lname=>t #f) ;; mutated, (FreeIdTable #t)
    (for ([eprefix (in-list eprefixes)]
          [evnames (in-list evnamess)]
          #:when #t
          [evname (in-list evnames)])
      (define localname (format-id eprefix "~a~a" eprefix evname))
      (bound-id-table-set! lname=>vname localname evname))
    (define vname=>ref (make-hasheq))
    (define prefixes* ;; (Listof (cons String Id)), de-duplicated
      (let* ([prefixes (remove-duplicates (datum (eprefix ...)) bound-identifier=?)])
        (filter values (for/list ([prefix (in-list prefixes)])
                         (define str (symbol->string (syntax-e prefix)))
                         (and (positive? (string-length str))
                              (cons str prefix))))))
    (define (prefixed-id? id) ;; starts with a prefix and has right scopes
      (define sym (syntax-e id))
      (define str (symbol->string sym))
      (for/or ([prefixp (in-list prefixes*)])
        (match-define (cons pstr pid) prefixp)
        (and (<= (string-length pstr) (string-length str))
             (equal? pstr (substring str 0 (string-length pstr)))
             (let ([id* (datum->syntax pid sym)])
               (bound-identifier=? id id*)))))
    ;; ----
    (define (add-seen! ids stx)
      (for ([id (in-list ids)])
        (cond [(bound-id-table-ref lname=>vname id #f)
               => (lambda (vname) (hash-set! vname=>ref vname id))]
              [(prefixed-id? id)
               (raise-syntax-error
                #f "defined name has export prefix but does not match any export" stx id)]
              [else (void)])))
    (define (exported-var? id)
      (unless lname=>t
        ;; must wait until pass2 to build free-id-table,
        ;; because identifier-binding-symbol may change
        (set! lname=>t (make-free-id-table))
        (for ([ref (in-hash-values vname=>ref)])
          (free-id-table-set! lname=>t ref #t)))
      (and (free-id-table-ref lname=>t id #f) #t))
    (define (build-result linkage-expr)
      (define/with-syntax linkage linkage-expr)
      #`(begin
          #,@(for/list ([eostx (in-list eostxs)]
                        [etsig (in-list etsigs)]
                        [evnames (in-list evnamess)]
                        [eexcepts (in-list eexceptss)])
               (define (excepted? name)
                 (and eexcepts (memq name eexcepts)))
               (define vname+index+lname-list
                 (for/list ([evname (in-list evnames)]
                            [index (in-naturals)])
                   (cond [(hash-has-key? vname=>ref evname)
                          (define lname
                            (syntax-local-introduce (hash-ref vname=>ref evname)))
                          (when (and eexcepts (memq evname eexcepts))
                            ;; error: defined but excepted
                            (raise-syntax-error
                             #f "member name is defined but in except-list"
                             eostx lname))
                          (list evname index lname)]
                         [(and eexcepts (not (memq evname eexcepts)))
                          ;; error: not defined (and not excepted)
                          (raise-syntax-error
                           #f (format "required member name is not defined: ~s" evname)
                           eostx)]
                         [else #f])))
               (define/with-syntax ((def-vname def-index def-lname) ...)
                 (filter values vname+index+lname-list))
               #`(do-export! linkage #,etsig (current-contract-region)
                             (quote-syntax #,eostx)
                             '(def-vname ...) '(def-index ...)
                             (list def-lname ...)))
          (void)))
    ;; ----
    (bctx add-seen!
          exported-var?
          build-result)))

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
     (define eies (elaborate-impexps (datum (~? (e.ast ...) ())) "exports"))
     (define iies (elaborate-impexps (datum (~? (i.ast ...) ())) "imports"))
     (check-impexps-for-collisions (append eies iies))
     (define/with-syntax ((etsig eprefix evnames eexcepts eostx) ...)
       (map impexp-extract eies))
     (define/with-syntax ((itsig iprefix ivnames _ iostx) ...)
       (map impexp-extract iies))
     #`(make-bundle*
        (bundle1
         (list etsig ...) (list itsig ...)
         (lambda (linkage)
           (define-names #:lazy iprefix ivnames itsig linkage iostx)
           ...
           (define-syntaxes (the-bctx)
             (make-bctx (quote-syntax ((eostx etsig eprefix evnames eexcepts) ...))))
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
          ((bctx-add-seen! ctx) vars ee))
        #'(define-values (var ...) (bundle-expr-wrap ctx-id rhs))]
       [(define-syntaxes ~! (var:id ...) . _)
        (let ([vars (syntax->list (syntax-local-introduce #'(var ...)))])
          ((bctx-add-seen! ctx) vars ee))
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
          (when ((bctx-exported-var? ctx) (syntax-local-introduce #'var))
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
     ((bctx-build-result ctx) #'linkage)]))

(define (do-export! linkage tsig impl-party src-stx vnames vindexes vvalues)
  (define sig (car tsig))
  (define lkey (tagged-sig->linkage-key tsig))
  (define vhbox (hash-ref linkage lkey))
  (define vh
    (cond [(rtif? sig)
           (define super-lkey (cons (car lkey) '(super)))
           (define supervh
             (let ([supervh (unbox (hash-ref linkage super-lkey))])
               (if (wrapped-super? supervh) (wrapped-super-ref supervh) supervh)))
           (define in-ctcv (rtif-in-ctcv sig))
           (for/fold ([vh supervh])
                     ([vname (in-list vnames)]
                      [vindex (in-list vindexes)]
                      [vvalue (in-list vvalues)])
             (define staged-in-ctc (vector-ref in-ctcv vindex))
             (define checked-value (staged-in-ctc vvalue #f impl-party src-stx))
             (hash-set vh vname checked-value))]
          [(rtdepsig? sig)
           (define vh0 (for/fold ([vh (hasheq)])
                                 ([vname (in-list vnames)]
                                  [vvalue (in-list vvalues)])
                         (hash-set vh vname vvalue)))
           (rtdepsig-apply-contracts sig vh0 #t impl-party src-stx)]))
  (set-box! vhbox vh))

(define-syntax (define-names stx)
  (syntax-parse stx
    [(_ mode prefix:id (vname:id ...) tsig:expr linkage:expr ostx)
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
              (do-import-strict tsig linkage (quote (vname ...))
                                (current-contract-region) (quote-syntax ostx) "import"))
            (define-syntax prefixedname
              (make-variable-like-transformer
               (quote-syntax varvar)))
            ...)]
       [(#:lazy)
        #`(begin
            (define varvar (box #f)) ...
            (define init!-box (box 'pre-init))
            (do-import-lazy! tsig linkage (quote (vname ...)) (list varvar ...) init!-box
                             (current-contract-region) (quote-syntax ostx))
            (define-syntax prefixedname
              (make-variable-like-transformer
               (quote-syntax
                (begin (let ([init! (unbox init!-box)])
                         (when init! (init! (quote prefixedname))))
                       (unbox varvar)))))
            ...)])]))

(define (do-import-strict tsig linkage vnames neg-party src-stx what)
  (define sig (car tsig))
  (define lkey (tagged-sig->linkage-key tsig))
  (define vh (unbox (hash-ref linkage lkey)))
  (define pos-party (list 'interface (rtsig-name sig)))
  (define src-stx (quote-syntax ostx))
  (cond [(rtif? sig)
         (define out-ctcv (rtif-out-ctcv sig))
         (apply values
                (for/list ([vname (in-list vnames)]
                           [staged-out-ctc (in-vector out-ctcv)])
                  (define v (hash-ref vh vname))
                  (define bname (format "~s (~a)" vname what))
                  (staged-out-ctc v bname neg-party src-stx)))]
        [else
         ;; FIXME: add arg for bname
         (define vh* (rtdepsig-apply-contracts sig vh #f neg-party src-stx))
         (apply values
                (for/list ([vname (in-list vnames)])
                  (hash-ref vh* vname)))]))

(define (do-import-lazy! tsig linkage vnames varboxes init!-box neg-party src-stx)
  (define lkey (tagged-sig->linkage-key tsig))
  (define vhbox (hash-ref linkage lkey))
  (define (init! who)
    (define sig (car tsig))
    (define pos-party (list 'interface (rtsig-name sig)))
    (define vh (unbox vhbox))
    (unless vh
      (error who "import not initialized\n  import: ~a"
             (tagged-sig->string tsig)))
    (cond [(rtif? sig)
           (for ([vname (in-list vnames)]
                 [varbox (in-list varboxes)]
                 [staged-out-ctc (in-vector (rtif-out-ctcv sig))])
             (define v (hash-ref vh vname))
             (define bname (format "~s (import)" vname))
             (define v* (staged-out-ctc v bname neg-party src-stx))
             (set-box! varbox v*))]
          [(rtdepsig? sig)
           ;; FIXME: add arg for bname
           (define vh* (rtdepsig-apply-contracts sig vh #f neg-party src-stx))
           (for ([vname (in-list vnames)]
                 [varbox (in-list varboxes)])
             (set-box! varbox (hash-ref vh* vname)))])
    (set-box! init!-box #f))
  (cond [(unbox vhbox) (init! #f)]
        [else (set-box! init!-box init!)]))

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
    (for/list ([export (in-list exports)]
               #:when (and (null? (cdr export))
                           (rtif? (car export))))
      (define ifc (car export))
      (define uid (rtsig-uid ifc))
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
;;                        -> (values (Listof TaggedSig)
;;                                   Linkage
;;                                   (StructType/#f -> Void))
(define (bundles-prepare-linkage who bs)
  (define exports (tagged-sigs-closure (append* (map bundle1-exports bs))))
  (define pre-linkage (build-linkage who bs))
  (define imported-super-ifcs (check-linkage who bs pre-linkage))
  (define super-ifcs
    (let ([exported-ifcs (remove-duplicates (filter rtif? (map car exports)))])
      (remove-duplicates (append exported-ifcs imported-super-ifcs))))
  (define linkage
    (for/fold ([linkage pre-linkage]) ([ifc (in-list super-ifcs)])
      (define super-lkey (cons (rtsig-uid ifc) '(super)))
      (hash-set linkage super-lkey (box #f))))
  (define (initialize-supers! stype)
    (for ([ifc (in-list super-ifcs)])
      (define super-vh (rtif-get-stype-vh ifc stype))
      (define super-lkey (cons (rtsig-uid ifc) '(super)))
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
    (define lkey (tagged-sig->linkage-key export))
    (cond [(super-linkage-key? lkey)
           (error who "illegal export with reserved super tag\n  export: ~a"
                  (tagged-sig->string export))]
          [(hash-ref linkage lkey #f)
           => (lambda (link-box)
                (error who "duplicate export: ~a"
                       (tagged-sig->string (unbox link-box))))]
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
    (define lkey (tagged-sig->linkage-key import))
    (cond [(super-linkage-key? lkey)
           (define sig (car import))
           (unless (rtif? sig)
             (error who "illegal import of signature with super tag\n  import: ~a"
                    (tagged-sig->string import)))
           (cons sig acc)]
          [(hash-has-key? linkage lkey) acc]
          [else (error who "import missing matching export\n  import: ~a"
                       (tagged-sig->string import))]))
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
    [(_ (~optional (~seq #:bind (e:import-spec ...)))
        (~var b (expr/c #'bundle?)) ...)
     (define eies (elaborate-impexps (datum (~? (e.ast ...) ())) "bindings"))
     (check-impexps-for-collisions eies)
     (define/with-syntax ((etsig eprefix evnames eostx _) ...)
       (map impexp-extract eies))
     #'(begin
         (define linkage
           (invoke-bundles* 'define/invoke-bundles (list etsig ...) (list b.c ...)))
         (define-names #:strict eprefix evnames etsig linkage eostx) ...
         (define-values () (begin (set! linkage #f) (values))))]))

;; invoke-bundles* : Symbol (Listof TaggedSig) (Listof Bundle) -> Void
;; PRE: binds is closed
(define (invoke-bundles* who binds bs0)
  ;; FIXME: check for var collisions
  (define bs (flatten-bundles bs0))
  (define-values (exports linkage initialize-supers!)
    (bundles-prepare-linkage 'invoke-bundles bs))
  (for ([bind (in-list binds)])
    (define lkey (tagged-sig->linkage-key bind))
    (unless (hash-has-key? linkage lkey)
      (error 'invoke-bundles "~a\n  tagged signature: ~a"
             "tagged signature not exported"
             (tagged-sig->string bind))))
  (initialize-supers! #f)
  (run-bundles bs linkage)
  linkage)


;; ============================================================
;; Struct Abbrevs

(define-syntax (define-struct-abbrevs stx)
  (syntax-case stx ()
    [(_ sname)
     (with-disappeared-uses
       (define (bad-sname)
         (raise-syntax-error #f "named defined as struct type" stx))
       (unless (identifier? #'sname) (bad-sname))
       (define info (syntax-local-value/record #'sname struct-info?))
       (unless info (bad-sname))
       (define infolist (extract-struct-info info))
       (define accessors (list-ref infolist 3))
       (define mutators (list-ref infolist 4))
       (define fields
         (let loop ([info info] [infolist infolist])
           (cond [(struct-field-info? info)
                  (define immediate-fields
                    (struct-field-info-list info))
                  (define super-name
                    (list-ref infolist 5))
                  (define super-info
                    (and (identifier? super-name)
                         (syntax-local-value super-name)))
                  (define super-infolist
                    (and super-info (extract-struct-info super-info)))
                  (append immediate-fields
                          (loop super-info super-infolist))]
                 [else null])))
       (define/with-syntax ((getter accessor) ...)
         (for/list ([accessor (in-list accessors)]
                    [field (in-list fields)]
                    #:when (identifier? accessor))
           (list (format-id stx ".~a" field) accessor)))
       (define/with-syntax ((setter mutator) ...)
         (for/list ([mutator (in-list mutators)]
                    [field (in-list fields)]
                    #:when (identifier? mutator))
           (list (format-id stx ".~a-set!" field) mutator)))
       #'(begin (define-syntax getter
                  (make-rename-transformer (quote-syntax accessor)))
                ...
                (define-syntax setter
                  (make-rename-transformer (quote-syntax mutator)))
                ...))]))

;; ============================================================
;; Ancestry

;; Ancestry = (vector Any ...), where if any two ancestries match at
;; index k, they also match at every index less than k.

(define empty-ancestry (vector-immutable))

(define (ancestor? a1 a2)
  (define n (vector-length a1))
  (and (>= (vector-length a2) n)
       (eq? (vector-ref a1 (sub1 n)) (vector-ref a2 (sub1 n)))))

(define (ancestry-extend anc [last-v (box 0)])
  (vector->immutable-vector
   (vector-extend anc (add1 (vector-length anc)) last-v)))

;; ============================================================
;; Contract utilities

;; contract for checking implementations of an interface member
(define (impl/c vname ctc)
  (define ctc-get-proj (get/build-late-neg-projection ctc))
  (define ctc-get-col-proj (get/build-collapsible-late-neg-projection ctc))
  (define important (format "~a (impl)" vname))
  (define message "the interface member's contract")
  (make-contract
   #:name (contract-name ctc)
   #:first-order (contract-first-order ctc)
   #:collapsible-late-neg-projection
   (lambda (blame)
     (define swapped-blame
       ;; #:important resets blame to "produced"!
       (blame-add-context blame message #:important important #:swap? #t))
     (ctc-get-col-proj blame))
   #:late-neg-projection
   (lambda (blame)
     (define swapped-blame
       ;; #:important resets blame to "produced"!
       (blame-add-context blame message #:important important #:swap? #t))
     (ctc-get-proj swapped-blame))
   #:list-contract? (list-contract? ctc)))

;; stage-contract : (U Contract #f) Party -> (Any Any Party Location -> Any)
(define (stage-contract ctc pos-party)
  ;; pos-party represents interface
  (cond [ctc
         (lambda (value value-name neg-party loc)
           (contract ctc value pos-party neg-party value-name loc))]
        [else
         (lambda (value value-name neg-party src)
           value)]))

;; ----------------------------------------
;; Protecting super methods

;; Importing [ifc #:super] gives access to super methods; may be misused by
;; being applied to targets that are not instances of super struct
;; type. Protect super vh in linkage using chaperone; unprotect using
;; impersonator property when composing new vh to avoid unnecessary wrapping.

(define-values (prop:wrapped-super wrapped-super? wrapped-super-ref)
  (make-impersonator-property 'wrapped-super))

(define (chaperone-super-vh prop? prop-ref anc vh)
  (define wrap-method (make-chaperone-super-method prop? prop-ref anc))
  (define (wrap-value h k v) (wrap-method v))
  (define (wrap-ref h k) (values k wrap-value))
  (define (wrap-set h k v) (error 'chaperone-super-vh "set not implemented"))
  (define (wrap-remove h k) (error 'chaperone-super-vh "remove not implemented"))
  (define (wrap-key h k) k)
  (chaperone-hash vh wrap-ref wrap-set wrap-remove wrap-key #f #f
                  prop:wrapped-super vh))

;; make-super-chaperone : ... -> Procedure -> Procedure
;; Make chaperone wrapper that checks first argument has correct ancestry.
(define (make-chaperone-super-method prop? prop-ref anc)
  (define (ok-first-arg? obj)
    (and (prop? obj)
         (let ([obj-anc (vtable-ancestry (prop-ref obj))])
           (ancestor? anc obj-anc))))
  (lambda (f)
    (define fname (object-name f))
    (define (wrapper obj . args)
      (unless (ok-first-arg? obj)
        (error fname "bad target for super method: ~e" obj))
      (apply values obj args))
    (define kw-wrapper
      (make-keyword-procedure
       (lambda (kws kwargs obj . args)
         (unless (ok-first-arg? obj)
           (error fname "bad target for super method: ~e" obj))
         (apply values kwargs obj args))
       wrapper))
    (cond [(procedure? f)
           (define-values (req-kws opt-kws) (procedure-keywords f))
           (cond [(null? opt-kws) (chaperone-procedure f wrapper)]
                 [else (chaperone-procedure f kw-wrapper)])]
          [else f])))
