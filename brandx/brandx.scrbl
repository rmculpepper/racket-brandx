#lang scribble/manual
@(require scribble/example
          (for-label racket/base racket/match racket/math
                     racket/contract/base brandx)
          (for-label (only-in racket/class
                              this abstract augment inner override)))
@(begin
  (define the-eval (make-base-eval))
  (the-eval '(require racket/match racket/math racket/contract/base brandx)))

@; ----------------------------------------
@title[#:tag "brandx"]{BrandX: Generics, Interfaces, and Components}

@defmodule[brandx]

This library, @racketmodname[brandx], is another library for
@bold{generics} in Racket. It provides features similar to
@racketmodname[racket/generic] and @racketmodname[racket/class], but
it does not interoperate with either. It can also replace simple uses
of @racketmodname[racket/unit].

@; ============================================================
@section{Introduction}



@examples[#:eval the-eval #:label #f
(define-interface shape
  ([contains? (-> shape? real? real? boolean?)]
   [area (-> shape? (>=/c 0))]))
]

@examples[#:eval the-eval #:label #f
(struct circle (xc yc r)
  #:properties
  (method-properties
   #:export ([shape #:prefix %])

   (define (%area self)
     (define r (circle-r self))
     (* pi r r))

   (define (%contains? self x y)
     (<= (dist-from-center self x y) (circle-r self)))

   (define (dist-from-center self x y)
     (match-define (circle xc yc _) self)
     (sqrt (+ (sqr (- x xc)) (sqr (- y yc)))))
   ))
]

@examples[#:eval the-eval #:label #f
(struct rectangle (x1 y1 x2 y2)
  (code:comment "x1 <= x2, y1 <= y2")
  #:properties
  (method-properties
   #:export ([shape #:prefix %])

   (define (%area self)
     (match-define (rectangle x1 y1 x2 y2) self)
     (* (- x2 x1) (- y2 y1)))

   (define (%contains? self x y)
     (match-define (rectangle x1 y1 x2 y2) self)
     (and (<= x1 x x2) (<= y1 y y2)))
   ))
]

@examples[#:eval the-eval #:label #f
(struct union (s1 s2)
  #:properties
  (method-properties
   #:export ([shape #:prefix %])

   (define (%contains? self x y)
     (match-define (union s1 s2) self)
     (or (contains? s1 x y) (contains? s2 x y)))
   ))
]

@examples[#:eval the-eval #:label #f
(contains? (circle 0 0 10) 3 4)
(area (rectangle 1 2 11 22))
(eval:error (area 'line))
(eval:error (area (rectangle 1 2 0 10)))
]

@; ----------------------------------------
@subsection[#:tag "intro-components"]{Components}

@examples[#:eval the-eval #:label #f
(define-interface worklist
  ([empty any/c]
   [empty? (-> any/c boolean?)]
   [enqueue (-> any/c any/c any/c)]
   [dequeue (-> any/c (values any/c any/c))])
  #:no-generics)

(define queue@
  (bundle
   #:export ([worklist #:prefix %])
   (struct queue (r w))
   (define %empty (queue null null))
   (define (%empty? q)
     (match q [(queue '() '()) #t] [_ #f]))
   (define (%enqueue q v)
     (match q
       [(queue r w) (queue r (cons v w))]))
   (define (%dequeue q)
     (match q
       [(queue (cons v r) w) (values v (queue r w))]
       [(queue '() '()) (error 'remove "empty queue")]
       [(queue '() w) (%dequeue (queue (reverse w) '()))]))))

(define stack@
  (bundle
   #:export ([worklist #:prefix %])
   (define %empty null)
   (define %empty? null?)
   (define (%enqueue st v) (cons v st))
   (define (%dequeue st)
     (match st [(cons v st) (values v st)]))))

(define-interface traversal
  ([traverse (-> any/c (-> any/c (listof any/c)) (listof any/c))])
  #:no-generics)

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

   (define (enqueue-all q xs)
      (for/fold ([q q]) ([x (in-list xs)]) (enqueue q x)))
   ))

(define (halfsies n)
  (define half (quotient n 2))
  (cond [(<= n 1) null]
        [(even? n) (list half)]
        [else (list half (add1 half))]))

(define/invoke-bundles #:export ([traversal #:prefix bfs:]) queue@ traversal@)
(define/invoke-bundles #:export ([traversal #:prefix dfs:]) stack@ traversal@)

(bfs:traverse 100 halfsies)
(dfs:traverse 100 halfsies)
]


@; ----------------------------------------
@subsection[#:tag "comparison"]{Comparison with Other Libraries}

Improvements over @racketmodname[racket/generic]: This library has better
binding ergonomics: implementations may use export prefixes to avoid shadowing
generic functions, and multiple interfaces may be implemented in a single
shared definition scope. Contracts are associated with interface members, and
interface imports and exports are contract boundaries, but there are no
instance contracts. This library supports method overriding with calls to
super-methods.

Limitations compared to @racketmodname[racket/generic]: This library's generic
functions always dispatch on their first positional argument, and they do not
support ``defaults'' (instead, define a wrapper function).

Differences from @racketmodname[racket/class]: Users retain direct access to
structs, including pattern-matching via @racket[match]. All method names to be
visible externally or visible to subclasses must be declared in an
interface. There is no syntactic restriction or special treatment of methods;
in particular, there is no implicit @racket[this] variable. Consequently,
there is no syntactic support for treating fields as variables, and there is
no special treatment of calls on the same object. There is no special
construction/initialization support. There is no support for augmentable
methods (@racket[augment], @racket[inner]).


@; ----------------------------------------
@section[#:tag "interface"]{Interfaces}

@defform[(define-interface iname maybe-supers maybe-predicate
           (member-decl ...) clause ...)
         #:grammar
         ([maybe-supers (code:line)
                        (code:line #:super (super-interface-id ...))]
          [maybe-predicate (code:line)
                           (code:line #:predicate predicate-id)]
          [member-decl member-id
                       [member-id maybe-contract]]
          [maybe-contract (code:line)
                          contract-expr]
          [clause (code:line #:fallbacks fallbacks-table-expr)
                  (code:line #:no-generics)
                  (code:line #:generics-prefix prefix-id)])]{

Defines an interface named @racket[iname] with the given
members. Specifically, the following names are defined:
@itemlist[

@item{@svar[iname] --- The interface. When an interface name is used in
expression position, it evaluates to the interface's run-time representation.}

@item{@svar[predicate-id], if given, or else @svar[iname?] --- A
predicate that recognizes instances of struct implementing the
interface.}

@item{@svar[member-id], prefixed with @svar[prefix-id], if given --- A
generic function for each member of the interface. If the
@racket[#:no-generics] option was given, no generics are defined.}

]

If the @racket[#:super] clause is given, then each @racket[super-interface-id]
must be the name of a previously-defined interface, and the interface
@racket[iname] extends the given interfaces. That is, an import or export of
the interface implicitly imports or exports all of its super-interfaces as
well.

The members of the interface are named according to the
@racket[member-id]s. If a member has a contract, the contract protects
the generic function as well as any import or export of the interface
member.

If a @racket[#:fallbacks] clause is present, then
@racket[fallbacks-table-expr] must evaluate to a hash mapping member name
symbols to their fallback implementations. Any member that is not given a
fallback implementation has a default fallback value, recognized by
@racket[unimplemented?], which raises an error when applied. Fallbacks cannot
be given for super-interface names.

By default, a generic function is defined for every member name. If a
@racket[#:no-generics] clause is given, then no generics are
defined. If a @racket[#:generics-prefix] clause is given, then the
generic function names are formed by adding the given prefix to the
beginning of the member name.
}

@defproc[(interface? [v any/c]) boolean?]{

Returns @racket[#t] is @racket[v] is a run-time interface representation,
@racket[#f] otherwise.
}

@defproc[(unimplemented? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a default fallback implementation
procedure created by @racket[define-interface], @racket[#f] otherwise. A
default fallback procedure accepts any number of arguments and raises an
``unimplemented'' error.
}

@defproc[(interface->predicate [ifc interface?]
                               [name (or/c symbol? #f) #f]
                               [#:accept-struct-type? accept-struct-type?
                                                      boolean? #f])
         (-> any/c boolean)]{

Returns a predicate that recognizes instances of @racket[ifc]. If
@racket[accept-struct-type?] is false (the default), then the predicate only
accepts instances of structs implementing @racket[ifc]; if it is true, then
the predicate also accepts struct type descriptors for structs implementing
@racket[ifc].

If @racket[name] is a symbol, then @racket[name] must be a member name of
@racket[ifc], and the predicate is further constrained to only accept
instances where that member name has a value that is not
@racket[unimplemented?].
}

@;{
@defproc[(make-generic [ifc interface?]
                       [name symbol?])
         procedure?]{

Returns a generic function that, when applied, looks up the method associated
with the @racket[name] member of interface @racket[ifc], and calls it. If
@racket[name] is not a member name of @racket[ifc], then an error is signaled.
}}

@defform[(interface-out interface-id)]{

Exports the bindings associated with the interface named by
@racket[interface-id]. Those bindings are @racket[interface-id] itself, the
interface's predicate, and the generic functions (unless the interface was
defined with @racket[#:no-generics]).
}

@; ============================================================
@section[#:tag "bundles"]{Bundles}

Interfaces are implemented by @deftech{bundles}, which are created with the
@racket[bundle] form and may be invoked using @racket[define/invoke-bundles]
or, more typically, attached to a struct type using
@racket[bundles->properties]. The @racket[method-properties] form provides a
convenient combination of @racket[bundles->properties] and @racket[bundle].

@defproc[(bundle? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a bundle, @racket[#f] otherwise.
}

@defform[(bundle link-clause ... definition-or-expression ...)
         #:grammar
         ([link-clause (code:line #:export (export-spec ...))
                       (code:line #:import (import-spec ...))
                       (code:line #:link bundle-list-expr)]
          [export-spec interface-id
                       [interface-id maybe-tag maybe-prefix]]
          [import-spec interface-id
                       [interface-id maybe-tag/super maybe-prefix]]
          [maybe-tag (code:line)
                     (code:line #:tag (id ...))]
          [maybe-tag/super maybe-tag
                           (code:line #:super)]
          [maybe-prefix (code:line)
                        (code:line #:prefix prefix-id)])]{

Produces a @tech{bundle} with the given exports, imports, linked bundles, and
definitions.

The @racket[#:export] clause declares what the bundle implements. An export
consists of an interface name, an optional tag, and an optional prefix. The
export is satisfied by definitions in the bundle's body matching the names of
the interface members, prefixed by the export prefix, if given. An export of
an interface also includes all of its super-interfaces.

If an export contains a non-empty prefix, then any definition in the bundle
body of a name matching that prefix (and set of scopes) must correspond to an
exported member name, otherwise an error is signaled. (This check helps
prevent typos from causing missed exports.)

The @racket[#:import] clause declares the bundle's imports. Like an export, an
import consists of an interface name, an optional tag, and an optional
prefix. The special import form @racket[[interface-id #:super]] is equivalent
to @racket[[interface-id #:tag (super) #:prefix super-]].

Imports and exports allow tags to distinguish between multiple occurrences of
the same interface in the linkage graph. An import in one bundle matches an
export in another bundle only if both the interface and tag matches. The
default tag is @racket[()]. The tag @racket[(super)] is special; it is
forbidden as an export tag, and as an import it is automatically satisfied by
the linker using the implementation from the struct super-type (if applicable)
or the interface's fallbacks.

If a @racket[#:link] clause is present, then @racket[bundle-list-expr] must
evaluate to a list of bundles. The linked bundles are included in the linkage
graph when the enclosing bundle is linked and invoked. They may satisfy
imports and consume exports of the enclosing bundle, but their imports and
exports must not be duplicated in the @racket[#:import] and @racket[#:export]
clauses of the enclosing bundle. When the bundle is invoked, the linked
bundles are invoked in order before the body is evaluated.

Depending on the link order, a bundle may have imports that are not fully
initialized by the time the bundle body is evaluated. In the typical case
where the bundle only defines functions that refer to imports, there is no
problem, but if the bundle attempts to evaluate an imported member name during
initialization, it will fail if the member is exported from a bundle that has
not yet been initialized.
}

@;{
@defproc[(make-bundle [#:export exports (listof tagged-interface/c) null]
                      [#:import imports (listof tagged-interface/c) null]
                      [#:link linked-bundles (listof bundle?) null]
                      [make-table
                       (-> (-> tagged-interface/c symbol? any/c)
                           (hash/c symbol? any/c))])
         bundle?]{}
}

@defproc[(bundles->properties [b bundle?] ...)
         (listof (cons/c struct-type-property? any/c))]{

Links the bundles @racket[(list b ...)] and returns an association list for
the exported interfaces' underlying struct type properties, suitable for the
@racket[#:properties] argument of the @racket[struct] form. Invocation of the
linked bundles is delayed until the struct is created, so that super
implementations can be populated from the struct's super type.
}

@defform[(method-properties link-clause ... definition-or-expression ...)]{

Equivalent to @racketblock[
(bundles->properties (bundle link-clause ... definition-or-expression ...))
]}

@defform[(define/invoke-bundles #:export (export-spec ...) bundle-expr ...)]{

Links the bundles @racket[(list bundle-expr ...)], invokes them, and defines
names according to the @racket[export-spec]s.
}

@defproc[(dynamic-invoke-bundles [b bundle?] ...
                                 [#:bind binds (listof tagged-interface/c)]
                                 [#:flatten? flatten? boolean? #t])
         (if/c flatten?
               (hash/c symbol? any/c)
               (hash/c tagged-interface/c (hash/c symbol? any/c)))]{

Links the bundles @racket[(list b ...)] and invokes them. If @racket[flatten?]
is true, then the result is a hash mapping all of the member names from all of
the interfaces in @racket[binds] to their corresponding values. If
@racket[flatten?] is false, then the result is a hash mapping each tagged
interface in @racket[binds] to a hash for that interface's names (including
those of its super-interfaces).
}



@; ----------------------------------------
@(close-eval the-eval)
