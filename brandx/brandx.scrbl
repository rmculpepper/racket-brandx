#lang scribble/manual
@(require scribble/example
          (for-label racket/base racket/match racket/math racket/struct-info
                     racket/contract brandx
                     (only-in racket/class
                              class this abstract augment inner override ->m)
                     (only-in racket/generic
                              redirect-generics)))
@(begin
  (define the-eval (make-base-eval))
  (the-eval '(require racket/match racket/math racket/contract brandx)))

@; ----------------------------------------
@title[#:tag "brandx"]{BrandX: Generics, Interfaces, and Components}

@defmodule[brandx]

This library supports object-oriented and interface-oriented programming via
@bold{generic} functions. It provides features similar to
@racketmodname[racket/generic] and @racketmodname[racket/class], and it can
also replace simple uses of @racketmodname[racket/unit], but it does not
interoperate with any of those libraries. See also @secref["comparison"].

@section-index["object-oriented programming"
               "interface-oriented programming"]

@; ============================================================
@section{Introduction}

This section introduces @racketmodname[brandx] interfaces, generic functions,
and their implementations as methods associated with @racket[struct]
declarations. The first example uses the domain of simple geometric shapes.

First we define a @racket[shape] interface with two members. Defining the
interface also defines a predicate @racket[shape?] and a generic function for
each interface member: @racket[contains?] and @racket[area].

@examples[#:eval the-eval #:no-prompt #:label #f
(define-interface shape
  ([contains? (-> shape? real? real? boolean?)]
   [area (-> shape? (>=/c 0))]))
]

Contracts are optional, but if present they should be ordinary function
contracts (use @racket[->], @racket[->*], etc; do not use
@racket[->m]). Contracts do not affect dispatch; this library's generic
functions always dispatch on the first positional argument, so the first
argument contract should generally be the interface predicate. (This library
does not support multiple dispatch.)

The interface is implemented by attaching methods to a @racket[struct]
declaration using @racket[#:properties] and the @racket[method-properties]
form. The @racket[#:export] clause declares the interfaces being
implemented---just one, @racket[shape]. Within the export, the @racket[#:all]
option requires that every interface member has a corresponding method
definition, and the @racket[#:prefix %] option indicates that the method
implementations are named by prefixing the interface member name with
@racket[%]---this avoids shadowing the generic functions. It is almost always
a mistake to call an export-prefixed name; use the generic function instead.
@margin-note{The implementation is implicitly packaged as a @tech{bundle}; the
@racket[method-properties] form is a convenient composition of
@racket[bundles->properties] and the @racket[bundle] form. Bundles are the
units of implementation corresponding to interfaces and signatures.}

@examples[#:eval the-eval #:no-prompt #:label #f
(struct rectangle (x1 y1 x2 y2) (code:comment "x1 <= x2, y1 <= y2")
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
]

Note that each method has an explicit @racket[self] argument. The argument
name does not matter; the name @racket[self] is just a convention. Unlike a
@racket[class] method, there is no special treatment of @racket[self], and
there is no automatic access to object fields.

Calling the generic function on a @racket[rectangle] instance dispatches to
the @racket[rectangle] method:

@examples[#:eval the-eval #:label #f
(contains? (rectangle 0 0 10 20) 5 12)
(area (rectangle 1 2 11 22))
]

The interface contracts protect the generic functions from misuse:

@examples[#:eval the-eval #:label #f
(eval:error (contains? (rectangle 0 0 10 20) 0 'center))
]

The interface contracts also protect callers from incorrect
implementations. For example, the @racket[rectangle] struct type does not
enforce the constraint @racket[(<= x1 x2)], so if we construct a bad rectangle
and ask its area, we get a contract error blaming the implementation:

@examples[#:eval the-eval #:label #f
(eval:error (area (rectangle 5 0 0 10)))
]

Here is another @racket[shape] implementation:

@examples[#:eval the-eval #:label #f
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
]

This implementation uses @racket[define-struct-abbrevs] to make field access
more convenient, by defining @racket[.xc] as an alias of @racket[circle-xc],
and so on. This example also shows the use of helper functions,
@racket[dist-from-center] and @racket[dist]. The @racket[dist] function could
just as well have been defined outside of the @racket[method-properties] body;
the @racket[dist-from-center] function could be moved outside also, but then
it would be outside the scope of the @racket[define-struct-abbrevs] aliases,
so it would need to be adjusted.

Since the helper functions are not interface members, they can be named nearly
anything, @emph{except} that the export prefix declaration reserves all names
starting with @racket[%] for exports. The restriction affects all names
defined immediately within the methods block. So for example, if @racket[dist]
were renamed to @racket[%dist], a syntax error would be raised. (This
restriction helps prevent typos in intended export names from silently being
ignored.)

Shape operations on circles work as expected:

@examples[#:eval the-eval #:label #f
(contains? (circle 0 0 10) 3 4)
(area (circle 0 0 1))
]

Here is another @racket[shape] implementation:

@examples[#:eval the-eval #:no-prompt #:label #f
(struct union (s1 s2)
  #:properties
  (method-properties
   #:export ([shape #:prefix %])

   (define (%contains? self x y)
     (match-define (union s1 s2) self)
     (or (contains? s1 x y) (contains? s2 x y)))
   ))
]

It is difficult to calculate the area of overlapping shapes, and it is
impossible to reliably detect overlap using only the members of the
@racket[shape] interface anyway. So @racket[union] is a @emph{partial}
implementation of the @racket[shape] interface: it does not define a
@racket[area] method. Note the absence of the @racket[#:all] export option. If
it were present, a syntax error would raised because of the missing
definition. To enforce that @racket[area] is the only missing definition, an
``except'' clause, @racket[#:except (area)], could be used instead.

A @racket[union] instance is considered a @racket[shape], and it works as
expected with the @racket[contains?] generic:

@examples[#:eval the-eval #:label #f
(shape? (union (circle 0 0 1) (rectangle 0 0 1 1)))
(contains? (union (circle 0 0 1) (rectangle 0 0 1 1)) 1/2 1/2)
]

A call to the @racket[area] generic function gets the method from
@racket[union]'s ``super-implementation'', which is the @racket[shape]
interface's fallbacks. Every interface member has a default fallback
implementation which is a procedure that raises an ``unimplemented'' error:

@examples[#:eval the-eval #:label #f
(eval:error (area (union (circle 0 0 1) (rectangle 0 0 1 1))))
]

We can further ``subclass'' the @racket[union] shape with a struct type that
we promise to use only if we know through other means that the shapes are
disjoint:

@examples[#:eval the-eval #:no-prompt #:label #f
(struct disjoint-union union ()
  (code:comment "sub-shapes must be disjoint; not checked!")
  #:properties
  (method-properties
   #:export ([shape #:except (contains?) #:prefix %])
   (define-struct-abbrevs disjoint-union)

   (define (%area self)
     (+ (area (.s1 self)) (area (.s2 self))))
   ))
]

Then calls to @racket[contains?] inherit the method from @racket[union] and
calls to @racket[area] get the new implementation:

@examples[#:eval the-eval #:label #f
(contains? (disjoint-union (rectangle 0 0 1 1) (rectangle 1 1 2 2)) 1/2 1/2)
(area (disjoint-union (rectangle 0 0 1 1) (rectangle 1 1 2 2)))
]

@; ----------------------------------------
@subsection[#:tag "intro2"]{Multiple Interfaces and Instance Contracts}

This section illustrates additional features and patterns---multiple interface
exports and instance contracts---using an example based on animals. We'll use
two behaviors of animals for this example, making noise and eating. Rather
than defining a single interface, let's define separate interfaces, one for
each kind of behavior. The @racket[can-greet] interface is simple:

@examples[#:eval the-eval #:no-prompt #:label #f
(define-interface can-greet
  ([greet (-> can-greet? string?)]))
]

The interface for eating is more complicated. Different animals eat different
kinds of foods, and it is wrong to feed them food that they cannot eat. Unlike
the @racketmodname[racket/generic] library, @racketmodname[brandx] does not
support attaching contracts to instances that affect the behavior of generic
functions (via @racket[redirect-generics], for example). But a different kind
of instance-specific contracts can be enforced using generic functions and
dependent function contracts. For example, each animal can implement a
@racket[get-food/c] method that produces a contract describing its allowed
food. Then the @racket[eat] operation has a dependent contract that
dynamically fetches the instance's specific food contract using the
@racket[get-food/c] generic function:

@examples[#:eval the-eval #:no-prompt #:label #f
(define-interface can-eat
  ([get-food/c (-> can-eat? contract?)]
   [eat (->i ([self can-eat?]
              [food (self) (get-food/c self)])
             [_ void?])]))
]

A dog can both make noise and eat:

@examples[#:eval the-eval #:no-prompt #:label #f
(struct dog (veg? [weight #:mutable] [happiness #:mutable])
  #:transparent
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %]
             [can-eat #:all #:prefix %])
   (define-struct-abbrevs dog)
   (define (%greet self) (if (>= (.weight self) 10) "woof" "bark"))
   (define (%get-food/c self)
     (or/c 'dog-food 'treat (if (.veg? self) 'carrot 'cheese)))
   (define (%eat self food)
     (case food
       [(treat) (.happiness-set! self (add1 (.happiness self)))]
       [else (.weight-set! self (add1 (.weight self)))]))))
]

Note that multiple exports may use the same export prefix, as above, or they
may use different export prefixes.

@examples[#:eval the-eval #:label #f
(define barkly (dog #f 8 5))
(greet barkly)
(eat barkly 'dog-food)
(eat barkly 'cheese)
(eat barkly 'treat)
barkly
(greet barkly)
(eval:error (eat barkly 'lettuce))
]

@; ----------------------------------------
@subsection[#:tag "intro3"]{Super Calls and Mixins}

A noisy dog makes three times as much noise as a regular dog. We can define a
@racket[noisy-dog] struct type that overrides the @racket[greet] method and
calls its super-implementation (the method from @racket[dog]) as a helper. To
get access to super-implementations, we use an @racket[#:import] clause with
the @racket[#:super] tag.

@examples[#:eval the-eval #:no-prompt #:label #f
(struct noisy-dog dog ()
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %])
   #:import ([can-greet #:super])
   (define (%greet self)
     (define greeting (super-greet self))
     (string-append greeting " " greeting " " greeting))))
]

Here is a noisy dog at work:

@examples[#:eval the-eval #:label #f
(define princess (noisy-dog #t 2 1))
(greet princess)
(eat princess 'treat)
]

Notice, however, that the implementation of noisiness had nothing to do with
the @racket[dog] or @racket[noisy-dog] struct type. We can extract the
``noisiness'' behavior into a separate ``mixin'' bundle. (A mixin bundle is
similar to a mixin in @racketmodname[racket/class], but a mixin bundle cannot
define fields.)

@examples[#:eval the-eval #:label #f
(define noisy@
  (bundle
   #:export ([can-greet #:all #:prefix %])
   #:import ([can-greet #:super])
   (define (%greet self)
     (define greeting (super-greet self))
     (string-append greeting " " greeting " " greeting))))
]

Then if we have another kind of animal...

@examples[#:eval the-eval #:no-prompt #:label #f
(struct cat ()
  #:properties
  (method-properties
   #:export ([can-greet #:all #:prefix %]
             [can-eat #:all #:prefix %])
   (define (%greet self) "meow")
   (define (%get-food/c self) (or/c 'cat-food 'fish 'bird 'mouse))
   (define (%eat self food) (void))))
]

we can make a noisy version by simply linking in the @racket[noisy@] mixin
bundle:

@examples[#:eval the-eval #:no-prompt #:label #f
(struct noisy-cat cat ()
  #:properties
  (method-properties
   #:link (list noisy@)))
]

Here is a noisy cat at work:

@examples[#:eval the-eval #:no-prompt #:label #f
(greet (noisy-cat))
]

@; ----------------------------------------
@subsection[#:tag "intro-components"]{Components}

This section provides an example of component programming. That is, this
section shows how to use @racketmodname[brandx] in a style similar to
@racketmodname[racket/unit] rather than @racketmodname[racket/generic] or
@racketmodname[racket/class].

Components are described by @tech{signatures}. Like an interface,
a signature contains a set of member names, but unlike an interface, the
signature does not define a predicate or generic functions, and it cannot be
attached to a struct declaration. On the other hand, signatures directly
support contracts that depend on other signature members.

The following is a signature for a worklist component:

@examples[#:eval the-eval #:no-prompt #:label #f
(define-signature worklist
  ([worklist/c contract?]
   [empty #:dep (worklist/c) worklist/c]
   [empty? #:dep (worklist/c) (-> worklist/c boolean?)]
   [enqueue #:dep (worklist/c) (-> worklist/c any/c worklist/c)]
   [dequeue #:dep (worklist/c) (-> worklist/c (values any/c worklist/c))]))
]

A worklist component decides on a representation for worklists; the decision
is made by the component, not the interface, and different worklist
implementations may choose different representations. We could write
approximate contracts for the operations by using @racket[any/c] for worklist
arguments and results, but those contracts would fail to catch many misuses of
the operations. Instead, we can include a signature member,
@racket[worklist/c], that allows each implementation component to declare a
contract for its worklist representation, and then the signatures of the other
operations depend on the worklist contract. When a signature member's contract
depends on the value of another signature member, it must declare the
dependency with a @racket[#:dep] clause.

The following @racket[stack@] component, which represents worklists as
ordinary lists, is one implementation of the @racket[worklist] signature:

@examples[#:eval the-eval #:no-prompt #:label #f
(define stack@
  (bundle
   #:export ([worklist #:prefix %])
   (define %worklist/c list?)
   (define %empty null)
   (define %empty? null?)
   (define (%enqueue st v) (cons v st))
   (define (%dequeue st)
     (match st [(cons v st) (values v st)]))))
]

The @racket[traversal] interface has a single member, @racket[traverse], which
takes an initial value and a successors function, and collects all of the
values reachable from the initial value into a list.

@examples[#:eval the-eval #:no-prompt #:label #f
(define-signature traversal
  ([traverse (-> any/c (-> any/c (listof any/c)) (listof any/c))]))
]

Here is an implementation of the traversal component that does no
cycle detection. It uses the worklist component to manage its state.

@examples[#:eval the-eval #:no-prompt #:label #f
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
]

As an example, let's consider positive integers and define the ``successors''
using the following @racket[halfsies] function:

@examples[#:eval the-eval #:no-prompt #:label #f
(define (halfsies n)
  (define half (quotient n 2))
  (cond [(<= n 1) null]
        [(even? n) (list half)]
        [else (list half (add1 half))]))
]

The traversal function with a stack worklist implements depth-first search:

@examples[#:eval the-eval #:label #f
(define/invoke-bundles #:bind ([traversal #:prefix dfs:]) stack@ traversal@)
(dfs:traverse 100 halfsies)
]

We could also implement a FIFO queue worklist component:

@examples[#:eval the-eval #:no-prompt #:label #f
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
]

If we link the traversal component with that instead, we get a breadth-first
search:

@examples[#:eval the-eval #:label #f
(define/invoke-bundles #:bind ([traversal #:prefix bfs:]) queue@ traversal@)
(bfs:traverse 100 halfsies)
]

We could also first compound @racket[queue@] and @racket[traversal@] together
into a single bundle. Doing so does not hide any of their exports, and we still
invoke the compound bundle in the same way:

@examples[#:eval the-eval #:label #f
(define queue-traversal@ (bundle #:link (list queue@ traversal@)))
(define/invoke-bundles #:bind ([traversal #:prefix bfs2:]) queue-traversal@)
(bfs2:traverse 100 halfsies)
]

@; ----------------------------------------
@subsection[#:tag "comparison"]{Comparison with Other Libraries}

Improvements over @racketmodname[racket/generic]: This library has better
binding ergonomics: implementations may use export prefixes to avoid shadowing
generic functions, and multiple interfaces may be implemented in a single
shared definition scope. Contracts are associated with interface members, and
interface imports and exports are contract boundaries. Calls to super-methods
are supported. Abstraction in the style of mixins and traits is supported at
the granularity of interfaces.

Limitations compared to @racketmodname[racket/generic]: This library's generic
functions always dispatch on their first positional argument, and they do not
support ``defaults'' (instead, define a wrapper function). Method redirection
(as with @racket[redirect-generics], etc) is not supported.

Differences from @racketmodname[racket/class]: Users retain direct access to
structs, including pattern-matching via @racket[match]. All method names to be
visible externally or visible to subclasses must be declared in an
interface. There is no syntactic restriction or special treatment of methods;
in particular, there is no implicit @racket[this] variable. Consequently,
there is no syntactic support for treating fields as variables, and there is
no special treatment of calls on the same object. There is no special
construction/initialization support. There is no support for final methods,
@racket[abstract] methods, or @racket[augment] methods.


@; ----------------------------------------
@section[#:tag "interface"]{Interfaces}

An @deftech{interface} describes a set of names that can be implemented with
@tech{methods} and called using @deftech{generic functions}. A
@deftech{method} is a procedure that accepts at least one positional argument
that is a candidate implementation for a @tech{generic function} to dispatch
to. @tech{Methods} are attached to @racket[struct] declarations using
@racket[method-properties] or @racket[bundles->properties].

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
                  (code:line #:generics-prefix prefix-id)])]{

Defines an interface named @racket[iname] with the given
members. Specifically, the following names are defined:
@itemlist[

@item{@svar[iname] --- The interface, used mainly in import and export
specifications.}

@item{@svar[predicate-id], if given, or else @svar[iname?] --- A predicate
that recognizes instances of struct types implementing the interface.}

@item{@svar[member-id], prefixed with @svar[prefix-id], if given --- A generic
function for each member of the interface.}

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
fallback implementation has a default fallback value that raises an error when
applied. Fallbacks cannot be given for super-interface names.

A generic function is defined for every member name. If a
@racket[#:generics-prefix] clause is given, then the generic function names
are formed by adding the given prefix to the beginning of the member name.
}

@defform[(interface-out interface-id)]{

Exports the bindings associated with the interface named by
@racket[interface-id]. Those bindings are @racket[interface-id] itself, the
interface's predicate, and the generic functions.
}

@; ============================================================
@section[#:tag "signature"]{Signatures}

A @deftech{signature} describes a set of names that can be implemented with a
@tech{bundle} and linked with other bundles.

@defform[(define-signature signame (member-decl ...))
         #:grammar
         ([member-decl member-id
                       [member-id maybe-contract]]
          [maybe-contract (code:line)
                          (code:line contract-expr)
                          (code:line #:dep (dep-member-id ...) contract-expr)])]{

Defines @racket[signame] as a signature with the given members. Unlike
@racket[define-interface], no predicate or generic functions are defined, and
signatures do not support super-signatures or fallback implementations.

If a member has a contract, the contract protects imports and exports of the
signature member. If the contract has a @racket[#:dep (_dep-member-id ...)]
clause, then each @racket[_dep-member-id] is in scope for the evaluation of
the contract expression, bound to the value of the signature member.
}

@; ============================================================
@section[#:tag "bundles"]{Bundles}

Interfaces and signatures are implemented by @deftech{bundles}, which are
created with the @racket[bundle] form and may be invoked using
@racket[define/invoke-bundles] or, more typically, attached to a struct type
using @racket[bundles->properties]. The @racket[method-properties] form
provides a convenient combination of @racket[bundles->properties] and
@racket[bundle].

@defproc[(bundle? [v any/c]) boolean?]{

Returns @racket[#t] if @racket[v] is a bundle, @racket[#f] otherwise.
}

@defform[(bundle link-clause ... definition-or-expression ...)
         #:grammar
         ([link-clause (code:line #:export (export-spec ...))
                       (code:line #:import (import-spec ...))
                       (code:line #:link bundle-list-expr)]
          [export-spec interface/signature-id
                       [interface/signature-id maybe-tag maybe-complete maybe-prefix]]
          [import-spec interface/signature-id
                       [interface/signature-id maybe-tag/super maybe-prefix]]
          [maybe-tag (code:line)
                     (code:line #:tag (id ...))]
          [maybe-complete (code:line)
                          (code:line #:all)
                          (code:line #:except (member-id ...))]
          [maybe-tag/super maybe-tag
                           (code:line #:super)]
          [maybe-prefix (code:line)
                        (code:line #:prefix prefix-id)])]{

Produces a @tech{bundle} with the given exports, imports, linked bundles, and
definitions.

The @racket[#:export] clause declares what the bundle implements. An export
consists of an interface or signature name, an optional tag, an optional
except-list, and an optional prefix. The export is satisfied by definitions in
the bundle's body matching the names of the interface or signature members,
prefixed by the export prefix, if given. An export of an interface also
includes all of its super-interfaces. A member of an exported interface that
has no definition in the body retains the value from the super struct type, if
applicable, or the interface's fallback implementation, otherwise. If a member
of an exported signature has no definition in the body, a syntax error is
raised.

If an interface export contains an @racket[#:all] or @racket[#:except] clause,
it triggers a completeness check for the export. If an @racket[#:except]
clause is present, then the body must contain a definition for every member
except those listed. An @racket[#:all] clause is equivalent to
@racket[#:except ()]. If neither is present, then no completeness check is
done. A signature export always performs a completeness check; the
@racket[#:all] option is allowed but redundant.

If an export contains a non-empty prefix, then any definition in the bundle
body of a name matching that prefix (and set of scopes) must correspond to an
exported member name, otherwise an error is signaled. (This check helps
prevent typos from causing missed exports.)

The @racket[#:import] clause declares the bundle's imports. Like an export, an
import consists of an interface or signature name, an optional tag, and an
optional prefix. The special import form @racket[[interface-id #:super]] is
equivalent to @racket[[interface-id #:tag (super) #:prefix super-]]. If a
signature import has @racket[#:super] or @racket[#:tag (super)], a syntax
error is raised.

Imports and exports allow tags to distinguish between multiple occurrences of
the same interface or signature in the linkage graph. An import in one bundle
matches an export in another bundle only if both the interface/signature and
tag match. The default tag is @racket[()]. The tag @racket[(super)] is
special; it is forbidden as a signature tag and as an interface export tag,
and as an interface import tag it is automatically satisfied by the linker
using the implementation from the struct super-type (if applicable) or the
interface's fallbacks.

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

@defform[(define/invoke-bundles #:bind (import-spec ...) bundle-expr ...)]{

Links the bundles @racket[(list bundle-expr ...)], invokes them, and defines
names according to the @racket[import-spec]s.
}

@; ----------------------------------------
@section[#:tag "struct-abbrev"]{Struct Abbreviations}

@defform[(define-struct-abbrevs struct-id)]{

Defines abbreviations for the accessors and mutators of the struct type named
by @racket[struct-id]. Relies on @racket[struct-id] being bound to
compile-time information satisfying @racket[struct-info?] and
@racket[struct-field-info?]. Aliases are also defined for accessors and
mutators from super-struct types.

For each field @svar[x], an alias named @svar[.x] is defined for the accessor,
and an alias named @svar[.x-set!] is defined for the mutator if it exists.
}

@; ----------------------------------------
@(close-eval the-eval)
