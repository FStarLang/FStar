# Prims

```fstar
module Prims
```

> This module provides the very basic primitives on which F* is
> built, including the definition of total functions, the basic
> logical connectives, the PURE and GHOST effects and the like.
>
> While some of the primitives have logical significance, others are
> define various conveniences in the language, e.g., type of
> attributes.

#### attribute

Type of attributes

```fstar
assume new type attribute : Type0
```

#### cps

An attribute indicating that some definition must be processed by the
Dijkstra monads for free construction

```fstar
assume val cps : attribute
```

#### hasEq

A predicate to express when a type supports decidable equality
The type-checker emits axioms for [`hasEq`](#hasEq) for each inductive type

```fstar
assume type hasEq: Type -> GTot Type0
```

#### eqtype

A convenient abbreviation, [`eqtype`](#eqtype) is the type of types in
universe 0 which support decidable equality

```fstar
type eqtype = a:Type0{hasEq a}
```

#### bool

[`bool`](#bool) is a two element type with elements `true` and `false`. We
assume it is primitive, for convenient interop with other
languages, although it could easily be defined as an inductive type
with two cases, `BTrue | BFalse`

```fstar
assume new type bool : eqtype
```

#### c_False

[`c_False`](#c_False) is the empty inductive type. The type with no
inhabitants represents logical falsehood. Note, [`c_False`](#c_False) is
seldom used directly in F*. We instead use its "squashed" variant,
`False`, see below.

```fstar
type c_False =
```

#### c_True

[`c_True`](#c_True) is the singleton inductive type---it is trivially
inhabited. Like [`c_False`](#c_False), [`c_True`](#c_True) is seldom used. We instead use
its "squashed" variants, `True`

```fstar
type c_True = | T
```

#### unit

[`unit`](#unit): another singleton type, with its only inhabitant written `()`
we assume it is primitive, for convenient interop with other languages *

```fstar
assume new type unit : eqtype
```

#### squash

`squash p` is a central type in F*---`squash p` is the proof
irrelevant analog of `p` and is represented as a unit
refinement. Squashed proofs are typically discharged using an SMT
solver, without expliciltly reconstructed any proof terms. As
such, one way to think of `squash p` is as the type of properties
proven using classical axioms without building proof terms.

```fstar
[@ "tac_opaque"]
type squash (p:Type) : Type0 = x:unit{p}
```

Note, `squash p` is just a unit refinement, it resides in universe
0, lowering the universe of `p`. From this perspective, one may
also see [`squash`](#squash) as a coercion down to universe 0.

The type is marked `tac_opaque` to indicate to Meta-F* that
instances of [`squash`](#squash) should not be unfolded when evaluating
tactics (since many optimizations in F*'s SMT encoding rely
specifically on occurrences of [`squash`](#squash).

See FStar.Squash for various ways of manipulating squashed
types.

#### auto_squash

[`auto_squash`](#auto_squash) is equivalent to [`squash`](#squash). However, F* will
automatically insert [`auto_squash`](#auto_squash) when simplifying terms,
converting terms of the form `p /\ True` to `auto_squash p`.

```fstar
let auto_squash (p:Type) = squash p
```

We distinguish these automatically inserted squashes from explicit,
user-written squashes.

A user should not have to manipulate [`auto_squash`](#auto_squash) at all, except
in rare circumstances when writing tactics to process proofs that
have already been partially simplified by F*'s simplifier.

#### logical

The [`logical`](#logical) type is transitionary. It is just an abbreviation
for `Type0`, but is used to classify uses of the basic squashed
logical connectives that follow. Some day, we plan to remove the
[`logical`](#logical) type, replacing it with [`prop`](#prop) (also defined below).

```fstar
private type logical = Type0
```

The type is marked `private` to intentionally prevent user code
from referencing this type, hopefully easing the removal of
[`logical`](#logical) in the future.

#### smt_theory_symbol

An attribute indicating that a symbol is an smt theory symbol and
hence may not be used in smt patterns.  The typechecker warns if
such symbols are used in patterns

```fstar
assume val smt_theory_symbol : attribute
```

#### l_True

[`l_True`](#l_True) has a special bit of syntactic sugar. It is written just
as "True" and rendered in the ide as `True`. It is a squashed version
of constructive truth, [`c_True`](#c_True).

```fstar
[@"tac_opaque" smt_theory_symbol]
let l_True :logical = squash c_True
```

#### l_False

[`l_False`](#l_False) has a special bit of syntactic sugar. It is written just
as "False" and rendered in the ide as `Falsee`. It is a squashed version
of constructive truth, [`c_True`](#c_True).

```fstar
[@ "tac_opaque" smt_theory_symbol]
let l_False :logical = squash c_False
```

#### equals

The type of provable equalities, defined as the usual inductive
type with a single constructor for reflexivity.  As with the other
connectives, we often work instead with the squashed version of
equality, below.

```fstar
type equals (#a:Type) (x:a) : a -> Type =
  | Refl : equals x x
```

#### eq2

[`eq2`](#eq2) is the squashed version of [`equals`](#equals). It's a proof
irrelevant, homogeneous equality in Type#0 and is written with
an infix binary `==`.

```fstar
[@ "tac_opaque" smt_theory_symbol]
type eq2 (#a:Type) (x:a) (y:a) :logical = squash (equals x y)
```

TODO: instead of hard-wiring the == syntax,
      we should just rename eq2 to op_Equals_Equals

#### h_equals

[`h_equals`](#h_equals) is the heterogeneous equality, allowing stating
equality among values of different types, but only allowing
reflexivity proofs at a given type, as with [`equals`](#equals).

```fstar
type h_equals (#a:Type) (x:a) : #b:Type -> b -> Type =
  | HRefl : h_equals x x
```

#### eq3

[`eq3`](#eq3) is the squashed variant of [`h_equals`](#h_equals)

```fstar
[@ "tac_opaque" smt_theory_symbol]
type eq3 (#a:Type) (#b:Type) (x:a) (y:b) :logical = squash (h_equals x y)
```

#### op_Equals_Equals_Equals

We typically write [`eq3`](#eq3) as a infix, binary `===`

```fstar
unfold
let op_Equals_Equals_Equals (#a:Type) (#b:Type) (x:a) (y:b) = eq3 x y
```

#### b2t

bool-to-type coercion: This is often automatically inserted type,
when using a boolean in context expecting a type. But,
occasionally, one may have to write [`b2t`](#b2t) explicitly

```fstar
type b2t (b:bool) :logical = (b == true)
```

#### c_and

constructive conjunction

```fstar
type c_and  (p:Type) (q:Type) =
  | And   : p -> q -> c_and p q
```

#### l_and

squashed conjunction, specialized to `Type0`, written with an
infix binary `/\`

```fstar
[@ "tac_opaque" smt_theory_symbol]
type l_and (p q:logical) :logical = squash (c_and p q)
```

#### c_or

constructive disjunction

```fstar
type c_or   (p:Type) (q:Type) =
  | Left  : p -> c_or p q
  | Right : q -> c_or p q
```

#### l_or

squashed disjunction, specialized to `Type0`, written with an
infix binary `\/`

```fstar
[@ "tac_opaque" smt_theory_symbol]
type l_or (p q:logical) :logical = squash (c_or p q)
```

#### l_imp

squashed (non-dependent) implication, specialized to `Type0`,
written with an infix binary `==>`. Note, `==>` binds weaker than
`/\` and `\/`

```fstar
[@ "tac_opaque" smt_theory_symbol]
type l_imp (p q:logical) :logical = squash (p -> GTot q)
```
^^^ NB: The GTot effect is primitive;

elaborated using GHOST a few lines below

#### l_iff

squashed double implication, infix binary `<==>`

```fstar
[@smt_theory_symbol]
type l_iff (p q:logical) :logical = (p ==> q) /\ (q ==> p)
```

#### l_not

squashed negation, prefix unary `~`

```fstar
[@smt_theory_symbol]
type l_not (p:logical) :logical = l_imp p False
```

#### l_ITE

l_ITE is a weak form of if-then-else at the level of
logical formulae. It's not much used.

```fstar
unfold
type l_ITE (p q r:logical) :logical = (p ==> q) /\ (~p ==> r)
```

TODO: Can we remove it

#### precedes

One of the main axioms provided by prims is [`precedes`](#precedes), a a
built-in well-founded partial order over all terms. It's typically
written with an infix binary `<<`.

```fstar
assume
type precedes : #a:Type -> #b:Type -> a -> b -> Type0
```

The `<<` order includes:
    * The `<` ordering on natural numbers
    * The subterm ordering on inductive types
    * A lexicographic ordering on the lex_t type, below
    * And, via FStar.WellFounded, relating `f x << f`

#### has_type

Within the SMT encoding, we have a relation `(HasType e t)`
asserting that (the encoding of) `e` has a type corresponding to
(the encoding of) `t`.

```fstar
assume
type has_type : #a:Type -> a -> Type -> Type0
```

It is sometimes convenient, e.g., when writing triggers for
quantifiers, to have access to this relation at the source
level. The [`has_type`](#has_type) predicate below reflects the SMT encodings
`HasType` relation. We also use it to define the type [`prop`](#prop) or
proof irrelevant propositions, below.

Note, unless you have a really good reason, you probably don't
want to use this [`has_type`](#has_type) predicate. F*'s type theory certainly
does not internalize its own typing judgment

#### l_Forall

Squashed universal quantification, or dependent products, written
`forall (x:a). p x`, specialized to Type0

```fstar
[@ "tac_opaque" smt_theory_symbol]
type l_Forall (#a:Type) (p:a -> GTot Type0) :logical = squash (x:a -> GTot (p x))
```

#### subtype_of

`p1 [`subtype_of`](#subtype_of) p2` when every element of `p1` is also an element
of `p2`.

```fstar
let subtype_of (p1:Type) (p2:Type) = forall (x:p1). has_type x p2
```

#### prop

The type of squashed types

```fstar
type prop = a:Type0{ a `subtype_of` unit }
```

#### range

[`range`](#range) is a type for the internal representations of source
ranges The functions that follow below allow manipulating ranges
abstractly.  Importantly, while we allow constructing ranges, we do
not allow destructing them, since that would reveal that
internally, set_range_of is not an identity function.

```fstar
assume
new type range : Type0
```

#### string

The type of primitive strings of characters; See FStar.String

```fstar
assume new
type string : eqtype
```

## The PURE effect

#### pure_pre

The type of pure preconditions

```fstar
let pure_pre = Type0
```

#### pure_post'

Pure postconditions, predicates on `a`, on which the precondition
`pre` is also valid. This provides a way for postcondition formula
to be typed in a context where they can assume the validity of the
precondition. This is discussed extensively in Issue #57

```fstar
let pure_post' (a:Type) (pre:Type) = (_:a{pre}) -> GTot Type0
let pure_post  (a:Type) = pure_post' a True
```

#### pure_wp

A pure weakest precondition transforms postconditions on `a`-typed
results to pure preconditions

```fstar
let pure_wp    (a:Type) = pure_post a -> GTot pure_pre
```

#### guard_free

This predicate is an internal detail, used to optimize the
encoding of some quantifiers to SMT by omitting their typing
guards. This is safe to use only when the quantifier serves to
introduce a local macro---use with caution.

```fstar
assume
type guard_free: Type0 -> Type0
```

#### pure_return

The return combinator for the PURE effect requires
proving the postcondition only on `x`

```fstar
unfold
let pure_return (a:Type) (x:a) (p:pure_post a) =
     forall (return_val:a). return_val==x ==> p return_val
```

#### pure_bind_wp

Sequential composition for the PURE effect

```fstar
unfold
let pure_bind_wp (r1:range) (a:Type) (b:Type)
                   (wp1:pure_wp a) (wp2: (a -> GTot (pure_wp b)))
                   (p : pure_post b) =
    wp1 (fun (bind_result_1:a) -> wp2 bind_result_1 p)
```

#### pure_if_then_else

Conditional composition for the PURE effect

```fstar
unfold
let pure_if_then_else (a:Type) (p:Type) (wp_then:pure_wp a) (wp_else:pure_wp a) (post:pure_post a) =
     l_ITE p (wp_then post) (wp_else post)
```

#### pure_ite_wp

Conditional composition for the PURE effect, while trying to avoid
duplicating the postcondition by giving it a local name `k`.

```fstar
unfold
let pure_ite_wp (a:Type) (wp:pure_wp a) (post:pure_post a) =
     forall (k:pure_post a).
         (forall (x:a).{:pattern (guard_free (k x))} post x ==> k x)
         ==> wp k
```

Note the use of [`guard_free`](#guard_free) here: `k` is just meant to be a macro
for `post`.

#### pure_stronger

Subsumption for the PURE effect

```fstar
unfold
let pure_stronger (a:Type) (wp1:pure_wp a) (wp2:pure_wp a) =
     forall (p:pure_post a). wp1 p ==> wp2 p
```

#### pure_close_wp

Closing a PURE WP under a binder for `b`

```fstar
unfold
let pure_close_wp (a:Type) (b:Type) (wp:(b -> GTot (pure_wp a))) (p:pure_post a) =
    forall (b:b). wp b p
```

#### pure_trivial

Trivial WP for PURE: Prove the WP with the trivial poscondition

```fstar
unfold
let pure_trivial  (a:Type) (wp:pure_wp a) = wp (fun (trivial_result:a) -> True)
```

#### PURE

Introduces the PURE effect.
The definition of the PURE effect is fixed.
NO USER SHOULD EVER CHANGE THIS.

```fstar
total
new_effect {
  PURE : a:Type -> wp:pure_wp a -> Effect
  with return_wp    = pure_return
     ; bind_wp      = pure_bind_wp
     ; if_then_else = pure_if_then_else
     ; ite_wp       = pure_ite_wp
     ; stronger     = pure_stronger
     ; close_wp     = pure_close_wp
     ; trivial      = pure_trivial
}
```

#### Pure

[`Pure`](#Pure) is a Hoare-style counterpart of [`PURE`](#PURE)

```fstar
effect Pure (a:Type) (pre:pure_pre) (post:pure_post' a pre) =
        PURE a (fun (p:pure_post a) ->
                  pre /\
                  (forall (pure_result:a). post pure_result ==> p pure_result))
```

Note the type of post, which allows to assume the precondition
for the well-formedness of the postcondition. c.f. #57

#### Admit

[`Admit`](#Admit) is an effect abbreviation for a computation that
disregards the verification condition of its continuation

```fstar
effect Admit (a:Type) = PURE a (fun (p:pure_post a) -> True)
```

#### pure_null_wp

The primitive effect [`Tot`](#Tot) is definitionally equal to an instance of [`PURE`](#PURE)

```fstar
unfold
let pure_null_wp (a:Type) (p:pure_post a) = forall (any_result:a). p any_result
```

#### Tot

[`Tot`](#Tot): From here on, we have [`Tot`](#Tot) as a defined symbol in F*.

```fstar
effect Tot (a:Type) = PURE a (pure_null_wp a)
```

```fstar
[@"opaque_to_smt"]
unfold
let pure_assert_wp (p:Type) (post:pure_post unit) = p /\ post ()
```

```fstar
[@"opaque_to_smt"]
unfold
let pure_assume_wp (p:Type) (post:pure_post unit) = p ==> post ()
```

## The `GHOST` effect

#### GHOST

[`GHOST`](#GHOST) is logically equivalent to [`PURE`](#PURE), but distinguished from
it nominally so that specific, computationally irrelevant
operations, are provided only in [`GHOST`](#GHOST) and are erased during
extraction

```fstar
total
new_effect GHOST = PURE
```

```fstar
unfold
let purewp_id (a:Type) (wp:pure_wp a) = wp
```

[`PURE`](#PURE) computations can be lifted to the [`GHOST`](#GHOST) effect (but not
vice versa) using just the identity lifting on pure wps

```fstar
sub_effect
  PURE ~> GHOST = purewp_id
```

#### GTot

As with [`Tot`](#Tot), the primitive effect [`GTot`](#GTot) is definitionally equal
to an instance of GHOST

```fstar
effect GTot (a:Type) = GHOST a (pure_null_wp a)
```

#### Ghost

[`Ghost`](#Ghost) is a the Hoare-style counterpart of [`GHOST`](#GHOST)

```fstar
effect Ghost (a:Type) (pre:Type) (post:pure_post' a pre) =
       GHOST a (fun (p:pure_post a) ->
                  pre /\
                  (forall (ghost_result:a). post ghost_result ==> p ghost_result))
```

#### dtuple2

Dependent pairs [`dtuple2`](#dtuple2) in concrete syntax is `x:a & b x`.
Its values can be constructed with the concrete syntax `(| x, y |)`

```fstar
unopteq
type dtuple2 (a:Type)
             (b:(a -> GTot Type)) =
  | Mkdtuple2: _1:a
            -> _2:b _1
            -> dtuple2 a b
```

#### l_Exists

Squashed existential quantification, or dependent sums,
are written `exists (x:a). p x` : specialized to Type0

```fstar
[@ "tac_opaque" smt_theory_symbol]
type l_Exists (#a:Type) (p:a -> GTot Type0) :logical = squash (x:a & p x)
```

#### int

Primitive type of mathematical intgers, mapped to zarith in OCaml
extraction and to the SMT sort of integers

```fstar
assume new type int : eqtype
```

#### range_0

A dummy range constant

```fstar
assume
val range_0 : range
```

#### mk_range

Building a range constant

```fstar
assume
val mk_range : file:string -> from_line:int -> from_col:int -> to_line:int -> to_col:int -> Tot range
```

## Basic operators on booleans and integers

#### op_AmpAmp

`&&` boolean conjunction

```fstar
[@smt_theory_symbol]
assume
val op_AmpAmp             : bool -> bool -> Tot bool
```

#### op_BarBar

`||` boolean disjunction

```fstar
[@smt_theory_symbol]
assume
val op_BarBar             : bool -> bool -> Tot bool
```

#### op_Negation

`not` boolean negation

```fstar
[@smt_theory_symbol]
assume
val op_Negation           : bool -> Tot bool
```

#### op_Multiply

Integer multiplication, no special symbol. See FStar.Mul

```fstar
[@smt_theory_symbol]
assume
val op_Multiply           : int -> int -> Tot int
```

#### op_Subtraction

`-` integer subtraction

```fstar
[@smt_theory_symbol]
assume
val op_Subtraction        : int -> int -> Tot int
```

#### op_Addition

`+` integer addition

```fstar
[@smt_theory_symbol]
assume
val op_Addition           : int -> int -> Tot int
```

#### op_Minus

`-` prefix unary integer negation

```fstar
[@smt_theory_symbol]
assume
val op_Minus              : int -> Tot int
```

#### op_LessThanOrEqual

`<=` integer comparison

```fstar
[@smt_theory_symbol]
assume
val op_LessThanOrEqual    : int -> int -> Tot bool
```

#### op_GreaterThan

`>` integer comparison

```fstar
[@smt_theory_symbol]
assume
val op_GreaterThan        : int -> int -> Tot bool
```

#### op_GreaterThanOrEqual

`>=` integer comparison

```fstar
[@smt_theory_symbol]
assume
val op_GreaterThanOrEqual : int -> int -> Tot bool
```

#### op_LessThan

`<` integer comparison

```fstar
[@smt_theory_symbol]
assume
val op_LessThan           : int -> int -> Tot bool
```

#### op_Equality

`=` decidable equality on [`eqtype`](#eqtype)

```fstar
[@smt_theory_symbol]
assume
val op_Equality :    #a:eqtype -> a -> a -> Tot bool
```

#### op_disEquality

`<>` decidable dis-equality on [`eqtype`](#eqtype)

```fstar
[@smt_theory_symbol]
assume
val op_disEquality : #a:eqtype -> a -> a -> Tot bool
```

#### exn

The extensible open inductive type of exceptions

```fstar
assume new
type exn : Type0
```

#### array

[`array`](#array): TODO: should be removed.
See FStar.Seq, LowStar.Buffer, etc.

```fstar
assume new
type array : Type -> Type0
```

#### deprecated

The `deprecated "s"` attribute: "s" is an alternative function
that should be printed in the warning it can be omitted if the use
case has no such function

```fstar
irreducible let deprecated (s:string) : unit = ()
```

#### strcat

String concatenation and its abbreviation as `^`.  TODO, both
should be removed in favor of what is present in FStar.String

```fstar
assume val strcat : string -> string -> Tot string
inline_for_extraction unfold let (^) s1 s2 = strcat s1 s2
```

#### list

The inductive type of polymorphic lists

```fstar
type list (a:Type) =
  | Nil  : list a
  | Cons : hd:a -> tl:list a -> list a
```

#### pattern

Values of type [`pattern`](#pattern) are used to tag [`Lemma`](#Lemma)s with SMT
quantifier triggers

```fstar
abstract
type pattern :Type0 = unit
```

#### smt_pat

The concrete syntax `SMTPat` desugars to [`smt_pat`](#smt_pat)

```fstar
irreducible
let smt_pat (#a:Type) (x:a) : pattern = ()
```

#### smt_pat_or

The concrete syntax `SMTPatOr` desugars to [`smt_pat_or`](#smt_pat_or). This is
used to represent a disjunction of conjunctions of patterns.

```fstar
irreducible
let smt_pat_or (x:list (list pattern)) : pattern = ()
```

Note, the typing discipline and syntax of patterns is laxer than
it should be. Patterns like `SMTPatOr `SMTPatOr `...``` are
expressible, but unsupported by F*

TODO: We should tighten this up, perhaps just reusing the
attribute mechanism for patterns.

#### decreases

The [`decreases`](#decreases) attribute on a recursive function is used to
specify a well-founded ordering for a termination proof

```fstar
assume
type decreases : #a:Type -> a -> Type0
```

#### Lemma

[`Lemma`](#Lemma) is a very widely used effect abbreviation.

```fstar
effect Lemma (a:Type) (pre:Type) (post:squash pre -> Type) (pats:list pattern) =
       Pure a pre (fun r -> post ())
```

 It stands for a unit-returning [`Ghost`](#Ghost) computation, whose main
 value is its logical payload in proving an implication between its
 pre- and postcondition.

 [`Lemma`](#Lemma) is desugared specially. The valid forms are:

  Lemma (ensures post)
  Lemma post `SMTPat ...`
  Lemma (ensures post) `SMTPat ...`
  Lemma (ensures post) (decreases d)
  Lemma (ensures post) (decreases d) `SMTPat ...`
  Lemma (requires pre) (ensures post) (decreases d)
  Lemma (requires pre) (ensures post) `SMTPat ...`
  Lemma (requires pre) (ensures post) (decreases d) `SMTPat ...`

and

  Lemma post    (== Lemma (ensures post))

the squash argument on the postcondition allows to assume the
precondition for the *well-formedness* of the postcondition.

#### M

The [`M`](#M) marker is interpreted by the Dijkstra Monads for Free
construction. It has a "double meaning", either as an alias for
reasoning about the direct definitions, or as a marker for places
where a CPS transformation should happen.

```fstar
effect M (a:Type) = Tot a (attributes cps)
```

#### returnM

Returning a value into the [`M`](#M) effect

```fstar
let returnM (a:Type) (x:a) : M a = x
```

#### lex_t

The type of lexicographically ordered tuples.

```fstar
type lex_t =
  | LexTop  : lex_t
  | LexCons : #a:Type -> a -> lex_t -> lex_t
```

Its values are usually written `%`a;b;c`` instead of
`LexCons a (LexCons b (LexCons c LexTop))`

Its main interest is in its ordering. In particular

[{
  %`a;b` << %`c;d` <==> a << c  \/ (a == c /\ b << d)
}]

TODO: Rather than exposing this as an an inductive type, we plan
      to revise this as an abstract type.

#### as_requires

[`as_requires`](#as_requires) turns a WP into a precondition, by applying it to
a trivial postcondition

```fstar
unfold
let as_requires (#a:Type) (wp:pure_wp a)  = wp (fun x -> True)
```

#### as_ensures

[`as_ensures`](#as_ensures) turns a WP into a postcondition, relying on a kind of
double negation translation.

```fstar
unfold
let as_ensures  (#a:Type) (wp:pure_wp a) (x:a) = ~ (wp (fun y -> (y=!=x)))
```

#### _assume

The keyword term-level keyword `assume` is desugared to [`_assume`](#_assume).
It explicitly provides an escape hatch to assume a given property
`p`.

```fstar
assume
val _assume : p:Type -> Pure unit (requires (True)) (ensures (fun x -> p))
```

#### admit

[`admit`](#admit) is another escape hatch: It discards the continuation and
returns a value of any type

```fstar
assume
val admit   : #a:Type -> unit -> Admit a
```

#### magic

[`magic`](#magic) is another escape hatch: It retains the continuation but
returns a value of any type

```fstar
assume
val magic   : #a:Type -> unit -> Tot a
```

#### unsafe_coerce

[`unsafe_coerce`](#unsafe_coerce) is another escape hatch: It coerces an `a` to a
`b`.

```fstar
irreducible
let unsafe_coerce (#a:Type) (#b: Type) (x:a) : b = admit (); x
```

#### admitP

[`admitP`](#admitP): TODO: Unused ... remove?

```fstar
assume
val admitP  : p:Type -> Pure unit True (fun x -> p)
```

#### _assert

The keyword term-level keyword `assert` is desugared to [`_assert`](#_assert).
It force a proof of a property `p`, then assuming `p` for the
continuation.

```fstar
val _assert : p:Type -> Pure unit (requires p) (ensures (fun x -> p))
let _assert p = ()
```

#### spinoff

In the default mode of operation, all proofs in a verification
condition are bundled into a single SMT query. Sub-terms marked
with the [`spinoff`](#spinoff) below are the exception: each of them is
spawned off into a separate SMT query

```fstar
abstract
let spinoff (p:Type) : Type = p
```

#### assert_spinoff

Logically equivalent to assert, but spins off separate query

```fstar
val assert_spinoff : (p:Type) -> Pure unit (requires (spinoff (squash p))) (ensures (fun x -> p))
let assert_spinoff p = ()
```

#### cut

Logically equivalent to assert; TODO remove?

```fstar
val cut : p:Type -> Pure unit (requires p) (fun x -> p)
let cut p = ()
```

#### nat

The type of non-negative integers

```fstar
type nat = i:int{i >= 0}
```

#### pos

The type of positive integers

```fstar
type pos = i:int{i > 0}
```

#### nonzero

The type of non-zero integers

```fstar
type nonzero = i:int{i<>0}
```

> Arbitrary precision ints are compiled to zarith (big_ints) in
> OCaml and to .NET BigInteger in F#. Both the modulus and division
> operations are Euclidean and are mapped to the corresponding
> theory symbols in the SMT encoding

#### op_Modulus

Euclidean modulus

```fstar
[@smt_theory_symbol]
assume
val op_Modulus            : int -> nonzero -> Tot int
```

#### op_Division

Euclidean division, written `/`

```fstar
[@smt_theory_symbol]
assume
val op_Division           : int -> nonzero -> Tot int
```

#### rec

`pow2 x` is `2^x`:

```fstar
let rec pow2 (x:nat) : Tot pos =
  match x with
  | 0  -> 1
  | _  -> 2 `op_Multiply` (pow2 (x-1))
```

TODO: maybe move this to FStar.Int

#### min

[`min`](#min) computes the minimum of two [`int`](#int)s

```fstar
let min x y = if x <= y then x else y
```

#### abs

[`abs`](#abs) computes the absolute value of an [`int`](#int)

```fstar
let abs (x:int) : Tot int = if x >= 0 then x else -x
```

#### string_of_bool

A primitive printer for booleans:

```fstar
assume
val string_of_bool: bool -> Tot string
```

TODO: unnecessary, this could easily be defined

#### string_of_int

A primitive printer for [`int`](#int)

```fstar
assume
val string_of_int: int -> Tot string
```

#### labeled

[`labeled`](#labeled) is used internally to the SMT encoding to associate a
source-code location with an assertion.

```fstar
irreducible
let labeled (r:range) (msg:string) (b:Type) :Type = b
```

#### __cache_version_number__

THIS IS MEANT TO BE KEPT IN SYNC WITH FStar.CheckedFiles.fs
Incrementing this forces all .checked files to be invalidated

```fstar
private
abstract
let __cache_version_number__ = 16
```
