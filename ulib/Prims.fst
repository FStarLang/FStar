(*
   Copyright 2008-2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
[@@"no_prelude"]
module Prims

/// This module is implicitly opened in the scope of all other modules.
///
/// It provides the very basic primitives on which F* is
/// built, including the definition of total functions, the basic
/// logical connectives, the PURE and GHOST effects and the like.
///
/// While some of the primitives have logical significance, others are
/// define various conveniences in the language, e.g., type of
/// attributes.


(***** Begin trusted primitives *****)

(** Primitives up to the definition of the GTot effect are trusted
    Beyond that all definitions are fully verified *)



(** Type of attributes *)
assume new
type attribute : Type0 


(** This attribute marks definitions for logical connectives that should
    not be unfolded during tactics. *)
assume
val tac_opaque : attribute

(** This attribute is added to all projectors. *)
assume
val projector : attribute

(** This attribute is added to all discriminators. *)
assume
val discriminator : attribute

(** This attribute can be used on type binders to make unifier attempt
    to unrefine them before instantiating them. This is useful in polymorphic
    definitions where the type does not change the result type, for example
    eq2 below. Using the attribute, an equality between two nats will happen
    at type int, which is more canonical.

    This feature is experimental and only enabled with "--ext __unrefine" *)
assume
val unrefine : attribute

(** This attribute can be attached to a type definition to partly counter the
    behavior of the `unrefine` attribute. It will cause the definition marked
    `do_not_unrefine` to not be unfolded during the unrefining process. *)
assume
val do_not_unrefine : attribute

(** A binder in a definition/declaration may optionally be annotated as strictly_positive
    When the let definition is used in a data constructor type in an inductive
    definition, this annotation is used to check the positivity of the inductive

    Further F* checks that the binder is actually positive in the let definition

    See tests/micro-benchmarks/Positivity.fst and NegativeTests.Positivity.fst for a few examples
  *)
assume val strictly_positive : attribute

(** The type of propositions. *)
assume val prop : Type0

(** A predicate to express when a type supports decidable equality
    The type-checker emits axioms for [hasEq] for each inductive type *)
assume
type hasEq : Type -> GTot prop

(** A convenient abbreviation, [eqtype] is the type of types in
    universe 0 which support decidable equality *)
type eqtype = a: Type0{hasEq a}

(** [bool] is a two element type with elements [true] and [false]. We
    assume it is primitive, for convenient interop with other
    languages, although it could easily be defined as an inductive type
    with two cases, [BTrue | BFalse] *)
assume new
type bool : eqtype 

(** [empty] is the empty inductive type. The type with no
    inhabitants represents logical falsehood. Note, [empty] is
    seldom used directly in F*. We instead use its "squashed" variant,
    [False], see below. *)
type empty = 

(** [trivial] is the singleton inductive type---it is trivially
    inhabited. Like [empty], [trivial] is seldom used. We instead use
    its "squashed" variants, [True] *)
type trivial = | T

(** [unit]: another singleton type, with its only inhabitant written [()]
    we assume it is primitive, for convenient interop with other languages *)
assume new
type unit : eqtype

(** [squash p] is a central type in F*---[squash p] is the proof
    irrelevant analog of [p] and is represented as a unit
    refinement. Squashed proofs are typically discharged using an SMT
    solver, without any proof terms explicitly reconstructed. As
    such, one way to think of [squash p] is as the type of properties
    proven using classical axioms without building proof terms.

    Note, [squash p] is just a unit refinement, it resides in universe
    0, lowering the universe of [p]. From this perspective, one may
    also see [squash] as a coercion down to universe 0.

    The type is marked [tac_opaque] to indicate to Meta-F* that
    instances of [squash] should not be unfolded when evaluating
    tactics (since many optimizations in F*'s SMT encoding rely
    specifically on occurrences of [squash].

    See FStar.Squash for various ways of manipulating squashed
    types. *)
[@@ tac_opaque]
type squash (p: prop) : Type0 = x: unit{p}

(** An attribute indicating that a symbol is an smt theory symbol and
    hence may not be used in smt patterns.  The typechecker warns if
    such symbols are used in patterns *)
assume
val smt_theory_symbol:attribute

(** Written with the `True` syntax, `l_True` is the true proposition. *)
[@@ smt_theory_symbol]
assume val l_True : prop

(** Written with the `False` syntax, `l_False` is the false proposition. *)
[@@ smt_theory_symbol]
assume val l_False : prop

(**** Effects

    In this simplified effect system an effect is just a name.  A
    computation type is [M t (requires pre) (ensures post)], where
    [pre] is a proposition and [post] is a predicate on the result. *)

total assume effect Tot
total assume effect GTot

(** [Tot] computations can be lifted to [GTot] (but not vice versa),
    *)
assume sub_effect Tot ~> GTot

(** Hoare-style abbreviations.  Effect abbreviations are parameterized
    by the result type only; any pre/postcondition written at the use
    site is conjoined with the one in the abbreviation. *)
effect Pure  (a: Type) = Tot a
effect PURE  (a: Type) = Tot a
effect Ghost (a: Type) = GTot a
effect GHOST (a: Type) = GTot a


(** The type of provable equalities, defined as the usual inductive
    type with a single constructor for reflexivity.  As with the other
    connectives, we often work instead with the squashed version of
    equality, below. *)
type equals (#a: Type) (x: a) : a -> Type = | Refl : equals x x

(** `eq2` is propositional equality, usually written with the `==` syntax. *)
//    TODO: instead of hard-wiring the == syntax,
//          we should just rename eq2 to op_Equals_Equals
[@@ smt_theory_symbol]
assume val eq2 (#[@@@unrefine] a: Type) (x: a) (y: a) : prop

(** bool-to-prop coercion: This is often automatically inserted type,
    when using a boolean in context expecting a type. But,
    occasionally, one may have to write [b2t] explicitly *)
let b2t (b: bool) : prop = (b == true)

(** constructive conjunction *)
type pair (p: Type) (q: Type) = | Pair : _1:p -> _2:q -> pair p q

(** Written with the `/\` syntax, `l_and` is the propositional conjunction. *)
[@@ smt_theory_symbol]
assume val l_and ([@@@strictly_positive] p: prop) ([@@@strictly_positive] q: prop) : prop

(** constructive disjunction *)
type sum (p: Type) (q: Type) =
  | Left : v:p -> sum p q
  | Right : v:q -> sum p q

(** Written with the `\/` syntax, `l_or` is the propositional disjunction. *)
[@@ smt_theory_symbol]
assume val l_or ([@@@strictly_positive] p: prop) ([@@@strictly_positive] q: prop) : prop

(** Written with the `==>` syntax, `l_imp` is the propositional implication.
    Note, [==>] binds weaker than [/\] and [\/] *)
[@@ smt_theory_symbol]
assume val l_imp (p: prop) ([@@@strictly_positive] q: prop) : prop

(** double implication, infix binary [<==>] *)
[@@ smt_theory_symbol]
let l_iff (p: prop) (q: prop) : prop = (p ==> q) /\ (q ==> p)

(** negation, prefix unary [~] *)
[@@ smt_theory_symbol]
type l_not (p: prop) : prop = p ==> False

(** l_ITE is a form of if-then-else at the level of
    propositions. It's not used much.

    TODO: Can we remove it *)
unfold
let l_ITE (p: prop) (q: prop) (r: prop) : prop = (p ==> q) /\ (~p ==> r)

(** One of the main axioms provided by prims is [precedes], a
    built-in well-founded partial order over all terms. It's typically
    written with an infix binary [<<].

    The [<<] order includes:
        * The [<] ordering on natural numbers
        * The subterm ordering on inductive types
        * [f x << D f] for data constructors D of an inductive t whose
          arguments include a ghost or total function returning a t *)

assume
type precedes : #a: Type -> #b: Type -> a -> b -> prop

(** The type of primitive strings of characters; See FStar.String *)
assume new
type string : eqtype 

(** This attribute can be added to the declaration or definition of
    any top-level symbol. It causes F* to report a warning on any
    use of that symbol, printing the [msg] argument.
    
    This is used, for instance to:
    
    - tag every escape hatch, e.g., [assume], [admit], etc

    Reports for uses of symbols tagged with this attribute
    are controlled using the `--report_assumes` option
    and warning number 334. 
    
    See tests/micro-benchmarks/WarnOnUse.fst
 *)
assume
val warn_on_use (msg: string) : Tot unit

(** The [deprecated "s"] attribute: "s" is an alternative function
    that should be printed in the warning it can be omitted if the use
    case has no such function *)
assume
val deprecated (s: string) : Tot unit


(** Within the SMT encoding, we have a relation [(HasType e t)]
    asserting that (the encoding of) [e] has a type corresponding to
    (the encoding of) [t].

    It is sometimes convenient, e.g., when writing triggers for
    quantifiers, to have access to this relation at the source
    level. The [has_type] predicate below reflects the SMT encodings
    [HasType] relation. We also use it to define the type [prop] or
    proof irrelevant propositions, below.

    Note, unless you have a really good reason, you probably don't
    want to use this [has_type] predicate. F*'s type theory certainly
    does not internalize its own typing judgment *)
[@@deprecated "'has_type' is intended for internal use and debugging purposes only; \
                do not rely on it for your proofs"]
assume
type has_type : #a: Type -> a -> Type -> prop 

(** Universal quantification, written [forall (x:a). p x] *)
[@@ tac_opaque; smt_theory_symbol]
assume val l_Forall (#a: Type) ([@@@strictly_positive] p: (a -> GTot prop)) : prop

#push-options "--warn_error -288" 
(** [p1 `subtype_of` p2] when every element of [p1] is also an element
    of [p2]. *)
let subtype_of (p1 p2: Type) = forall (x: p1). has_type x p2
#pop-options

(**** Escape hatches *)

(***** End trusted primitives *****)


(** This point onward, F* fully verifies all the definitions *)

(** [===] heterogeneous equality *)
let ( === ) (#a #b: Type) (x: a) (y: b) : prop = a == b /\ x == y

(** Dependent pairs [dtuple2] in concrete syntax is [x:a & b x].
    Its values can be constructed with the concrete syntax [(| x, y |)] *)
unopteq
type dtuple2 (a: Type) (b: (a -> GTot Type)) =
  | Mkdtuple2 : _1: a -> _2: b _1 -> dtuple2 a b

(** Squashed existential quantification, or dependent sums,
    are written [exists (x:a). p x] : specialized to Type0 *)
[@@ smt_theory_symbol]
assume val l_Exists (#a: Type) ([@@@strictly_positive] p: (a -> GTot prop)) : prop

(** Primitive type of mathematical integers, mapped to zarith in OCaml
    extraction and to the SMT sort of integers *)
assume new
type int : eqtype 

(**** Basic operators on booleans and integers *)

(** [&&] boolean conjunction *)

[@@ smt_theory_symbol]
assume
val ( && ) : bool -> bool -> Tot bool

(** [||] boolean disjunction *)

[@@ smt_theory_symbol]
assume
val ( || ) : bool -> bool -> Tot bool

(** [not] boolean negation *)

[@@ smt_theory_symbol]
assume
val not: bool -> Tot bool

(** [*] integer multiplication *)

[@@ smt_theory_symbol]
assume
val ( * ) : int -> int -> Tot int

(** [-] integer subtraction *)

[@@ smt_theory_symbol]
assume
val ( - ) : int -> int -> Tot int

(** [+] integer addition *)

[@@ smt_theory_symbol]
assume
val ( + ) : int -> int -> Tot int

(** [~-] prefix unary integer negation; [-x] is notation for [~-x] *)

[@@ smt_theory_symbol]
assume
val ( ~- ) : int -> Tot int

(** [<=] integer comparison *)

[@@ smt_theory_symbol]
assume
val ( <= ) : int -> int -> Tot bool

(** [>] integer comparison *)

[@@ smt_theory_symbol]
assume
val ( > ) : int -> int -> Tot bool

(** [>=] integer comparison *)

[@@ smt_theory_symbol]
assume
val ( >= ) : int -> int -> Tot bool

(** [<] integer comparison *)

[@@ smt_theory_symbol]
assume
val ( < ) : int -> int -> Tot bool

(** [=] decidable equality on [eqtype] *)

[@@ smt_theory_symbol]
assume
val ( = ) : #[@@@unrefine]a: eqtype -> a -> a -> Tot bool

(** [<>] decidable dis-equality on [eqtype] *)

[@@ smt_theory_symbol]
assume
val ( <> ) : #[@@@unrefine]a: eqtype -> a -> a -> Tot bool

(** The extensible open inductive type of exceptions *)
assume new
type exn : Type0 

(** String concatenation and its abbreviation as [^].  TODO, both
    should be removed in favor of what is present in FStar.String *)
assume
val strcat: string -> string -> Tot string
inline_for_extraction unfold
let ( ^ ) s1 s2 = strcat s1 s2

(** The inductive type of polymorphic lists *)
type list (a: Type) =
  | Nil : list a
  | Cons : hd: a -> tl: list a -> list a

(** The keyword term-level keyword [assume] is desugared to [_assume].
    It explicitly provides an escape hatch to assume a given property
    [p]. *)
[@@ warn_on_use "Uses an axiom"]
assume
val _assume (p: prop) : Pure unit (requires (True)) (ensures (fun x -> p))

(** [admit] is another escape hatch: It discards the continuation and
    returns a value of any type.  Discarding the continuation is what the
    [l_False] in its result type does: everything after a call to [admit] is
    checked under a false hypothesis. *)
[@@ warn_on_use "Uses an axiom"]
assume
val admit: #a: Type -> unit -> Tot (_: a{l_False})

(** [magic] is another escape hatch: It retains the continuation but
    returns a value of any type *)
[@@ warn_on_use "Uses an axiom"]
assume
val magic: #a: Type -> unit -> Tot a

(** [unsafe_coerce] is another escape hatch: It coerces an [a] to a
    [b].  *)
[@@ warn_on_use "Uses an axiom"]
irreducible
let unsafe_coerce (#a #b: Type) (x: a) : b =
  admit ();
  x

(** The keyword term-level keyword [assert] is desugared to [_assert].
    It force a proof of a property [p], then assuming [p] for the
    continuation. *)
val _assert (p: prop) : Pure unit (requires p) (ensures (fun x -> p))
let _assert p = ()

(** Logically equivalent to assert; TODO remove? *)
val cut (p: prop) : Pure unit (requires p) (fun x -> p)
let cut p = ()

(** Indefinite description is an axiom that allows picking a witness for an existential quantifier

For some background on the axiom, see:
  https://github.com/coq/coq/wiki/CoqAndAxioms#indefinite-description--hilberts-epsilon-operator
  https://en.wikipedia.org/wiki/Theory_of_descriptions#Indefinite_descriptions *)
assume val indefinite_description (#a: Type) (p: (a -> prop) { exists x. p x })
  : GTot (x: a { p x })

(* prop-to-bool coercion.

   [t2b_pred] is a top-level definition rather than a local one on purpose: the
   witness for [indefinite_description]'s existential is found by instantiating
   it with the applications appearing in the assertion below, which only works
   as long as they survive as applications. *)
let t2b_pred (p: prop) (b: bool) : prop = b <==> p

irreducible let t2b (p: prop) : GTot (b:bool { b <==> p }) =
  assert t2b_pred p true \/ t2b_pred p false;
  indefinite_description (t2b_pred p)

(** The type of non-negative integers *)
type nat = i: int{i >= 0}

(** The type of positive integers *)
type pos = i: int{i > 0}

(** The type of non-zero integers *)
type nonzero = i: int{i <> 0}

/// Arbitrary precision ints are compiled to zarith (big_ints) in
/// OCaml and to .NET BigInteger in F#. Both the modulus and division
/// operations are Euclidean and are mapped to the corresponding
/// theory symbols in the SMT encoding

(** Euclidean modulus *)

[@@ smt_theory_symbol]
assume
val ( % ) : int -> nonzero -> Tot int

(** Euclidean division, written [/] *)

[@@ smt_theory_symbol]
assume
val ( / ) : int -> nonzero -> Tot int

(** [pow2 x] is [2^x]:

    TODO: maybe move this to FStar.Int *)
let rec pow2 (x: nat) : Tot pos =
  match x with
  | 0 -> 1
  | _ -> 2 * pow2 (x - 1)

(** [min] computes the minimum of two [int]s *)
let min x y = if x <= y then x else y

(** [abs] computes the absolute value of an [int] *)
let abs (x: int) : Tot int = if x >= 0 then x else - x

(** A primitive printer for booleans:

    TODO: unnecessary, this could easily be defined *)
assume
val string_of_bool: bool -> Tot string

(** A primitive printer for [int] *)
assume
val string_of_int: int -> Tot string

(** An artificial tag used in the definition of [nonempty] below. It
    exists only to make sure the body of the existential mentions the
    bound variable, so that F*'s simplifier does not turn
    [exists (x:a). True] into [True]. *)
let nonempty_tag (#a: Type) (x: a) : prop = True

(** [nonempty a] holds exactly when the type [a] is inhabited.

    This is a lang item: the typechecker requires a proof of
    [nonempty t] for every top-level definition [let x : t = e] where
    [e] has a potentially divergent effect (i.e., any effect other than
    [Tot] or [GTot]). Without this obligation, a divergent term could
    be used to inhabit any type, including [False].

    It is stated as [nonempty a] rather than [exists (x:a). True] so
    that libraries can register SMT patterns for it. *)
let nonempty (a: Type) : prop = exists (x: a). nonempty_tag x

(** Any element of [a] witnesses that [a] is nonempty. *)
let nonempty_intro (#a: Type) (x: a) : nonempty a = _assert (nonempty_tag x)

(** The axiom of choice: from a proof that [a] is inhabited, we can
    (ghostly) obtain an element of [a]. *)
let nonempty_elim (a: Type { nonempty a }) : GTot a =
  indefinite_description (fun (_: a) -> True)

(** A version of [nonempty_elim] taking the proof explicitly. *)
let nonempty_elim' (#a: Type) (h: nonempty a) : GTot a = nonempty_elim a
