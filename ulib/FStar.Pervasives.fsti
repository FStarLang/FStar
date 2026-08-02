(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Pervasives

(* This is a file from the core library, dependencies must be explicit *)
open Prims
open FStar.Pervasives.Native

/// This module is implicitly opened in the scope of all other
/// modules.
///
/// It provides several basic definitions in F* that are common to
/// most programs. Broadly, these include:
///
/// - Utility types and functions, like [id], [either], dependent
///   tuples, etc.
///
/// - Utility effect definitions, including [DIV] for divergence,
///   [EXN] of exceptions, [STATE_h] a template for state, and (the
///   poorly named) [ALL_h] which combines them all.
///
/// - Some utilities to control proofs, e.g., inversion of inductive
///   type definitions.
///
/// - Built-in attributes that can be used to decorate definitions and
///   trigger various kinds of special treatments for those
///   definitions.

(** [remove_unused_type_parameters]

    This attribute is used to decorate signatures in interfaces for
    type abbreviations, indicating that the 0-based positional
    parameters are unused in the definition and should be eliminated
    for extraction.

    This is important particularly for use with F# extraction, since
    F# does not accept type abbreviations with unused type parameters.

    See tests/bug-reports/RemoveUnusedTyparsIFace.A.fsti
 *)
val remove_unused_type_parameters : list int -> Tot unit

(** Values of type [pattern] are used to tag [Lemma]s with SMT
    quantifier triggers *)
type pattern : Type0 = unit

(** The concrete syntax [SMTPat] desugars to [smt_pat] *)
val smt_pat (#a: Type) (x: a) : Tot pattern

(** The concrete syntax [SMTPatOr] desugars to [smt_pat_or]. This is
    used to represent a disjunction of conjunctions of patterns.

    Note, the typing discipline and syntax of patterns is laxer than
    it should be. Patterns like [SMTPatOr [SMTPatOr [...]]] are
    expressible, but unsupported by F*

    TODO: We should tighten this up, perhaps just reusing the
    attribute mechanism for patterns.
*)
val smt_pat_or (x: list (list pattern)) : Tot pattern

(** eqtype is defined in prims at universe 0
    
    Although, usually, only universe 0 types have decidable equality,
    sometimes it is possible to define a type in a higher universe also
    with decidable equality (e.g., type t : Type u#1 = | Unit)

    Further, sometimes, as in Lemma below, we need to use a
    universe-polymorphic equality type (although it is only ever
    instantiated with `unit`)
*)
type eqtype_u = a:Type{hasEq a}

(** [Lemma] is a very widely used effect abbreviation.

    It stands for a unit-returning [Ghost] computation, whose main
    value is its logical payload in proving an implication between its
    pre- and postcondition.

    [Lemma] is desugared specially. The valid forms are:

     Lemma (ensures post)
     Lemma post [SMTPat ...]
     Lemma (ensures post) [SMTPat ...]
     Lemma (ensures post) (decreases d)
     Lemma (ensures post) (decreases d) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d)
     Lemma (requires pre) (ensures post) [SMTPat ...]
     Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]

   and

     Lemma post    (== Lemma (ensures post))

   the squash argument on the postcondition allows to assume the
   precondition for the *well-formedness* of the postcondition.
*)
effect Lemma (a: eqtype_u) = PURE a

(** IN the default mode of operation, all proofs in a verification
    condition are bundled into a single SMT query. Sub-terms marked
    with the [spinoff] below are the exception: each of them is
    spawned off into a separate SMT query *)
val spinoff (p: prop) : prop

val spinoff_eq (p:prop) : Lemma (spinoff p == p)

val spinoff_equiv (p:prop) : Lemma (p <==> spinoff p) [SMTPat (spinoff p)]

(** Logically equivalent to assert, but spins off separate query *)
val assert_spinoff (p: prop) : Pure unit (requires (spinoff p)) (ensures (fun x -> p))

(** The polymorphic identity function *)
unfold
let id (#a: Type) (x: a) : a = x

(** Trivial postconditions for the [PURE] effect *)
unfold
let trivial_pure_post (a: Type) : a -> prop = fun _ -> True

(** Sometimes it is convenient to explicit introduce nullary symbols
    into the ambient context, so that SMT can appeal to their definitions
    even when they are no mentioned explicitly in the program, e.g., when
    needed for triggers.

    Use [intro_ambient t] for that.
    See, e.g., LowStar.Monotonic.Buffer.fst and its usage there for loc_none *)
[@@ remove_unused_type_parameters [0; 1;]]
val ambient (#a: Type) (x: a) : prop

(** cf. [ambient], above *)
val intro_ambient (#a: Type) (x: a) : Tot (squash (ambient x))

open FStar.NormSteps

///  Controlling normalization

(** In any invocation of the F* normalizer, every occurrence of
    [normalize_term e] is reduced to the full normal for of [e]. *)
noextract
val normalize_term (#a: Type) (x: a) : Tot a

(** In any invocation of the F* normalizer, every occurrence of
    [normalize e] is reduced to the full normal for of [e]. *)
noextract
val normalize (a: prop) : prop

(** [norm s e] requests normalization of [e] with the reduction steps
    [s]. *)
noextract
val norm (s: list norm_step) (#a: Type) (x: a) : Tot a

(** [assert_norm p] reduces [p] as much as possible and then asks the
    SMT solver to prove the reduct, concluding [p] *)
val assert_norm (p: prop) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))

(** Sometimes it is convenient to introduce an equation between a term
    and its normal form in the context. *)
val normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x)

(** Like [normalize_term_spec], but specialized to [Type0] *)
val normalize_spec (a: prop) : Lemma (normalize a == a)

(** Like [normalize_term_spec], but with specific normalization steps *)
val norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x)

(** Use the following to expose an ["opaque_to_smt"] definition to the
    solver as: [reveal_opaque (`%defn) defn]. *)
let reveal_opaque (s: string) = norm_spec [delta_once [s]]

/// The [DIV] effect for divergent computations

(** The effect of divergence: from a specificational perspective it is
    identical to PURE, however the specs are given a partial
    correctness interpretation. Computations with the [DIV] effect may
    not terminate. *)
assume effect DIV

(** [PURE] and [GHOST] computations can be silently promoted for use in
    a [DIV] context *)
assume sub_effect PURE ~> DIV
assume sub_effect GHOST ~> DIV

(** [Div] is the Hoare-style counterpart of [DIV] *)
effect Div (a: Type) = DIV a

(** [Dv] is the instance of [DIV] with trivial pre- and postconditions *)
effect Dv (a: Type) = DIV a


(** We use the [EXT] effect to underspecify external system calls
    as being impure but having no observable effect on the state *)
effect EXT (a: Type) = Dv a

/// Exceptional results

(** Normal results are represented using [V x].
    Handleable exceptions are represented [E e].
    Fatal errors are [Err msg]. *)
noeq
type result (a: Type) =
  | V : v: a -> result a
  | E : e: exn -> result a
  | Err : msg: string -> result a

/// The [EXN] effect for computations that may raise exceptions or
/// fatal errors.
///
/// NOTE: BE WARNED, CODE IN THE [EXN] EFFECT IS ONLY CHECKED FOR
/// PARTIAL CORRECTNESS

assume effect EXN

(** We include divergence in exceptions. *)
assume sub_effect DIV ~> EXN

(** A Hoare-style abbreviation for [EXN] *)
effect Exn (a: Type) = EXN a

(** A variant of [Exn] with trivial pre- and postconditions *)
effect Ex (a: Type) = EXN a

(**
 Controlling inversions of inductive type

 Given a value of an inductive type [v:t], where [t = A | B], the SMT
 solver can only prove that [v=A \/ v=B] by _inverting_ [t]. This
 inversion is controlled by the [ifuel] setting, which usually limits
 the recursion depth of the number of such inversions that the solver
 can perform.

 The [inversion] predicate below is a way to circumvent the
 [ifuel]-based restrictions on inversion depth. In particular, if the
 [inversion t] is available in the SMT solver's context, it is free to
 invert [t] infinitely, regardless of the [ifuel] setting.

 Be careful using this, since it explicitly subverts the [ifuel]
 setting. If used unwisely, this can lead to very poor SMT solver
 performance.  *)
[@@ remove_unused_type_parameters [0]]
val inversion (a: Type) : prop

(** To introduce [inversion t] in the SMT solver's context, call
    [allow_inversion t]. *)
val allow_inversion (a: Type) : Pure unit (requires True) (ensures (fun x -> inversion a))

(** Since the [option] type is so common, we always allow inverting
    options, regardless of [ifuel] *)
val invertOption (a: Type)
    : Lemma (requires True) (ensures (forall (x: option a). None? x \/ Some? x)) [SMTPat (option a)]

(** Values of type [a] or type [b] *)
type either a b =
  | Inl : v: a -> either a b
  | Inr : v: b -> either a b

(** Projections for the components of a dependent pair *)
let dfst (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b)
    : Tot a
  = Mkdtuple2?._1 t

let dsnd (#a: Type) (#b: a -> GTot Type) (t: dtuple2 a b)
    : Tot (b  (Mkdtuple2?._1 t))
  = Mkdtuple2?._2 t

(** Dependent triples, with sugar [x:a & y:b x & c x y] *)
unopteq
type dtuple3 (a: Type) (b: (a -> GTot Type)) (c: (x: a -> b x -> GTot Type)) =
  | Mkdtuple3 : _1: a -> _2: b _1 -> _3: c _1 _2 -> dtuple3 a b c

(** Dependent quadruples, with sugar [x:a & y:b x & z:c x y & d x y z] *)
unopteq
type dtuple4
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  = | Mkdtuple4 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> dtuple4 a b c d

(** Dependent quadruples, with sugar [x:a & y:b x & z:c x y & d x y z] *)
unopteq
type dtuple5
  (a: Type) (b: (x: a -> GTot Type)) (c: (x: a -> b x -> GTot Type))
  (d: (x: a -> y: b x -> z: c x y -> GTot Type))
  (e: (x: a -> y: b x -> z: c x y -> w: d x y z -> GTot Type))
  = | Mkdtuple5 : _1: a -> _2: b _1 -> _3: c _1 _2 -> _4: d _1 _2 _3 -> _5: e _1 _2 _3 _4 -> dtuple5 a b c d e

(** Explicitly discarding a value *)
let ignore (#a: Type) (x: a) : Tot unit = ()

(** In a context where [false] is provable, you can prove that any
    type [a] is inhabited.

    There are many proofs of this fact in F*. Here, in the implementation, we build an
    infinitely looping function, since the termination check succeeds
    in a [False] context. *)
val false_elim (#a: Type) (u: unit{False}) : Tot a
(** Pure and ghost inner let bindings are now always inlined during
    the wp computation, if: the return type is not unit and the head
    symbol is not marked irreducible.

    To circumvent this behavior, singleton can be used.
    See the example usage in ulib/FStar.Algebra.Monoid.fst. *)
val singleton (#a: Type) (x: a) : Tot (y: a{y == x})

(** A weakening coercion from eqtype to Type.

    One of its uses is in types of layered effect combinators that
    are subjected to stricter typing discipline (no subtyping) *)
unfold let eqtype_as_type (a:eqtype) : Type = a

(** A coercion of the [x] from [a] to [b], when [a] is provably equal
    to [b]. In most cases, F* will silently coerce from [a] to [b]
    along a provable equality (as in the body of this
    function). Occasionally, you may need to apply this explicitly *)
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

(** This attribute decorates a let binding, e.g.,

    [@@normalize_for_extraction steps]
    let f = e

    The effect is that prior to extraction, F* will first reduce [e]
    using the normalization [steps], and then proceed to extract it as
    usual.

    Almost the same behavior can be achieved by using a
    [postprocess_for_extraction_with t] attribute, which runs tactic
    [t] on the goal [e == ?u] and extracts the solution to [?u] in
    place of [e]. However, using a tactic to postprocess a term is
    more general than needed for some cases.

    In particular, if we intend to only normalize [e] before
    extraction (rather than applying some other form of equational
    reasoning), then using [normalize_for_extraction] can be more
    efficient, for the following reason:

    Since we are reducing [e] just before extraction, F* can enable an
    otherwise non-user-facing normalization feature that allows all
    arguments marked [@@@erasable] to be erased to [()]---these terms
    will anyway be extracted to [()] so erasing them during
    normalization is a useful optimization.
  *)
val normalize_for_extraction (steps:list norm_step) : Tot unit

(* When using [normalize_for_extraction] this flag indicates that the type
 * of the definition should also be normalized. *)
val normalize_for_extraction_type : unit
