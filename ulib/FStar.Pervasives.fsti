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

module FStar.Pervasives

(* This is a file from the core library, dependencies must be explicit *)
open Prims
include FStar.Pervasives.Native

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
    sometimes it is possible to define a type in a higher univese also
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
effect Lemma (a: eqtype_u) (pre: Type) (post: (squash pre -> Type)) (pats: list pattern) =
  Pure a pre (fun r -> post ())

(** IN the default mode of operation, all proofs in a verification
    condition are bundled into a single SMT query. Sub-terms marked
    with the [spinoff] below are the exception: each of them is
    spawned off into a separate SMT query *)
val spinoff (p: Type0) : Type0

val spinoff_eq (p:Type0) : Lemma (spinoff p == p)

val spinoff_equiv (p:Type0) : Lemma (p <==> spinoff p) [SMTPat (spinoff p)]

(** Logically equivalent to assert, but spins off separate query *)
val assert_spinoff (p: Type) : Pure unit (requires (spinoff (squash p))) (ensures (fun x -> p))

(** The polymorphic identity function *)
unfold
let id (#a: Type) (x: a) : a = x

(** Trivial postconditions for the [PURE] effect *)
unfold
let trivial_pure_post (a: Type) : pure_post a = fun _ -> True

(** Sometimes it is convenient to explicit introduce nullary symbols
    into the ambient context, so that SMT can appeal to their definitions
    even when they are no mentioned explicitly in the program, e.g., when
    needed for triggers.

    Use [intro_ambient t] for that.
    See, e.g., LowStar.Monotonic.Buffer.fst and its usage there for loc_none *)
[@@ remove_unused_type_parameters [0; 1;]]
val ambient (#a: Type) (x: a) : Type0

(** cf. [ambient], above *)
val intro_ambient (#a: Type) (x: a) : Tot (squash (ambient x))


///  Controlling normalization

(** In any invocation of the F* normalizer, every occurrence of
    [normalize_term e] is reduced to the full normal for of [e]. *)
val normalize_term (#a: Type) (x: a) : Tot a

(** In any invocation of the F* normalizer, every occurrence of
    [normalize e] is reduced to the full normal for of [e]. *)
val normalize (a: Type0) : Type0

(** Value of [norm_step] are used to enable specific normalization
    steps, controlling how the normalizer reduces terms. *)
val norm_step : Type0

(** Logical simplification, e.g., [P /\ True ~> P] *)
val simplify : norm_step

(** Weak reduction: Do not reduce under binders *)
val weak : norm_step

(** Head normal form: Do not reduce in function arguments or in binder types *)
val hnf : norm_step

(** Reduce primitive operators, e.g., [1 + 1 ~> 2] *)
val primops : norm_step

(** Unfold all non-recursive definitions *)
val delta : norm_step

(** Turn on debugging for this specific call. *)
val norm_debug : norm_step

(** Unroll recursive calls

    Note: Since F*'s termination check is semantic rather than
    syntactically structural, recursive calls in inconsistent contexts,
    or recursive evaluation of open terms can diverge.

    When asking for the [zeta] step, F* implements a heuristic to
    disable [zeta] when reducing terms beneath a blocked match. This
    helps prevent some trivial looping behavior. However, it also
    means that with [zeta] alone, your term may not reduce as much as
    you might want. See [zeta_full] for that.
  *)
val zeta : norm_step

(** Unroll recursive calls

    Unlike [zeta], [zeta_full] has no looping prevention
    heuristics. F* will try to unroll recursive functions as much as
    it can, potentially looping. Use with care.

    Note, [zeta_full] implies [zeta].
    See [tests/micro-benchmarks/ReduceRecUnderMatch.fst] for an example.
 *)
val zeta_full : norm_step

(** Reduce case analysis (i.e., match) *)
val iota : norm_step

(** Use normalization-by-evaluation, instead of interpretation (experimental) *)
val nbe : norm_step

(** Reify effectful definitions into their representations *)
val reify_ : norm_step

(** Unlike [delta], unfold definitions for only the names in the given
    list. Each string is a fully qualified name like [A.M.f] *)
val delta_only (s: list string) : Tot norm_step

(** Unfold definitions for only the names in the given list, but
    unfold each definition encountered after unfolding as well.

    For example, given

      {[
        let f0 = 0
        let f1 = f0 + 1
      ]}

    [norm [delta_only [`%f1]] f1] will reduce to [f0 + 1].
    [norm [delta_fully [`%f1]] f1] will reduce to [0 + 1].

    Each string is a fully qualified name like [A.M.f], typically
    constructed using a quotation, as in the example above. *)
val delta_fully (s: list string) : Tot norm_step

(** Rather than mention a symbol to unfold by name, it can be
    convenient to tag a collection of related symbols with a common
    attribute and then to ask the normalizer to reduce them all.

    For example, given:

      {[
        irreducible let my_attr = ()

        [@@my_attr]
        let f0 = 0

        [@@my_attr]
        let f1 = f0 + 1
      ]}

   {[norm [delta_attr [`%my_attr]] f1]}

   will reduce to [0 + 1].

  *)
val delta_attr (s: list string) : Tot norm_step

(**
    For example, given:

      {[
        unfold
        let f0 = 0

        inline_for_extraction
        let f1 = f0 + 1

      ]}

   {[norm [delta_qualifier ["unfold"; "inline_for_extraction"]] f1]}

   will reduce to [0 + 1].

  *)
val delta_qualifier (s: list string) : Tot norm_step

val delta_namespace (s: list string) : Tot norm_step

(**
    This step removes the some internal meta nodes during normalization

    In most cases you shouldn't need to use this step explicitly

   *)
val unmeta : norm_step

(**
    This step removes ascriptions during normalization

    An ascription is a type or computation type annotation on
      an expression, written as (e <: t) or (e <: C)

    normalize (e <: (t|C)) usually would normalize both the expression e
      and the ascription

    However, with unascribe step on, it will drop the ascription
      and return the result of (normalize e),

    Removing ascriptions may improve the performance,
      as the normalization has less work to do

    However, ascriptions help in re-typechecking of the terms,
      and in some cases, are necessary for doing so

    Use it with care

   *)
val unascribe : norm_step

(** [norm s e] requests normalization of [e] with the reduction steps
    [s]. *)
val norm (s: list norm_step) (#a: Type) (x: a) : Tot a

(** [assert_norm p] reduces [p] as much as possible and then asks the
    SMT solver to prove the reduct, concluding [p] *)
val assert_norm (p: Type) : Pure unit (requires (normalize p)) (ensures (fun _ -> p))

(** Sometimes it is convenient to introduce an equation between a term
    and its normal form in the context. *)
val normalize_term_spec (#a: Type) (x: a) : Lemma (normalize_term #a x == x)

(** Like [normalize_term_spec], but specialized to [Type0] *)
val normalize_spec (a: Type0) : Lemma (normalize a == a)

(** Like [normalize_term_spec], but with specific normalization steps *)
val norm_spec (s: list norm_step) (#a: Type) (x: a) : Lemma (norm s #a x == x)

(** Use the following to expose an ["opaque_to_smt"] definition to the
    solver as: [reveal_opaque (`%defn) defn] *)
let reveal_opaque (s: string) = norm_spec [delta_only [s]]

(** Wrappers over pure wp combinators that return a pure_wp type
    (with monotonicity refinement) *)

unfold
let pure_return (a:Type) (x:a) : pure_wp a =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_return0 a x

unfold
let pure_bind_wp (a b:Type) (wp1:pure_wp a) (wp2:(a -> Tot (pure_wp b))) : Tot (pure_wp b) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_bind_wp0 a b wp1 wp2

unfold
let pure_if_then_else (a p:Type) (wp_then wp_else:pure_wp a) : Tot (pure_wp a) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_if_then_else0 a p wp_then wp_else

unfold
let pure_ite_wp (a:Type) (wp:pure_wp a) : Tot (pure_wp a) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_ite_wp0 a wp

unfold
let pure_close_wp (a b:Type) (wp:b -> Tot (pure_wp a)) : Tot (pure_wp a) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_close_wp0 a b wp

unfold
let pure_null_wp (a:Type) : Tot (pure_wp a) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_null_wp0 a

[@@ "opaque_to_smt"]
unfold
let pure_assert_wp (p:Type) : Tot (pure_wp unit) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_assert_wp0 p

[@@ "opaque_to_smt"]
unfold
let pure_assume_wp (p:Type) : Tot (pure_wp unit) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  pure_assume_wp0 p

/// The [DIV] effect for divergent computations
///
/// The wp-calculus for [DIV] is same as that of [PURE]


(** The effect of divergence: from a specificational perspective it is
    identical to PURE, however the specs are given a partial
    correctness interpretation. Computations with the [DIV] effect may
    not terminate. *)
new_effect {
  DIV : a:Type -> wp:pure_wp a -> Effect
  with
    return_wp = pure_return
  ; bind_wp = pure_bind_wp
  ; if_then_else = pure_if_then_else
  ; ite_wp = pure_ite_wp
  ; stronger = pure_stronger
  ; close_wp = pure_close_wp
  ; trivial = pure_trivial
}

(** [PURE] computations can be silently promoted for use in a [DIV] context *)
sub_effect PURE ~> DIV { lift_wp = purewp_id }


(** [Div] is the Hoare-style counterpart of the wp-indexed [DIV] *)
unfold
let div_hoare_to_wp (#a:Type) (#pre:pure_pre) (post:pure_post' a pre) : Tot (pure_wp a) =
  reveal_opaque (`%pure_wp_monotonic) pure_wp_monotonic;
  fun (p:pure_post a) -> pre /\ (forall a. post a ==> p a)

effect Div (a: Type) (pre: pure_pre) (post: pure_post' a pre) =
  DIV a (div_hoare_to_wp post)


(** [Dv] is the instance of [DIV] with trivial pre- and postconditions *)
effect Dv (a: Type) = DIV a (pure_null_wp a)


(** We use the [EXT] effect to underspecify external system calls
    as being impure but having no observable effect on the state *)
effect EXT (a: Type) = Dv a

/// The [STATE_h] effect template for stateful computations, generic
/// in the type of the state.
///
/// Note, [STATE_h] is itself not a computation type in F*, since it
/// is parameterized by the type of heap. However, instantiations of
/// [STATE_h] with specific types of the heap are computation
/// types. See, e.g., [FStar.ST] for such instantiations.
///
/// Weakest preconditions for stateful computations transform
/// [st_post_h] postconditions to [st_pre_h] preconditions. Both are
/// parametric in the type of the state, here denoted by the
/// [heap:Type] variable.

(** Preconditions are predicates on the [heap] *)
let st_pre_h (heap: Type) = heap -> GTot Type0

(** Postconditions relate [a]-typed results to the final [heap], here
    refined by some pure proposition [pre], typically instantiated to
    the precondition applied to the initial [heap] *)
let st_post_h' (heap a pre: Type) = a -> _: heap{pre} -> GTot Type0

(** Postconditions without refinements *)
let st_post_h (heap a: Type) = st_post_h' heap a True

(** The type of the main WP-transformer for stateful computations *)
let st_wp_h (heap a: Type) = st_post_h heap a -> Tot (st_pre_h heap)

(** Returning a value does not transform the state *)
unfold
let st_return (heap a: Type) (x: a) (p: st_post_h heap a) = p x

(** Sequential composition of stateful WPs *)
unfold
let st_bind_wp
      (heap: Type)
      (a b: Type)
      (wp1: st_wp_h heap a)
      (wp2: (a -> GTot (st_wp_h heap b)))
      (p: st_post_h heap b)
      (h0: heap)
     = wp1 (fun a h1 -> wp2 a p h1) h0

(** Branching for stateful WPs *)
unfold
let st_if_then_else
      (heap a p: Type)
      (wp_then wp_else: st_wp_h heap a)
      (post: st_post_h heap a)
      (h0: heap)
     = wp_then post h0 /\ (~p ==> wp_else post h0)

(** As with [PURE] the [wp] combinator names the postcondition as
    [k] to avoid duplicating it. *)
unfold
let st_ite_wp (heap a: Type) (wp: st_wp_h heap a) (post: st_post_h heap a) (h0: heap) =
  forall (k: st_post_h heap a).
    (forall (x: a) (h: heap). {:pattern (guard_free (k x h))} post x h ==> k x h) ==> wp k h0

(** Subsumption for stateful WPs *)
unfold
let st_stronger (heap a: Type) (wp1 wp2: st_wp_h heap a) =
  (forall (p: st_post_h heap a) (h: heap). wp1 p h ==> wp2 p h)

(** Closing the scope of a binder within a stateful WP *)
unfold
let st_close_wp (heap a b: Type) (wp: (b -> GTot (st_wp_h heap a))) (p: st_post_h heap a) (h: heap) =
  (forall (b: b). wp b p h)

(** Applying a stateful WP to a trivial postcondition *)
unfold
let st_trivial (heap a: Type) (wp: st_wp_h heap a) = (forall h0. wp (fun r h1 -> True) h0)

(** Introducing a new effect template [STATE_h] *)
new_effect {
  STATE_h (heap: Type) : result: Type -> wp: st_wp_h heap result -> Effect
  with
    return_wp = st_return heap
  ; bind_wp = st_bind_wp heap
  ; if_then_else = st_if_then_else heap
  ; ite_wp = st_ite_wp heap
  ; stronger = st_stronger heap
  ; close_wp = st_close_wp heap
  ; trivial = st_trivial heap
}

/// The [EXN] effect for computations that may raise exceptions or
/// fatal errors
///
/// Weakest preconditions for stateful computations transform
/// [ex_post] postconditions (predicates on [result]s) to [ex_pre]
/// precondition propositions.

(** Normal results are represented using [V x].
    Handleable exceptions are represented [E e].
    Fatal errors are [Err msg]. *)
noeq
type result (a: Type) =
  | V : v: a -> result a
  | E : e: exn -> result a
  | Err : msg: string -> result a

(** Exceptional preconditions are just propositions *)
let ex_pre = Type0

(** Postconditions on results refined by a precondition *)
let ex_post' (a pre: Type) = _: result a {pre} -> GTot Type0

(** Postconditions on results *)
let ex_post (a: Type) = ex_post' a True

(** Exceptions WP-predicate transformers *)
let ex_wp (a: Type) = ex_post a -> GTot ex_pre

(** Returning a value [x] normally promotes it to the [V x] result *)
unfold
let ex_return (a: Type) (x: a) (p: ex_post a) : GTot Type0 = p (V x)

(** Sequential composition of exception-raising code requires case analysing
    the result of the first computation before "running" the second one *)
unfold
let ex_bind_wp (a b: Type) (wp1: ex_wp a) (wp2: (a -> GTot (ex_wp b))) (p: ex_post b)
    : GTot Type0 =
  forall (k: ex_post b).
    (forall (rb: result b). {:pattern (guard_free (k rb))} p rb ==> k rb) ==>
    (wp1 (function
          | V ra1 -> wp2 ra1 k
          | E e -> k (E e)
          | Err m -> k (Err m)))

(** As for other effects, branching in [ex_wp] appears in two forms.
    First, a simple case analysis on [p] *)
unfold
let ex_if_then_else (a p: Type) (wp_then wp_else: ex_wp a) (post: ex_post a) =
  wp_then post /\ (~p ==> wp_else post)

(** Naming continuations for use with branching *)
unfold
let ex_ite_wp (a: Type) (wp: ex_wp a) (post: ex_post a) =
  forall (k: ex_post a).
    (forall (rb: result a). {:pattern (guard_free (k rb))} post rb ==> k rb) ==> wp k

(** Subsumption for exceptional WPs *)
unfold
let ex_stronger (a: Type) (wp1 wp2: ex_wp a) = (forall (p: ex_post a). wp1 p ==> wp2 p)

(** Closing the scope of a binder for exceptional WPs *)
unfold
let ex_close_wp (a b: Type) (wp: (b -> GTot (ex_wp a))) (p: ex_post a) = (forall (b: b). wp b p)

(** Applying a computation with a trivial postcondition *)
unfold
let ex_trivial (a: Type) (wp: ex_wp a) = wp (fun r -> True)

(** Introduce a new effect for [EXN] *)
new_effect {
  EXN : result: Type -> wp: ex_wp result -> Effect
  with
    return_wp = ex_return
  ; bind_wp = ex_bind_wp
  ; if_then_else = ex_if_then_else
  ; ite_wp = ex_ite_wp
  ; stronger = ex_stronger
  ; close_wp = ex_close_wp
  ; trivial = ex_trivial
}

(** A Hoare-style abbreviation for EXN *)
effect Exn (a: Type) (pre: ex_pre) (post: ex_post' a pre) =
  EXN a (fun (p: ex_post a) -> pre /\ (forall (r: result a). post r ==> p r))

(** We include divergence in exceptions.

    NOTE: BE WARNED, CODE IN THE [EXN] EFFECT IS ONLY CHECKED FOR
    PARTIAL CORRECTNESS *)
unfold
let lift_div_exn (a: Type) (wp: pure_wp a) (p: ex_post a) = wp (fun a -> p (V a))
sub_effect DIV ~> EXN { lift_wp = lift_div_exn }

(** A variant of [Exn] with trivial pre- and postconditions *)
effect Ex (a: Type) = Exn a True (fun v -> True)

/// The [ALL_h] effect template for computations that may diverge,
/// raise exceptions or fatal errors, and uses a generic state.
///
/// Note, this effect is poorly named, particularly as F* has since
/// gained many more user-defined effect. We no longer have an effect
/// that includes all others.
///
/// We might rename this in the future to something like [StExnDiv_h].
///
/// We layer state on top of exceptions, meaning that raising an
/// exception does not discard the state.
///
/// As with [STATE_h], [ALL_h] is not a computation type, though its
/// instantiation with a specific type of [heap] (in FStar.All) is.

(** [all_pre_h] is a predicate on the initial state *)
let all_pre_h (h: Type) = h -> GTot Type0

(** Postconditions relate [result]s to final [heap]s refined by a precondition *)
let all_post_h' (h a pre: Type) = result a -> _: h{pre} -> GTot Type0

(** A variant of [all_post_h'] without the precondition refinement *)
let all_post_h (h a: Type) = all_post_h' h a True

(** WP predicate transformers for the [All_h] effect template *)
let all_wp_h (h a: Type) = all_post_h h a -> Tot (all_pre_h h)

(** Returning a value [x] normally promotes it to the [V x] result
    without touching the [heap] *)
unfold
let all_return (heap a: Type) (x: a) (p: all_post_h heap a) = p (V x)

(** Sequential composition for [ALL_h] is like [EXN]: case analysis of
    the exceptional result before "running" the continuation *)
unfold
let all_bind_wp
      (heap: Type)
      (a b: Type)
      (wp1: all_wp_h heap a)
      (wp2: (a -> GTot (all_wp_h heap b)))
      (p: all_post_h heap b)
      (h0: heap)
    : GTot Type0 =
  wp1 (fun ra h1 ->
        (match ra with
          | V v -> wp2 v p h1
          | E e -> p (E e) h1
          | Err msg -> p (Err msg) h1))
    h0

(** Case analysis in [ALL_h] *)
unfold
let all_if_then_else
      (heap a p: Type)
      (wp_then wp_else: all_wp_h heap a)
      (post: all_post_h heap a)
      (h0: heap)
     = wp_then post h0 /\ (~p ==> wp_else post h0)

(** Naming postcondition for better sharing in [ALL_h] *)
unfold
let all_ite_wp (heap a: Type) (wp: all_wp_h heap a) (post: all_post_h heap a) (h0: heap) =
  forall (k: all_post_h heap a).
    (forall (x: result a) (h: heap). {:pattern (guard_free (k x h))} post x h ==> k x h) ==> wp k h0

(** Subsumption in [ALL_h] *)
unfold
let all_stronger (heap a: Type) (wp1 wp2: all_wp_h heap a) =
  (forall (p: all_post_h heap a) (h: heap). wp1 p h ==> wp2 p h)

(** Closing a binder in the scope of an [ALL_h] wp *)
unfold
let all_close_wp
      (heap a b: Type)
      (wp: (b -> GTot (all_wp_h heap a)))
      (p: all_post_h heap a)
      (h: heap)
     = (forall (b: b). wp b p h)

(** Applying an [ALL_h] wp to a trivial postcondition *)
unfold
let all_trivial (heap a: Type) (wp: all_wp_h heap a) = (forall (h0: heap). wp (fun r h1 -> True) h0)

(** Introducing the [ALL_h] effect template *)
new_effect {
  ALL_h (heap: Type) : a: Type -> wp: all_wp_h heap a -> Effect
  with
    return_wp = all_return heap
  ; bind_wp = all_bind_wp heap
  ; if_then_else = all_if_then_else heap
  ; ite_wp = all_ite_wp heap
  ; stronger = all_stronger heap
  ; close_wp = all_close_wp heap
  ; trivial = all_trivial heap
}

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
val inversion (a: Type) : Type0

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

/// Attributes:
///
/// An attribute is any F* term.
///
/// Attributes are desugared and checked for being well-scoped. But,
/// they are not type-checked.
///
/// It is associated with a definition using the [[@@attribute]]
/// notation, just preceding the definition.

(** We collect several internal ocaml attributes into a single
    inductive type.

    This may be unnecessary. In the future, we are likely to flatten
    this definition into several definitions of abstract top-level
    names.

    An example:

     {[
        [@@ CInline ] let f x = UInt32.(x +%^ 1)
      ]}

    is extracted to C by KaRaMeL to a C definition tagged with the
    [inline] qualifier. *)
type __internal_ocaml_attributes =
  | PpxDerivingShow (* Generate [@@@ deriving show ] on the resulting OCaml type *)
  | PpxDerivingShowConstant of string (* Similar, but for constant printers. *)
  | PpxDerivingYoJson (* Generate [@@@ deriving yojson ] on the resulting OCaml type *)
  | CInline
  (* KaRaMeL-only: generates a C "inline" attribute on the resulting
     * function declaration. When used on a local definition (i.e. a letbinding)
     KaRaMeL will try to inline this binding in the extracted C code. *)
  | Substitute
  (* KaRaMeL-only: forces KaRaMeL to inline the function at call-site; this is
     * deprecated and the recommended way is now to use F*'s
     * [inline_for_extraction], which now also works for stateful functions. *)
  | Gc
  (* KaRaMeL-only: instructs KaRaMeL to heap-allocate any value of this
     * data-type; this requires running with a conservative GC as the
     * allocations are not freed. *)
  | Comment of string
  (* KaRaMeL-only: attach a comment to the declaration. Note that using F*-doc
     * syntax automatically fills in this attribute. *)
  | CPrologue of string
  (* KaRaMeL-only: verbatim C code to be prepended to the declaration.
     * Multiple attributes are valid and accumulate, separated by newlines. *)
  | CEpilogue of string (* Ibid. *)
  | CConst of string
  (* KaRaMeL-only: indicates that the parameter with that name is to be marked
     * as C const.  This will be checked by the C compiler, not by KaRaMeL or F*.
     *
     * This is deprecated and doesn't work as intended. Use
     * LowStar.ConstBuffer.fst instead! *)
  | CCConv of string (* A calling convention for C, one of stdcall, cdecl, fastcall *)
  | CAbstractStruct
  (* KaRaMeL-only: for types that compile to struct types (records and
     * inductives), indicate that the header file should only contain a forward
     * declaration, which in turn forces the client to only ever use this type
     * through a pointer. *)
  | CIfDef (* KaRaMeL-only: on a given `val foo`, compile if foo with #ifdef. *)
  | CMacro
(* KaRaMeL-only: for a top-level `let v = e`, compile as a macro *)
  | CNoInline
    (* For security-sensitive functions only: generate special attributes in C
       to prevent inlining; if the function is subjected to a -static-header
       option, the `inline` attribute will be removed, but the static will
       remain. *)

(** The [inline_let] attribute on a local let-binding, instructs the
    extraction pipeline to inline the definition. This may be both to
    avoid generating unnecessary intermediate variables, and also to
    enable further partial evaluation. Note, use this with care, since
    inlining all lets can lead to an exponential blowup in code
    size. *)
val inline_let : unit

(** The [rename_let] attribute support a form of metaprogramming for
    the names of let-bound variables used in extracted code.

    This is useful, particularly in conjunction with partial
    evaluation, to ensure that names reflect their usage context.

    See tests/micro-benchmarks/Renaming*.fst *)
val rename_let (new_name: string) : Tot unit

(** The [plugin] attribute is used in conjunction with native
    compilation of F* components, accelerating their reduction
    relative to the default strategy of just interpreting them.

    See examples/native_tactics for several examples. *)
val plugin (x: int) : Tot unit

(** An attribute to mark things that the typechecker should *first*
    elaborate and typecheck, but unfold before verification. *)
val tcnorm : unit

(** We erase all ghost functions and unit-returning pure functions to
    [()] at extraction. This creates a small issue with abstract
    types. Consider a module that defines an abstract type [t] whose
    (internal) definition is [unit] and also defines [f: int -> t]. [f]
    would be erased to be just [()] inside the module, while the
    client calls to [f] would not, since [t] is abstract. To get
    around this, when extracting interfaces, if we encounter an
    abstract type, we tag it with this attribute, so that
    extraction can treat it specially.

    Note, since the use of cross-module inlining (the [--cmi] option),
    this attribute is no longer necessary. We retain it for legacy,
    but will remove it in the future. *)
val must_erase_for_extraction : unit

(** This attribute is used with the Dijkstra Monads for Free
    construction to track position information in generated VCs *)
val dm4f_bind_range : unit

(** When attached a top-level definition, the typechecker will succeed
    if and only if checking the definition results in an error. The
    error number list is actually OPTIONAL. If present, it will be
    checked that the definition raises exactly those errors in the
    specified multiplicity, but order does not matter. *)
val expect_failure (errs: list int) : Tot unit

(** When --admit_smt_queries true is present, with the previous attribute since some
  definitions only fail when verification is turned on. With this
  attribute, one can ensure that a definition fails while lax-checking
  too. Same semantics as above, but lax mode will be turned on for the
  definition.  *)
val expect_lax_failure (errs: list int) : Tot unit

(** Print the time it took to typecheck a top-level definition *)
val tcdecltime : unit

(** This attribute is to be used as a hint for the unifier.  A
    function-typed symbol `t` marked with this attribute will be treated
    as being injective in all its arguments by the unifier.  That is,
    given a problem `t a1..an =?= t b1..bn` the unifier will solve it by
    proving `ai =?= bi` for all `i`, without trying to unfold the
    definition of `t`. *)
val unifier_hint_injective : unit

(**
 This attribute is used to control the evaluation order
 and unfolding strategy for certain definitions.

  In particular, given
     {[
        [@@(strict_on_arguments [1;2])]
        let f x0 (x1:list x0) (x1:option x0) = e
     ]}

 An application [f e0 e1 e2] is reduced by the normalizer by:

     1. evaluating [e0 ~>* v0, e1 ~>* v1, e2 ~>* v2]

     2 a.
        If, according to the positional arguments [1;2],
        if v1 and v2 have constant head symbols
              (e.g., v1 = Cons _ _ _, and v2 = None _)
       then [f] is unfolded to [e] and reduced as
         {[e[v0/x0][v1/x1][v2/x2]]}

     2 b.

      Otherwise, [f] is not unfolded and the term is [f e0 e1 e2]
      reduces to [f v0 v1 v2]. *)
val strict_on_arguments (x: list int) : Tot unit

(**
 * An attribute to tag a tactic designated to solve any
 * unsolved implicit arguments remaining at the end of type inference.
 **)
val resolve_implicits : unit

(**
 * Implicit arguments can be tagged with an attribute [abc] to dispatch 
 * their solving to a user-defined tactic also tagged with the same 
 * attribute and resolve_implicits [@@abc; resolve_implicits]. 
 
 * However, sometimes it is useful to have multiple such 
 * [abc]-tagged tactics in scope. In such a scenario, to choose among them, 
 * one can use the attribute as shown below to declare that [t] overrides
 * all the tactics [t1...tn] and should be used to solve [abc]-tagged 
 * implicits, so long as [t] is not iself overridden by some other tactic.

   [@@resolve_implicits; abc; override_resolve_implicits_handler abc [`%t1; ... `%tn]]
   let t = e

 **)
val override_resolve_implicits_handler : #a:Type -> a -> list string -> Tot unit

(** A tactic registered to solve implicits with the (handle_smt_goals)
    attribute will receive the SMT goal generated during typechecking
    just before it is passed to the SMT solver.
   *)
val handle_smt_goals : unit

(** This attribute can be added to an inductive type definition,
    indicating that it should be erased on extraction to `unit`.

    However, any pattern matching on the inductive type results
    in a `Ghost` effect, ensuring that computationally relevant
    code cannot rely on the values of the erasable type.

    See tests/micro-benchmarks/Erasable.fst, for examples.  Also
    see https://github.com/FStarLang/FStar/issues/1844 *)
val erasable : unit

(** [commute_nested_matches]
    This attribute can be used to decorate an inductive type [t]

    During normalization, if reduction is blocked on matching the
    constructors of [t] in the following sense:

    [
     match (match e0 with | P1 -> e1 | ... | Pn -> en) with
     | Q1 -> f1 ... | Qm -> fm
    ]

    i.e., the outer match is stuck due to the inner match on [e0]
    being stuck, and if the head constructor the outer [Qi] patterns
    are the constructors of the decorated inductive type [t], then,
    this is reduced to

    [
     match e0 with
     | P1 -> (match e1 with | Q1 -> f1 ... | Qm -> fm)
     | ...
     | Pn -> (match en with | Q1 -> f1 ... | Qm -> fm)
    ]

    This is sometimes useful when partially evaluating code before
    extraction, particularly when aiming to obtain first-order code
    for KaRaMeL. However, this attribute should be used with care,
    since if after the rewriting the inner matches do not reduce, then
    this can cause an explosion in code size.

    See tests/micro-benchmarks/CommuteNestedMatches.fst
    and examples/layeredeffects/LowParseWriters.fsti
  *)
val commute_nested_matches : unit

(** This attribute controls extraction: it can be used to disable
    extraction of a given top-level definition into a specific backend,
    such as "OCaml". If any extracted code must call into an erased
    function, an error will be raised (code 340).
  *)
val noextract_to (backend:string) : Tot unit


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


(** A layered effect definition may optionally be annotated with
    (ite_soundness_by t) attribute, where t is another attribute
    When so, the implicits and the smt guard generated when
    checking the soundness of the if-then-else combinator, are
    dispatched to the tactic in scope that has the t attribute (in addition
    to the resolve_implicits attribute as usual)

    See examples/layeredeffects/IteSoundess.fst for a few examples
  *)
val ite_soundness_by (attribute: unit): Tot unit

(** By-default functions that have a layered effect, need to have a type
    annotation for their bodies
    However, a layered effect definition may contain the default_effect
    attribute to indicate to the typechecker that for missing annotations,
    use the default effect.
    The default effect attribute takes as argument a string, that is the name
    of the default effect, two caveats:
      - The argument must be a string constant (not a name, for example)
      - The argument should be the fully qualified name
    For example, the TAC effect in FStar.Tactics.Effect.fsti specifies
    its default effect as FStar.Tactics.Tac
    F* will typecheck that the default effect only takes one argument,
      the result type of the computation
  *)
val default_effect (s:string) : Tot unit

(** A layered effect may optionally be annotated with the
    top_level_effect attribute so indicate that this effect may
    appear at the top-level
    (e.g., a top-level let x = e, where e has a layered effect type)

    The top_level_effect attribute takes (optional) string argument, that is the
    name of the effect abbreviation that may constrain effect arguments
    for the top-level effect

    As with default effect, the string argument must be a string constant,
    and fully qualified

    E.g. a Hoare-style effect `M a pre post`, may have the attribute
    `@@ top_level_effect "N"`, where the effect abbreviation `N` may be:

    effect N a post = M a True post

    i.e., enforcing a trivial precondition if `M` appears at the top-level

    If the argument to `top_level_effect` is absent, then the effect itself
    is allowed at the top-level with any effect arguments

    See tests/micro-benchmarks/TopLevelIndexedEffects.fst for examples

    *)
val top_level_effect (s:string) : Tot unit

(** This attribute can be annotated on the binders in an effect signature
    to indicate that they are effect parameters. For example, for a
    state effect that is parametric in the type of the state, the state
    index may be marked as an effect parameter.

    Also see https://github.com/FStarLang/FStar/wiki/Indexed-effects

    *)
val effect_param : unit

(** Bind definition for a layered effect may optionally contain range
    arguments, that are provided by the typechecker during reification
    This attribute on the effect definition indicates that the bind
    has range arguments.
    See for example the TAC effect in FStar.Tactics.Effect.fsti
  *)
val bind_has_range_args : unit


(** An indexed effect definition may be annotated with
    this attribute to indicate that the effect should be
    extracted "natively". E.g., the `bind` of the effect is
    extracted to primitive `let` bindings

    As an example, `Steel` effects (the effect for concurrent
    separation logic) are marked as such

  *)
val primitive_extraction : unit

(** A qualifier on a type definition which when used in co-domain position
    on an arrow type will be extracted as if it were an impure effect type.

    e.g., if you have
    
    [@@extract_as_impure_effect]
    val stt (a:Type) (pre:_) (post:_) : Type

    then arrows of the form `a -> stt b p q` will be extracted 
    similarly to `a -> Dv b`.
 *)
val extract_as_impure_effect : unit


(** A binder in a definition/declaration may optionally be annotated as strictly_positive
    When the let definition is used in a data constructor type in an inductive
    definition, this annotation is used to check the positivity of the inductive

    Further F* checks that the binder is actually positive in the let definition

    See tests/micro-benchmarks/Positivity.fst and NegativeTests.Positivity.fst for a few examples
  *)
val strictly_positive : unit

(** A binder in a definition/declaration may optionally be annotated as unused.
    This is used in the strict positivity checker. E.g., a type such as the one
    below is accepted
    
    let f ([@@@unused] a:Type) = unit
    type t = | MkT: f t -> t
    
    F* checks that the binder is actually unused in the definition

    See tests/micro-benchmarks/Positivity.fst for a few examples
  *)
val unused : unit

(** This attribute may be added to an inductive type
    to disable auto generated projectors

    Normally there should not be any need to use this unless:
    for some reason F* cannot typecheck the auto-generated projectors.
    
    Another reason to use this attribute may be to avoid generating and
    typechecking lot of projectors, most of which are not going to be used
    in the rest of the program
  *)
val no_auto_projectors : unit

(** As [no_auto_projectors] but also do not even generate declarations
    for them. *)
val no_auto_projectors_decls : unit

(** This attribute can be added to a let definition
    and indicates to the typechecker to typecheck the signature of the definition
    without using subtyping. This is sometimes useful for indicating that a lemma
    can be applied by the tactic engine without requiring to check additional
    subtyping obligations
*)
val no_subtyping : unit

val admit_termination : unit

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

val coercion : unit

(** Marks a record type as being the result of an automatic desugar of
    a constructor with a record payload.
    For example, in a module `M`, `type foo = | A {x: int}` desugars
    to the type `M.foo` and a type `M.foo__A__payload`. That latter
    type `foo__A__payload` is decorated with an attribute
    `desugar_of_variant_record ["M.A"]`. *)
val desugar_of_variant_record (type_name: string): unit

(** Tag for implicits that are to be solved by a tactic. *)
val defer_to (#a:Type) (tag : a) : unit
