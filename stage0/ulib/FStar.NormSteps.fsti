[@@"no_prelude"]
module FStar.NormSteps

open Prims

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

(** Like [delta_only], unfold only the definitions in this list,
but do so only once. This is useful for a controlled unfolding
of recursive definitions. NOTE: if there are many occurrences
of a variable in this list, it is unspecified which one will
be unfolded (currently it depends on normalization order). *)
val delta_once (s: list string) : Tot norm_step

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
