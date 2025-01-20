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

module FStar.Classical

/// This module provides various utilities to manipulate the squashed
/// logical connectives [==>], [/\], [\/], [forall], [exists] and [==],
/// defined in Prims in terms of the [squash] type. See Prims and
/// FStar.Squash for basic explanations of the [squash] type.
///
/// In summary:
///
/// - [squash p] is proof-irrelevant proof of [p], expressed as a unit
///   refinement.
///
/// - [Lemma p] is also a proof-irrelevant proof of [p], expressed as
///   a postcondition of a unit-returning Ghost computation.
///
/// We provide several utilities to turn proofs of various
/// propositions with non-trivial proof terms into proof-irrelevant,
/// classical proofs.

(** [give_witness x] transforms a constructive proof [x:a] into a
    proof-irrelevant postcondition. It is similar to
    [FStar.Squash.return_squash] *)
val give_witness (#a: Type) (_: a) : Lemma (ensures a)

(** [give_witness_from_squash s] moves from a unit-refinement to a
    postcondition. It is similar to [FStar.Squash.give_proof] *)
val give_witness_from_squash (#a: Type) (_: squash a) : Lemma (ensures a)

(** This turns a proof-irrelevant postcondition into a squashed proof *)
val lemma_to_squash_gtot (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> Lemma (p x))) (x: a)
    : GTot (squash (p x))

(**** Equality *)

(** Turning an equality precondition into returned squash proof,
    similar to [FStar.Squash.get_proof], but avoiding an extra squash,
    since [==] is already squashed. *)
val get_equality (#t: Type) (a b: t) : Pure (a == b) (requires (a == b)) (ensures (fun _ -> True))

(**** Implication *)

(** Turning an [a ==> b] into a [squash a -> squash b]. Note [a ==> b] is
    defined as [squash (a -> b)], so this distributes the squash over the arrow. *)
val impl_to_arrow (#a #b: Type0) (_: (a ==> b)) (_: squash a) : Tot (squash b)

(** The converse of [impl_to_arrow] *)
val arrow_to_impl (#a #b: Type0) (_: (squash a -> GTot (squash b))) : GTot (a ==> b)

(** Similar to [arrow_to_impl], but without squashing proofs on the left *)
val impl_intro_gtot (#p #q: Type0) ($_: (p -> GTot q)) : GTot (p ==> q)

(** Similar to [impl_intro_gtot], but for a Tot arrow *)
val impl_intro_tot (#p #q: Type0) ($_: (p -> Tot q)) : Tot (p ==> q)

(** Similar to [arrow_to_impl], but not squashing the proof of [p] on the LHS. *)
val impl_intro (#p #q: Type0) ($_: (p -> Lemma q)) : Lemma (p ==> q)

(** A lemma with a precondition can also be treated as a proof a quantified implication.

    See the remark at the top of this section comparing nested lemmas
    with SMT pattern to [move_requires] and [forall_intro] *)
val move_requires
      (#a: Type)
      (#p #q: (a -> Type))
      ($_: (x: a -> Lemma (requires (p x)) (ensures (q x))))
      (x: a)
    : Lemma (p x ==> q x)

(** The arity 2 version of [move_requires] *)
val move_requires_2
      (#a: Type)
      (#b: (a -> Type))
      (#p #q: (x: a -> b x -> Type))
      ($_: (x: a -> y: b x -> Lemma (requires (p x y)) (ensures (q x y))))
      (x: a)
      (y: b x)
    : Lemma (p x y ==> q x y)

(** The arity 3 version of [move_requires] *)
val move_requires_3
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p #q: (x: a -> y: b x -> c x y -> Type))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (requires (p x y z)) (ensures (q x y z))))
      (x: a)
      (y: b x)
      (z: c x y)
    : Lemma (p x y z ==> q x y z)

(** The arity 4 version of [move_requires] *)
val move_requires_4
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p #q: (x: a -> y: b x -> z: c x y -> w: d x y z -> Type))
      ($_: (x: a -> y: b x -> z: c x y -> w: d x y z -> Lemma (requires (p x y z w)) (ensures (q x y z w))))
      (x: a)
      (y: b x)
      (z: c x y)
      (w: d x y z)
    : Lemma (p x y z w ==> q x y z w)

(** When proving predicate [q] whose well-formedness depends on the
    predicate [p], it is convenient to have [q] appear only under a
    context where [p] is know to be valid. *)
val impl_intro_gen (#p: Type0) (#q: (squash p -> Tot Type0)) (_: (squash p -> Lemma (q ())))
    : Lemma (p ==> q ())

(**** Universal quantification *)

/// Many of the utilities for universal quantification are designed to
/// help in the proofs of lemmas that ensure quantified
/// postconditions. For example, in order to prove [Lemma (forall
/// (x:a). p x)] it is often useful to "get your hands" on a freshly
/// introduced variable [x] and to prove [p x] for it, i.e., to prove
/// [x:a -> Lemma (p x)] and to turn this into a proof for [forall
/// x. p x]. Functions like [forall_intro] in this module let you do
/// just that.
///
/// That said, it may often be more convenient to prove such
/// properties using local lemmas in inner scopes. For example, here
/// are two proof sketches for [forall x. p x].
///
/// {[
///    assume
///    val p : nat -> prop
///
///    let proof1 =
///      let lem (x:nat)
///        : Lemma (ensures p x)
///        = admit()
///      in
///      forall_intro lem;
///      assert (forall x. p x)
///
///    let proof2 =
///      let lem (x:nat)
///        : Lemma (ensures p x)
///                [SMTPat (p x)]
///        = admit()
///      in
///      assert (forall x. p x)
/// ]}
///
/// In [proof1], we prove an auxiliary lemma [lem] and then use
/// [forall_intro] to turn it into a proof of [forall x. p x].
///
/// In [proof2], we simply decorate [lem] with an SMT pattern to
/// allow the solver to use that lemma to prove [forall x. p x]
/// directly.
///
/// The style of [proof2] is often more robust for several reasons:
///
///  - [forall_intro] only works with lemmas that do not have
///    preconditions. E.g., if you wanted to prove [forall x. q x ==>
///    p x], you would have had to prove [lem] with the type [x:nat ->
///    Lemma (q x ==> p x)]. In contrast, in the style of [proof2],
///    you could have proven [x:nat -> Lemma (requires q x) (ensures p
///    x)], which is easier, since you can assume the precondition [q
///    x]. To use this style of lemma-with-precondition with
///    [forall_intro], one typically must also use [move_requires] to
///    coerce a lemma with a precondition into a lemma proving an
///    implication, or to use [ghost_lemma].
///
///  - [forall_intro] introduces a quantifier without an SMT
///    pattern. This can pollute the local context with an unguarded
///    quantifier, leading to inefficient proofs. Note, the variants
///    [forall_intro_with_pat] help with this somewhat, but they only
///    support a single pattern, rather than conjunctive and
///    disjunctive patterns.
///
///  - [forall_intro] and its variants are available for only a fixed
///    arity up to 4. The nested SMTPat lemma style of [proof2] works
///    are arbitrary arity.
///
/// That said, there may still be cases where [forall_intro] etc. are
/// more suitable.

(** Turning an universally quantified precondition into returned
    squash proof, similar to [FStar.Squash.get_proof], but avoiding an
    extra squash, since [forall] is already squashed. *)
val get_forall (#a: Type) (p: (a -> GTot Type0))
    : Pure (forall (x: a). p x) (requires (forall (x: a). p x)) (ensures (fun _ -> True))

(** This introduces a squash proof of a universal
    quantifier. [forall_intro_gtot f] is equivalent to [return_squash
    (return_squash f)].

    TODO: Perhaps remove this? It seems redundant *)
val forall_intro_gtot (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> GTot (p x)))
    : Tot (squash (forall (x: a). p x))

(** This turns a dependent arrow into a proof-irrelevant postcondition
    of a universal quantifier. *)
val lemma_forall_intro_gtot (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> GTot (p x)))
    : Lemma (forall (x: a). p x)

(** This turns a dependent arrow producing a proof a [p] into a lemma
    ensuring [p], effectively squashing the proof of [p], while still
    retaining the arrow. *)
val gtot_to_lemma (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> GTot (p x))) (x: a) : Lemma (p x)

(** This is the analog of [lemma_forall_intro_gtot] but with squashed
    proofs on both sides, including a redundant extra squash on the result.

    TODO: perhaps remove this? *)
val forall_intro_squash_gtot (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> GTot (squash (p x))))
    : Tot (squash (forall (x: a). p x))

(** This is the analog of [lemma_forall_intro_gtot] but with squashed
    proofs on both sides *)
val forall_intro_squash_gtot_join
      (#a: Type)
      (#p: (a -> GTot Type))
      ($_: (x: a -> GTot (squash (p x))))
    : Tot (forall (x: a). p x)

(** The main workhorse for introducing universally quantified postconditions, at arity 1.

    See the remark at the start of this section for guidelines on its
    use. You may prefer to use a local lemma with an SMT pattern. *)
val forall_intro (#a: Type) (#p: (a -> GTot Type)) ($_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). p x)

(** The main workhorse for introducing universally quantified
    postconditions, at arity 1, including a provision for a single
    pattern.

    See the remark at the start of this section for guidelines on its
    use. You may prefer to use a local lemma with an SMT pattern. *)
val forall_intro_with_pat
      (#a: Type)
      (#c: (x: a -> Type))
      (#p: (x: a -> GTot Type0))
      ($pat: (x: a -> Tot (c x)))
      ($_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). {:pattern (pat x)} p x)

(** This function is almost identical to [forall_intro]. The only
    difference is that rather in [forall_intro f] the type of [f] is
    _unified_ with expected type of that argument, leading to better
    resolution of implicit variables.

    However, sometimes it is convenient to introduce a quantifier from
    a lemma while relying on subtyping---[forall_intro_sub f] allows
    the use of subtyping when comparing the type of [f] to the
    expected type of the argument. This will likely mean that the
    implicit arguments, notably [p], will have to be provided
    explicilty. *)
val forall_intro_sub (#a: Type) (#p: (a -> GTot Type)) (_: (x: a -> Lemma (p x)))
    : Lemma (forall (x: a). p x)

(** The arity 2 version of [forall_intro] *)
val forall_intro_2
      (#a: Type)
      (#b: (a -> Type))
      (#p: (x: a -> b x -> GTot Type0))
      ($_: (x: a -> y: b x -> Lemma (p x y)))
    : Lemma (forall (x: a) (y: b x). p x y)

(** The arity 2 version of [forall_intro_with_pat] *)
val forall_intro_2_with_pat
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p: (x: a -> b x -> GTot Type0))
      ($pat: (x: a -> y: b x -> Tot (c x y)))
      ($_: (x: a -> y: b x -> Lemma (p x y)))
    : Lemma (forall (x: a) (y: b x). {:pattern (pat x y)} p x y)

(** The arity 3 version of [forall_intro] *)
val forall_intro_3
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> Type0))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (p x y z)))
    : Lemma (forall (x: a) (y: b x) (z: c x y). p x y z)

(** The arity 3 version of [forall_intro_with_pat] *)
val forall_intro_3_with_pat
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> GTot Type0))
      ($pat: (x: a -> y: b x -> z: c x y -> Tot (d x y z)))
      ($_: (x: a -> y: b x -> z: c x y -> Lemma (p x y z)))
    : Lemma (forall (x: a) (y: b x) (z: c x y). {:pattern (pat x y z)} p x y z)

(** The arity 4 version of [forall_intro] *)
val forall_intro_4
      (#a: Type)
      (#b: (a -> Type))
      (#c: (x: a -> y: b x -> Type))
      (#d: (x: a -> y: b x -> z: c x y -> Type))
      (#p: (x: a -> y: b x -> z: c x y -> w: d x y z -> Type0))
      ($_: (x: a -> y: b x -> z: c x y -> w: d x y z -> Lemma (p x y z w)))
    : Lemma (forall (x: a) (y: b x) (z: c x y) (w: d x y z). p x y z w)

(** This combines th use of [arrow_to_impl] with [forall_intro].

    TODO: Seems overly specific; could be removed?  *)
val forall_impl_intro
      (#a: Type)
      (#p #q: (a -> GTot Type))
      ($_: (x: a -> squash (p x) -> Lemma (q x)))
    : Lemma (forall x. p x ==> q x)

(** This is similar to [forall_intro], but with a lemma that has a precondition.

    Note: It's unclear why [q] has an additional [unit] argument.
  *)
val ghost_lemma
      (#a: Type)
      (#p: (a -> GTot Type0))
      (#q: (a -> unit -> GTot Type0))
      ($_: (x: a -> Lemma (requires p x) (ensures (q x ()))))
    : Lemma (forall (x: a). p x ==> q x ())


(**** Existential quantification *)

(** The most basic way to introduce a squashed existential quantifier
    [exists x. p x] is to present a witness [w] such that [p w].

    While [exists_intro] is very explicit, as with universal
    quantification and [forall_intro], it is only available for a
    fixed arity.

    However, unlike with we do not yet provide any conveniences for
    higher arities. One workaround is to tuple witnesses together,
    e.g., instead of proving [exists x y. p x y] to prove instead
    [exists xy. p (fst xy) (snd xy)] and to allow the SMT solver to convert
    the latter to the former. *)
val exists_intro (#a: Type) (p: (a -> Type)) (witness: a)
    : Lemma (requires (p witness)) (ensures (exists (x: a). p x))

(** Introducing an exists via its classical correspondence with a negated universal quantifier *)
val exists_intro_not_all_not
      (#a: Type)
      (#p: (a -> Type))
      ($f: ((x: a -> Lemma (~(p x))) -> Lemma False))
    : Lemma (exists x. p x)

(** If [r] is true for all [x:a{p x}], then one can use
    [forall_to_exists] to establish [(exists x. p x) ==> r]. *)
val forall_to_exists (#a: Type) (#p: (a -> Type)) (#r: Type) ($_: (x: a -> Lemma (p x ==> r)))
    : Lemma ((exists (x: a). p x) ==> r)

(** The arity two variant of [forall_to_exists] for two separate
    existentially quantified hypotheses.

    TODO: overly specific, remove? *)
val forall_to_exists_2
      (#a: Type)
      (#p: (a -> Type))
      (#b: Type)
      (#q: (b -> Type))
      (#r: Type)
      ($f: (x: a -> y: b -> Lemma ((p x /\ q y) ==> r)))
    : Lemma (((exists (x: a). p x) /\ (exists (y: b). q y)) ==> r)

(** An eliminator for squashed existentials: If every witness can be
    eliminated into a squashed proof of the [goal], then the [goal]
    postcondition is valid. *)
val exists_elim
      (goal #a: Type)
      (#p: (a -> Type))
      (_: squash (exists (x: a). p x))
      (_: (x: a{p x} -> GTot (squash goal)))
    : Lemma goal


(*** Disjunction *)

(** Eliminating [l \/ r] into a [goal] whose well-formedness depends on
    [l \/ r] *)
val or_elim
      (#l #r: Type0)
      (#goal: (squash (l \/ r) -> Tot Type0))
      (hl: (squash l -> Lemma (goal ())))
      (hr: (squash r -> Lemma (goal ())))
    : Lemma ((l \/ r) ==> goal ())

(** The law of excluded middle: squashed types are classical *)
val excluded_middle (p: Type) : Lemma (requires (True)) (ensures (p \/ ~p))
