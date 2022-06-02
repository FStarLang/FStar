(*
   Copyright 2020 Microsoft Research

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
module Steel.ST.Util
(** This module aggregates several of the core effects and utilities
    associated with the Steel.ST namespace.

    Client modules should typically just [open Steel.ST.Util] and
    that should bring most of what they need in scope.
*)
open FStar.Ghost
open Steel.Memory
open Steel.ST.Effect.Ghost
module U = FStar.Universe
include Steel.FractionalPermission
include Steel.Memory
include Steel.Effect.Common
include Steel.ST.Effect
include Steel.ST.Effect.Atomic
include Steel.ST.Effect.Ghost

module T = FStar.Tactics

/// Weaken a vprop from [p] to [q]
/// of every memory validating [p] also validates [q]
val weaken (#opened:inames)
           (p q:vprop)
           (l:(m:mem) -> Lemma
                           (requires interp (hp_of p) m)
                           (ensures interp (hp_of q) m))
  : STGhostT unit opened p (fun _ -> q)

/// Rewrite [p] to [q] when they are equal
val rewrite (#opened:inames)
            (p q: vprop)
  : STGhost unit opened p (fun _ -> q) (p == q) (fun _ -> True)

/// Rewrite p to q, proving their equivalence using the framing tactic
/// Most places, this rewriting kicks in automatically in the framework,
///   but sometimes it is useful to explicitly rewrite, while farming AC reasoning
///   to the tactic
val rewrite_with_tactic (#opened:_) (p q:vprop)
  : STGhost unit opened
      p
      (fun _ -> q)
      (requires T.with_tactic init_resolve_tac (squash (p `equiv` q)))
      (ensures fun _ -> True)

/// This rewrite is useful when you have equiv predicate in the logical context
/// Internally implemented using `weaken`
val rewrite_equiv (#opened:_) (p q:vprop)
  : STGhost unit opened p (fun _ -> q)
      (requires equiv p q \/ equiv q p)
      (ensures fun _ -> True)

/// A noop operator, occasionally useful for forcing framing of a
/// subsequent computation
val noop (#opened:inames) (_:unit)
  : STGhostT unit opened emp (fun _ -> emp)

/// Asserts the validity of vprop [p] in the current context
val assert_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants p (fun _ -> p)

/// Allows assuming [p] for free
/// See also Steel.ST.Effect.Ghost.admit_
[@@warn_on_use "uses an axiom"]
val assume_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants emp (fun _ -> p)

/// Drops vprop [p] from the context. Although our separation logic is
/// affine, the frame inference tactic treats it as linear.
/// Leveraging affinity requires a call from the user to this helper,
/// to avoid implicit memory leaks.  This should only be used for pure
/// and ghost vprops
val drop (#opened:inames) (p:vprop) : STGhostT unit opened p (fun _ -> emp)

/// A pure vprop
val pure (p: prop) : vprop

val reveal_pure (p: prop) : Lemma (pure p == Steel.Effect.Common.pure p)

/// Introduce a pure vprop, when [p] is valid in the context
val intro_pure (#uses:_) (p:prop)
  : STGhost unit uses emp (fun _ -> pure p) p (fun _ -> True)

/// Eliminate a pure vprop, gaining that p is valid in the context
val elim_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> emp) True (fun _ -> p)

/// Extracting a proposition from a [pure p] while retaining [pure p]
val extract_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> pure p) True (fun _ -> p)

/// Useful lemmas to make the framing tactic automatically handle `pure`

[@@solve_can_be_split_lookup; (solve_can_be_split_for pure)]
val intro_can_be_split_pure
  (p: prop)
  (sq: squash p)
: Lemma (emp `can_be_split` pure p)

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for pure)]
val intro_can_be_split_forall_dep_pure
  (#a: Type)
  (p: a -> Tot prop)
: Lemma (can_be_split_forall_dep p (fun _ -> emp) (fun x -> pure (p x)))

/// It's generally good practice to end a computation with a [return].
///
/// It becomes necessary when combining ghost and non-ghost
/// computations, so it is often less surprising to always write it.
///
/// Because of the left-associative structure of F* computations, this
/// is necessary when a computation is atomic and returning a value
/// with an informative type, but the previous computation was ghost.
/// Else, the returned value will be given type SteelGhost, and F*
/// will fail to typecheck the program as it will try to lift a
/// SteelGhost computation with an informative return type
[@@noextract_to "Plugin"]
val return (#a:Type u#a)
           (#opened_invariants:inames)
           (#p:a -> vprop)
           (x:a)
  : STAtomicBase a true opened_invariants Unobservable
                 (return_pre (p x)) p
                 True
                 (fun v -> v == x)

/// An existential quantifier for vprop
val exists_ (#a:Type u#a) (p:a -> vprop) : vprop

/// Useful lemmas to make the framing tactic automatically handle `exists_`
[@@solve_can_be_split_lookup; (solve_can_be_split_for exists_)]
val intro_can_be_split_exists (a:Type) (x:a) (p: a -> vprop)
  : Lemma
    (ensures (p x `can_be_split` (exists_ p)))

[@@solve_can_be_split_forall_dep_lookup; (solve_can_be_split_forall_dep_for exists_)]
val intro_can_be_split_forall_dep_exists (b:Type) (a: b -> Type)
                           (x: (u: b) -> GTot (a u))
                           (p: (u: b) -> a u -> vprop)
  : Lemma
    (ensures (fun (y:b) -> p y (x y)) `(can_be_split_forall_dep (fun _ -> True))` (fun (y:b) -> exists_ (p y)))

/// Introducing an existential if the predicate [p] currently holds for value [x]
val intro_exists (#a:Type) (#opened_invariants:_) (x:a) (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Variant of intro_exists above, when the witness is a ghost value
val intro_exists_erased (#a:Type)
                        (#opened_invariants:_)
                        (x:Ghost.erased a)
                        (p:a -> vprop)
  : STGhostT unit opened_invariants (p x) (fun _ -> exists_ p)

/// Extracting a witness for predicate [p] if it currently holds for some [x]
val elim_exists (#a:Type)
                (#opened_invariants:_)
                (#p:a -> vprop)
                (_:unit)
  : STGhostT (Ghost.erased a) opened_invariants
             (exists_ p)
             (fun x -> p x)

/// Lifting the existentially quantified predicate to a higher universe
val lift_exists (#a:_)
                (#u:_)
                (p:a -> vprop)
  : STGhostT unit u
             (exists_ p)
             (fun _a -> exists_ #(U.raise_t a) (U.lift_dom p))

/// If two predicates [p] and [q] are equivalent, then their existentially quantified versions
/// are equivalent, and we can switch from `h_exists p` to `h_exists q`
val exists_equiv (#a:_)
                (p:a -> vprop)
                (q:a -> vprop {forall x. equiv (p x) (q x) })
  : Lemma (equiv (exists_ p) (exists_ q))

val exists_cong (#a:_)
                (#u:_)
                (p:a -> vprop)
                (q:a -> vprop {forall x. equiv (p x) (q x) })
  : STGhostT unit u
             (exists_ p)
             (fun _ -> exists_ q)

/// Creation of a new invariant associated to vprop [p].
/// After execution of this function, [p] is consumed and not available in the context anymore
val new_invariant (#opened_invariants:inames) (p:vprop)
  : STGhostT (inv p) opened_invariants p (fun _ -> emp)

/// Atomically executing function [f] which relies on the predicate [p] stored in invariant [i]
/// as long as it maintains the validity of [p]
/// This requires invariant [i] to not belong to the set of currently opened invariants.
[@@noextract_to "Plugin"]
val with_invariant (#a:Type)
                   (#fp:vprop)
                   (#fp':a -> vprop)
                   (#opened_invariants:inames)
                   (#p:vprop)
                   (i:inv p{not (mem_inv opened_invariants i)})
                   ($f:unit -> STAtomicT a (add_inv opened_invariants i)
                                          (p `star` fp)
                                          (fun x -> p `star` fp' x))
  : STAtomicT a opened_invariants fp fp'

/// Variant of the above combinator for ghost computations
val with_invariant_g (#a:Type)
                     (#fp:vprop)
                     (#fp':a -> vprop)
                     (#opened_invariants:inames)
                     (#p:vprop)
                     (i:inv p{not (mem_inv opened_invariants i)})
                     ($f:unit -> STGhostT a (add_inv opened_invariants i)
                                         (p `star` fp)
                                         (fun x -> p `star` fp' x))
  : STGhostT a opened_invariants fp fp'

/// Parallel composition of two STT functions
[@@noextract_to "Plugin"]
val par
  (#aL:Type u#a)
  (#aR:Type u#a)
  (#preL:vprop)
  (#postL:aL -> vprop)
  (#preR:vprop)
  (#postR:aR -> vprop)
  ($f:unit -> STT aL preL postL)
  ($g:unit -> STT aR preR postR)
  : STT (aL & aR)
        (preL `star` preR)
        (fun y -> postL (fst y) `star` postR (snd y))

/// Extracts an argument to a vprop from the context. This can be useful if we do need binders for some of the existentials opened by gen_elim.

val vpattern
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun _ -> p x) True (fun res -> res == x)

val vpattern_replace
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost a opened (p x) (fun res -> p res) True (fun res -> res == x)

val vpattern_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun _ -> p x) True (fun res -> Ghost.reveal res == x)

val vpattern_replace_erased
  (#opened: _)
  (#a: Type)
  (#x: a)
  (p: a -> vprop)
: STGhost (Ghost.erased a) opened (p x) (fun res -> p (Ghost.reveal res)) True (fun res -> Ghost.reveal res == x)

val vpattern_replace_erased_global
  (#opened: _)
  (#a: Type)
  (#x: a)
  (#q: a -> vprop)
  (p: a -> vprop)
: STGhostF (Ghost.erased a) opened (p x `star` q x) (fun res -> p (Ghost.reveal res) `star` q (Ghost.reveal res)) True (fun res -> Ghost.reveal res == x)

val vpattern_rewrite
  (#opened: _)
  (#a: Type)
  (#x1: a)
  (p: a -> vprop)
  (x2: a)
: STGhost unit opened
    (p x1)
    (fun _ -> p x2)
    (x1 == x2)
    (fun _ -> True)
