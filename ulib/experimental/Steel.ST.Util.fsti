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
module SEA = Steel.Effect.Atomic

val coerce_atomic (#a:Type)
                  (#o:inames)
                  (#obs:observability)
                  (#p:vprop)
                  (#q:a -> vprop)
                  (#pre:Type0)
                  (#post: a -> Type0)
                  ($f:unit -> SEA.SteelAtomicBase a false o obs p q
                           (fun _ -> pre)
                           (fun _ x _ -> post x))
  : STAtomicBase a false o obs p q pre post

val coerce_ghost (#a:Type)
                 (#o:inames)
                 (#p:vprop)
                 (#q:a -> vprop)
                 (#pre:Type0)
                 (#post: a -> Type0)
                 ($f:unit -> SEA.SteelGhostBase a false o Unobservable p q
                   (fun _ -> pre)
                   (fun _ x _ -> post x))
  : STGhostBase a false o Unobservable p q pre post

val weaken (#opened:inames)
            (p q:vprop)
            (l:(m:mem) -> Lemma
                           (requires interp (hp_of p) m)
                           (ensures interp (hp_of q) m))
  : STGhostT unit opened p (fun _ -> q)

val rewrite (#opened:inames)
            (p q: vprop)
  : STGhost unit opened p (fun _ -> q) (p == q) (fun _ -> True)

val extract_fact (#opened:inames)
                 (p:vprop)
                 (fact:prop)
                 (l:(m:mem) -> Lemma
                                (requires interp (hp_of p) m)
                                (ensures fact))
  : STGhost unit opened p (fun _ -> p) True (fun _ -> fact)

/// A noop operator, occasionally useful for forcing framing of a subsequent computation
val noop (#opened:inames) (_:unit)
  : STGhostT unit opened emp (fun _ -> emp)

[@@warn_on_use "uses an axiom"]
val admit (#a:Type)
          (#opened:inames)
          (#p:pre_t)
          (#q:post_t a)
          (_:unit)
  : STGhostF a opened p q True (fun _ -> False)

/// Asserts the validity of vprop [p] in the current context
val assert_ (#opened_invariants:_)
            (p:vprop)
  : STGhostT unit opened_invariants p (fun _ -> p)

/// Drops vprop [p] from the context. Although our separation logic is affine,
/// the frame inference tactic treats it as linear.
/// Leveraging affinity requires a call from the user to this helper, to avoid
/// implicit memory leaks.
/// This should only be used for pure and ghost vprops
val drop (#opened:inames) (p:vprop) : STGhostT unit opened p (fun _ -> emp)

(* Helpers to interoperate between pure predicates encoded as separation logic
   propositions, and as predicates discharged by SMT *)
val intro_pure (#opened_invariants:_) (p:prop)
  : STGhost unit opened_invariants emp (fun _ -> pure p) p (fun _ -> True)

val elim_pure (#uses:_) (p:prop)
  : STGhost unit uses (pure p) (fun _ -> emp) True (fun _ -> p)

/// Hook to manually insert atomic monadic returns.
/// Because of the left-associative structure of F* computations,
/// this is necessary when a computation is atomic and returning a value
/// with an informative type, but the previous computation was ghost.
/// Else, the returned value will be given type SteelGhost, and F* will fail to typecheck
/// the program as it will try to lift a SteelGhost computation with an informative return type
val return (#a:Type u#a)
           (#opened_invariants:inames)
           (#p:a -> vprop)
           (x:a)
  : STAtomicBase a true opened_invariants Unobservable
                 (return_pre (p x)) p
                 True
                 (fun v -> v == x)

(* Lifting the separation logic exists combinator to vprop *)
val exists_ (#a:Type u#a) (p:a -> vprop) : vprop

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

let set_add i o : inames = Set.union (Set.singleton i) o
/// Atomically executing function [f] which relies on the predicate [p] stored in invariant [i]
/// as long as it maintains the validity of [p]
/// This requires invariant [i] to not belong to the set of currently opened invariants.
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
