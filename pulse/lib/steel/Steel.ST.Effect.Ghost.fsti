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

module Steel.ST.Effect.Ghost
(** This module instantiates Steel.ST.Effect.AtomicAndGhost
    providing the STGhost effect, a non-selector variant of
    SteelGhost *)
#push-options "--warn_error -330" //we intentionally use polymonads
open Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
module STAG = Steel.ST.Effect.AtomicAndGhost
module STA = Steel.ST.Effect.Atomic

(*** STGhost effect ***)

[@@ erasable; ite_soundness_by ite_attr]
total
reflectable
effect {
  STGhostBase (a:Type)
             (framed:bool)
             (opened_invariants:inames)
             (o:observability)
             (pre:pre_t)
             (post:post_t a)
             (req:pure_pre)
             (ens:pure_post a)
  with { repr = STAG.repr;
         return = STAG.return_;
         bind = STAG.bind;
         subcomp = STAG.subcomp;
         if_then_else = STAG.if_then_else }
}

(* NB: Defining it this way led to universe errors *)
// [@@ erasable; ite_soundness_by ite_attr]
// total
// reflectable
// new_effect STGhostBase = STAG.STAGCommon

effect STGhost (a:Type)
               (opened:inames)
               (pre:pre_t)
               (post:post_t a)
               (req:pure_pre)
               (ens:pure_post a)
  = STGhostBase a false opened Unobservable pre post req ens

/// This is an internal variant of the STGhost, for computations that
/// have not been framed.  It's unlikely that a client will want to
/// use this directly.
effect STGhostF (a:Type)
                (opened:inames)
                (pre:pre_t)
                (post:post_t a)
                (req:pure_pre)
                (ens:pure_post a)
  = STGhostBase a true opened Unobservable pre post req ens

polymonadic_bind (PURE, STGhostBase) |> STGhostBase = STAG.bind_pure_stag

/// A version of the SteelGhost effect with trivial requires and ensures clauses
effect STGhostT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  STGhost a opened pre post True (fun _ -> True)

(***** Lift relations *****)

/// Any STGhost ghost computation can always be lifted to an atomic
/// computation if needed.  Note that because SteelGhost is marked as
/// erasble, the F* typechecker will throw an error if this lift is
/// applied to a ghost computation with an informative return value
val lift_ghost_atomic
    (a:Type)
    (opened:inames)
    (#framed:eqtype_as_type bool)
    (#[@@@ framing_implicit] pre:pre_t)
    (#[@@@ framing_implicit] post:post_t a)
    (#[@@@ framing_implicit] req:pure_pre)
    (#[@@@ framing_implicit] ens:pure_post a)
    (f:STAG.repr a framed opened Unobservable pre post req ens)
  : STAG.repr a framed opened Unobservable pre post req ens

sub_effect STGhostBase ~> STA.STAtomicBase = lift_ghost_atomic

/// Adding an action as a ghost primitive: use wisely
[@@warn_on_use "as_atomic_ghost_action is a trusted primitive"]
val as_atomic_action_ghost (#a:Type u#a)
                           (#opened_invariants:inames)
                           (#fp:slprop)
                           (#fp': a -> slprop)
                           (f:action_except a opened_invariants fp fp')
  : STGhostT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))

/// A low-level utility to derive information from vprop validity
val extract_fact (#opened:inames)
                 (p:vprop)
                 (fact:prop)
                 (l:(m:mem) -> Lemma
                                (requires interp (hp_of p) m)
                                (ensures fact))
  : STGhost unit opened p (fun _ -> p) True (fun _ -> fact)

/// A utility to admit the proof of the continuation of program
[@@warn_on_use "uses an axiom"]
val admit_ (#a:Type)
          (#opened:inames)
          (#p:pre_t)
          (#q:post_t a)
          (_:unit)
  : STGhostF a opened p q True (fun _ -> False)
