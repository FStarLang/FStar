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

open Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
module STAG = Steel.ST.Effect.AtomicAndGhost
module STA = Steel.ST.Effect.Atomic

(*** STGhost effect ***)

[@@ erasable; ite_soundness_by ite_attr]
total
reflectable
new_effect STGhostBase = STAG.STAGCommon

/// The two user-facing effects, corresponding to not yet framed (SteelGhost)
/// and already framed (SteelGhostF) computations.
/// In the ICFP21 paper, this is modeled by the |- and |-_F modalities.
/// Both effects are instantiated with the UnObservable bit, indicating that they
/// model ghost computations, which can be freely composed with each other
effect STGhost (a:Type)
                  (opened:inames)
                  (pre:pre_t)
                  (post:post_t a)
                  (req:Type0)
                  (ens:a -> Type0)
  = STGhostBase a false opened Unobservable pre post req ens

effect STGhostF (a:Type)
                (opened:inames)
                (pre:pre_t)
                (post:post_t a)
                (req:Type0)
                (ens:a -> Type0)
  = STGhostBase a true opened Unobservable pre post req ens

polymonadic_bind (PURE, STGhostBase) |> STGhostBase = STAG.bind_pure_stag

/// A version of the SteelGhost effect with trivial requires and ensures clauses
effect STGhostT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  STGhost a opened pre post True (fun _ -> True)

(***** Lift relations *****)

/// Any Steel ghost computation can always be lifted to an atomic computation if needed.
/// Note that because SteelGhost is marked as erasble, the F* typechecker will throw an error
/// if this lift is applied to a ghost computation with an informative return value
val lift_ghost_atomic
    (a:Type)
    (opened:inames)
    (#framed:eqtype_as_type bool)
    (#[@@@ framing_implicit] pre:pre_t)
    (#[@@@ framing_implicit] post:post_t a)
    (#[@@@ framing_implicit] req:Type0)
    (#[@@@ framing_implicit] ens:a -> Type0)
    (f:STAG.repr a framed opened Unobservable pre post req ens)
  : STAG.repr a framed opened Unobservable pre post req ens

sub_effect STGhostBase ~> STA.STAtomicBase = lift_ghost_atomic

[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action_ghost (#a:Type u#a)
                           (#opened_invariants:inames)
                           (#fp:slprop)
                           (#fp': a -> slprop)
                           (f:action_except a opened_invariants fp fp')
  : STGhostT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))
