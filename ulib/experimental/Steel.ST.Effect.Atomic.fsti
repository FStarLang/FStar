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

module Steel.ST.Effect.Atomic

open Steel.Memory
module T = FStar.Tactics
include Steel.Effect.Common
module STAG = Steel.ST.Effect.AtomicAndGhost

/// Defining a SteelAtomic effect for atomic Steel computations.
/// F*'s effect system is nominal; defining this as a `new_effect` ensures
/// that SteelAtomic computations are distinct from any computation with the
/// SteelAGCommon effect, while allowing this effect to directly inherit
/// the SteelAGCommon combinators
[@@ ite_soundness_by ite_attr]
total
reflectable
new_effect STAtomicBase = STAG.STAGCommon

/// The two user-facing effects, corresponding to not yet framed (SteelAtomic)
/// and already framed (SteelAtomicF) computations.
/// In the ICFP21 paper, this is modeled by the |- and |-_F modalities.
/// Both effects are instantiated with the Observable bit, indicating that they do not
/// model ghost computations
effect STAtomic (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:Type0)
  (ens:a -> Type0)
  = STAtomicBase a false opened Observable pre post req ens

effect STAtomicF (a:Type)
  (opened:inames)
  (pre:pre_t)
  (post:post_t a)
  (req:Type0)
  (ens:a -> Type0)
  = STAtomicBase a true opened Observable pre post req ens

(* Composing SteelAtomic and Pure computations *)

#push-options "--warn_error -330"
polymonadic_bind (PURE, STAtomicBase) |> STAtomicBase = STAG.bind_pure_stag
#pop-options

/// A version of the SteelAtomic effect with trivial requires and ensures clauses
effect STAtomicT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  STAtomic a opened pre post True (fun _ -> True)

sub_effect STAtomicBase ~> Steel.ST.Effect.STBase = STAG.lift_atomic_st

/// Lifting actions from the memory model to Steel atomic and ghost computations.
/// Only to be used internally, for the core primitives of the Steel framework
[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : STAtomicT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))

