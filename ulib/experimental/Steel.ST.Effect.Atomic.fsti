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
(** This module instantiates Steel.ST.Effect.AtomicAndGhost
    providing the STAtomic effect, a non-selector variant of
    SteelAtomic *)
#push-options "--warn_error -330" //we intentionally use polymonads
open Steel.Memory
include Steel.Effect.Common
module STAG = Steel.ST.Effect.AtomicAndGhost

[@@ ite_soundness_by ite_attr]
total
reflectable
effect {
  STAtomicBase (a:Type)
               (framed:bool)
               (opened_invariants:inames)
               (o:observability)
               (pre:pre_t)
               (post:post_t a)
               (req:st_req_t)
               (ens:st_ens_t a)
  with { repr = STAG.repr;
         return = STAG.return_;
         bind = STAG.bind;
         subcomp = STAG.subcomp;
         if_then_else = STAG.if_then_else }
}

(* NB: Definining it this way led to universe errors *)
// [@@ ite_soundness_by ite_attr]
// total
// reflectable
// new_effect STAtomicBase = STAG.STAGCommon

effect STAtomic (a:Type)
                (opened:inames)
                (pre:pre_t)
                (post:post_t a)
                (req:st_req_t)
                (ens:st_ens_t a)
  = STAtomicBase a false opened Observable pre post req ens

effect STAtomicF (a:Type)
                 (opened:inames)
                 (pre:pre_t)
                 (post:post_t a)
                 (req:st_req_t)
                 (ens:st_ens_t a)
  = STAtomicBase a true opened Observable pre post req ens

(* Composing SteelAtomic and Pure computations *)
polymonadic_bind (PURE, STAtomicBase) |> STAtomicBase = STAG.bind_pure_stag

/// A version of the SteelAtomic effect with trivial requires and ensures clauses
effect STAtomicT (a:Type) (opened:inames) (pre:pre_t) (post:post_t a) =
  STAtomic a opened pre post True (fun _ -> True)

sub_effect STAtomicBase ~> Steel.ST.Effect.STBase = STAG.lift_atomic_st

/// Lifting actions from the memory model to atomic and ghost computations.
/// Only to be used internally, for the core primitives of the Steel framework
[@@warn_on_use "as_atomic_action is a trusted primitive"]
val as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : STAtomicT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))

