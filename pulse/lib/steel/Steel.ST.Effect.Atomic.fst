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
friend Steel.ST.Effect.AtomicAndGhost
friend Steel.Effect.Atomic
open Steel.Memory
module T = FStar.Tactics
module SEA = Steel.Effect.Atomic

let as_atomic_action (#a:Type u#a)
                     (#opened_invariants:inames)
                     (#fp:slprop)
                     (#fp': a -> slprop)
                     (f:action_except a opened_invariants fp fp')
  : STAtomicT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))
  = let ff = SEA.reify_steel_atomic_comp (fun _ -> SEA.as_atomic_action f) in
    STAtomicBase?.reflect ff


let as_atomic_unobservable_action (#a:Type u#a)
                                  (#opened_invariants:inames)
                                  (#fp:slprop)
                                  (#fp': a -> slprop)
                                  (f:action_except a opened_invariants fp fp')
  : STAtomicUT a opened_invariants (to_vprop fp) (fun x -> to_vprop (fp' x))
  = let ff = SEA.reify_steel_atomic_comp (fun _ -> SEA.as_atomic_unobservable_action f) in
    STAtomicBase?.reflect ff
