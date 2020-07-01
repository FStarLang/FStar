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

module Steel.Effect.Atomic
open FStar.PCM
open Steel.Memory

let observability = bool

#push-options "--query_stats" //crappy workaround
let has_eq_observability () = ()
#pop-options
let observable = true
let unobservable = false

let atomic_repr a opened_invariants f pre post =
    action_except a opened_invariants pre post

let return a x o p = fun _ -> x

let bind a b o o1 o2 pre_f post_f post_g f g =
  fun m0 ->
    let x = f () in
    g x ()

inline_for_extraction
let lift_pure_steel_atomic a op p wp f
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ -> let x = f () in x

let lift_atomic_to_steelT f = Steel.Effect.add_action (reify (f()))
let as_atomic_action f = SteelAtomic?.reflect f
let new_invariant i p = SteelAtomic?.reflect (Steel.Memory.new_invariant i p)
let with_invariant i f = SteelAtomic?.reflect (Steel.Memory.with_invariant i (reify (f())))
let frame frame f = SteelAtomic?.reflect (Steel.Memory.frame frame (reify (f ())))
let change_slprop p q proof = SteelAtomic?.reflect (Steel.Memory.change_slprop p q proof)

open NMSTTotal
open MSTTotal

let witness_h_exists #a #u #p () = SteelAtomic?.reflect (Steel.Memory.witness_h_exists p)
let lift_h_exists_atomic #a #u p = SteelAtomic?.reflect (Steel.Memory.lift_h_exists #u p)
let elim_pure #uses p = SteelAtomic?.reflect (Steel.Memory.elim_pure #uses p)
