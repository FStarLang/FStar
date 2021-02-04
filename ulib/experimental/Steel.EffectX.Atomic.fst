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

module Steel.EffectX.Atomic
open FStar.PCM
open Steel.Memory

let observability = bool

#push-options "--query_stats" //crappy workaround
let has_eq_observability () = ()
#pop-options
let observable = true
let unobservable = false

let join_preserves_interp hp m0 m1
  = intro_emp m1;
    intro_star hp emp m0 m1;
    affine_star hp emp (join m0 m1)

let respects_fp #fp p =
  forall (m0:hmem fp) (m1:mem{disjoint m0 m1}). p m0 <==> p (join m0 m1)
let reveal_respects_fp p = ()

let respects_binary_fp #a #pre #post q
  = (forall x (h_pre:hmem pre) h_post (h:mem{disjoint h_pre h}).
      q h_pre x h_post <==> q (join h_pre h) x h_post) /\
    (forall x h_pre (h_post:hmem (post x)) (h:mem{disjoint h_post h}).
      q h_pre x h_post <==> q h_pre x (join h_post h))
let reveal_respects_binary_fp q = ()

let req_to_act_req (#pre:slprop) (req:fp_mprop pre) : mprop pre =
  fun m -> interp pre m /\ req m

let ens_to_act_ens (#pre:slprop) (#a:Type) (#post:a -> slprop) (ens:fp_binary_mprop pre post)
: mprop2 pre post
= fun m0 x m1 -> interp pre m0 /\ interp (post x) m1 /\ ens m0 x m1

let atomic_repr a opened_invariants f pre post req ens =
    action_except_full a opened_invariants pre post (req_to_act_req req) (ens_to_act_ens ens)

let return a x o p = fun _ -> x

let bind a b o o1 o2 pre_f post_f req_f ens_f post_g req_g ens_g f g =
  fun frame ->
    let x = f frame in
    g x frame

let subcomp a opened o pre post req_f ens_f req_g ens_g f = f

inline_for_extraction
let lift_pure_steel_atomic a op p wp f
  = FStar.Monotonic.Pure.wp_monotonic_pure ();
    fun _ -> let x = f () in x

let as_atomic_action f = SteelAtomicX?.reflect f
let new_invariant i p = SteelAtomicX?.reflect (Steel.Memory.new_invariant i p)
let with_invariant #a #fp #fp' #opened i f = SteelAtomicX?.reflect (Steel.Memory.with_invariant #_ #fp #fp' #opened i (reify (f())))
let frame frame f = SteelAtomicX?.reflect (Steel.Memory.frame frame (reify (f ())))
let change_slprop #opened p q proof = SteelAtomicX?.reflect (Steel.Memory.change_slprop #opened p q proof)

open NMSTTotal
open MSTTotal

let witness_h_exists #a #u #p () = SteelAtomicX?.reflect (Steel.Memory.witness_h_exists #u p)
let lift_h_exists_atomic #a #u p = SteelAtomicX?.reflect (Steel.Memory.lift_h_exists #u p)
let elim_pure #uses p = SteelAtomicX?.reflect (Steel.Memory.elim_pure #uses p)
