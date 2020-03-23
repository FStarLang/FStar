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

module Frame


(*** Small examples for frame inference ***)

#push-options "--no_tactics"

open Steel.Semantics.Instantiate
open Steel.Memory
module Mem = Steel.Memory
open Steel.Actions
open Steel.Effect
open Steel.Memory.Tactics

let rassert
  (#h_in:hprop)
  (h_out:hprop{
    FStar.Tactics.with_tactic
    reprove_frame
    (can_be_split_into h_in h_out emp /\ True)})
  : SteelT unit h_in (fun _ -> h_out)
  = Steel?.reflect (fun _ ->
      let m0 = mst_get () in
      FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into h_in h_out emp /\ True);
      let (| _, m1 |) = rewrite_hprop h_in h_out m0 in
      act_preserves_frame_and_preorder (rewrite_hprop h_in h_out) m0;
      mst_put m1)

let steel_frame_t
  (#outer:hprop)
  (#a:Type) (#pre:pre_t) (#post:post_t a)
  (#[resolve_frame()]
    frame:hprop{
      FStar.Tactics.with_tactic
      reprove_frame
      (can_be_split_into outer pre frame /\ True)}
  )
  ($f:unit -> Steel a pre post (fun _ -> True) (fun _ _ _ -> True))
: SteelT a
  outer
  (fun x -> post x `Mem.star` frame)
= FStar.Tactics.by_tactic_seman reprove_frame (can_be_split_into outer pre frame /\ True);
  Mem.emp_unit (pre `Mem.star` frame);
  FStar.Tactics.unfold_with_tactic reprove_frame
    (can_be_split_into outer (pre `Mem.star` frame) emp /\ True);
  rassert (pre `Mem.star` frame);
  steel_frame f frame (fun _ -> True)
#pop-options
