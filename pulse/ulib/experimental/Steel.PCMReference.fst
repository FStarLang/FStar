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


module Steel.PCMReference

module Mem = Steel.Memory

let read r v0 = as_action (sel_action FStar.Set.empty r v0)
let write r v0 v1 = as_action (upd_action FStar.Set.empty r v0 v1)

val alloc' (#a:Type)
           (#pcm:pcm a)
           (x:a)
  : Steel (ref a pcm)
          (to_vprop Mem.emp)
          (fun r -> pts_to r x)
          (requires fun _ -> compatible pcm x x /\ pcm.refine x)
          (ensures fun _ _ _ -> True)

let alloc' x = as_action (alloc_action FStar.Set.empty x)

let alloc x = rewrite_slprop emp (to_vprop Mem.emp) (fun _ -> reveal_emp ());
              alloc' x

let free r x = as_action (free_action FStar.Set.empty r x)

val split'
          (#inames: _)
          (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v0:erased a)
          (v1:erased a{composable p v0 v1})
  : SteelGhostT unit inames (pts_to r (op p v0 v1))
                (fun _ -> to_vprop Mem.(pts_to r v0 `star` pts_to r v1))

let split' #inames #a #p r v0 v1 = as_atomic_action_ghost (split_action inames r v0 v1)

let split #_ #a #p r v v0 v1 =
  let _:squash (composable p v0 v1) = () in
  rewrite_slprop (pts_to r v) (pts_to r (op p v0 v1)) (fun _ -> ());
  split' r v0 v1;
  rewrite_slprop (to_vprop Mem.(pts_to r v0 `star` pts_to r v1))
                 (pts_to r v0 `star` pts_to r v1)
                 (fun _ -> ())

val gather'
           (#inames: _)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:erased a)
           (v1:erased a)
  : SteelGhostT (_:unit{composable p v0 v1}) inames
           (to_vprop Mem.(pts_to r v0 `star` pts_to r v1))
           (fun _ -> pts_to r (op p v0 v1))

let gather' #inames r v0 v1 = as_atomic_action_ghost (gather_action inames r v0 v1)

let gather r v0 v1 =
  rewrite_slprop (pts_to r v0 `star` pts_to r v1)
                 (to_vprop Mem.(pts_to r v0 `star` pts_to r v1))
                 (fun _ -> ());
  gather' r v0 v1

val witness' (#inames: _) (#a:Type) (#pcm:pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:erased a)
            (_:fact_valid_compat fact v)
  : SteelGhostT unit inames (pts_to r v)
                (fun _ -> to_vprop Mem.(pts_to r v `star` pure (witnessed r fact)))

let witness' #inames r fact v _ = as_atomic_action_ghost (Steel.Memory.witness inames r fact v ())

let witness r fact v s =
  witness' r fact v s;
  rewrite_slprop (to_vprop Mem.(pts_to r v `star` pure (witnessed r fact)))
                 (pts_to r v `star` pure (witnessed r fact))
                 (fun _ -> ());
  elim_pure (witnessed r fact)

val recall' (#inames: _) (#a:Type u#1) (#pcm:pcm a) (fact:property a)
           (r:ref a pcm)
           (v:erased a)
  : SteelGhostT (v1:erased a{compatible pcm v v1}) inames
           (to_vprop Mem.(pts_to r v `star` pure (witnessed r fact)))
           (fun v1 -> to_vprop Mem.(pts_to r v `star` pure (fact v1)))

let recall' #inames #a #pcm fact r v = as_atomic_action_ghost (Steel.Memory.recall #a #pcm #fact inames r v)

let recall #inames #a #pcm fact r v =
  intro_pure (witnessed r fact);
  rewrite_slprop (pts_to r v `star` pure (witnessed r fact))
                 (to_vprop Mem.(pts_to r v `star` pure (witnessed r fact)))
                 (fun _ -> ());
  let v1 = recall' fact r v in
  rewrite_slprop (to_vprop Mem.(pts_to r v `star` pure (fact v1)))
                 (pts_to r v `star` pure (fact v1))
                 (fun _ -> ());
  elim_pure (fact v1);
  v1

let select_refine #a #p r x f = as_action (Steel.Memory.select_refine Set.empty r x f)

let upd_gen #a #p r x y f = as_action (Steel.Memory.upd_gen Set.empty r x y f)

let atomic_read #opened #_ #_ r v0 = as_atomic_action (sel_action opened r v0)
let atomic_write #opened #_ #_ r v0 v1 = as_atomic_action (upd_action opened r v0 v1)
