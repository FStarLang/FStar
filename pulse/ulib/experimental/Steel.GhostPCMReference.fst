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
module Steel.GhostPCMReference
(* A ghost variant of Steel.PCMReference *)
open FStar.PCM
open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
module Mem = Steel.Memory
module P = Steel.PCMReference

let ref (a:Type) (p:pcm a) = erased (Steel.Memory.ref a p)

/// Its selector is non-informative (it is unit)
[@@__reduce__]
let pts_to (#a:Type u#1) (#pcm:pcm a) (r:ref a pcm) ([@@@smt_fallback]v:a)
  = to_vprop (Steel.Memory.pts_to r v)

let alloc (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : SteelGhost
          (ref a pcm) o
          (emp)
          (fun r -> pts_to r x)
          (requires fun _ -> pcm.refine x)
          (ensures fun _ _ _ -> True)
  = rewrite_slprop emp (to_vprop Mem.emp) (fun _ -> reveal_emp ());
    FStar.PCM.compatible_refl pcm x;
    let r = as_atomic_action_ghost (alloc_action o x) in
    r

let read (#o:inames)
         (#a:Type)
         (#pcm:pcm a)
         (#v0:a)
         (r:ref a pcm)
  : SteelGhost a o
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires fun _ -> True)
          (ensures fun _ v _ -> compatible pcm v0 v)
  = let v = as_atomic_action_ghost (sel_action o r v0) in
    v

let write (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (r:ref a pcm)
          (v0:a)
          (v1:a)
  : SteelGhost unit o
          (pts_to r v0)
          (fun _ -> pts_to r v1)
          (requires fun _ -> frame_preserving pcm v0 v1 /\ pcm.refine v1)
          (ensures fun _ _ _ -> True)
  = as_atomic_action_ghost (upd_action o r v0 v1)

let upd_gen (#o:inames)
            (#a:Type)
            (#p:pcm a)
            (r:ref a p)
            (x y:a)
            (f:frame_preserving_upd p x y)
  : SteelGhostT unit o
           (pts_to r x)
           (fun _ -> pts_to r y)
  = as_atomic_action_ghost (Steel.Memory.upd_gen o r x y f)

let share (#o:inames)
          (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v:a)
          (v0:a)
          (v1:a)
  : SteelGhost unit o
          (pts_to r v)
          (fun _ -> pts_to r v0 `star` pts_to r v1)
          (requires fun _ ->
                 composable p v0 v1 /\
                 v == op p v0 v1)
          (ensures fun _ _ _ -> True)
  = P.split r v v0 v1

let gather (#o:inames)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:a)
           (v1:a)
  : SteelGhostT (_:unit{composable p v0 v1}) o
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))
  = P.gather r v0 v1

let witnessed (#a:Type) (#p:pcm a) (r:ref a p) (fact:property a)
  : prop
  = Steel.Memory.witnessed r fact

let witness (#o:inames)
            (#a:Type)
            (#pcm:pcm a)
            (r:ref a pcm)
            (fact:Steel.Preorder.stable_property pcm)
            (v:a)
            (_:squash (Steel.Preorder.fact_valid_compat fact v))
  : SteelGhost unit o
      (pts_to r v)
      (fun _ -> pts_to r v)
      (requires fun _ -> True)
      (ensures fun _ _ _ -> witnessed r fact)
  = P.witness r fact v ()

let recall (#o: _)
           (#a:Type)
           (#pcm:pcm a)
           (fact:property a)
           (r:ref a pcm)
           (v:erased a)
  : SteelGhost a o
          (pts_to r v)
          (fun v1 -> pts_to r v)
          (requires fun _ -> witnessed r fact)
          (ensures fun _ v1 _ -> fact v1 /\ compatible pcm v v1)
  = let x = P.recall fact r v in
    reveal x
