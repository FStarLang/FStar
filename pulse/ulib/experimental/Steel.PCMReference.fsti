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

open FStar.PCM
open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

#set-options "--ide_id_info_off"

[@@ __steel_reduce__]
unfold
let pts_to (#a:Type) (#pcm:pcm a) (r:ref a pcm) (v:a) = to_vprop (pts_to r v)

val read (#a:Type)
         (#pcm:pcm a)
         (r:ref a pcm)
         (v0:erased a)
  : Steel a
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires fun _ -> True)
          (ensures fun _ v _ -> compatible pcm v0 v /\ True)

val write (#a:Type)
          (#pcm:pcm a)
          (r:ref a pcm)
          (v0:erased a)
          (v1:a)
  : Steel unit
          (pts_to r v0)
          (fun _ -> pts_to r v1)
          (requires fun _ -> frame_preserving pcm v0 v1 /\ pcm.refine v1)
          (ensures fun _ _ _ -> True)

val alloc (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : Steel (ref a pcm)
          emp
          (fun r -> pts_to r x)
          (requires fun _ -> compatible pcm x x /\ pcm.refine x)
          (ensures fun _ _ _ -> True)

val free (#a:Type)
         (#p:pcm a)
         (r:ref a p)
         (x:erased a)
  : Steel unit (pts_to r x) (fun _ -> pts_to r p.p.one)
          (requires fun _ -> exclusive p x /\ p.refine p.p.one)
          (ensures fun _ _ _ -> True)

val split (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v:erased a)
          (v0:erased a)
          (v1:erased a)
  : Steel unit (pts_to r v)
               (fun _ -> pts_to r v0 `star` pts_to r v1)
               (requires fun _ ->
                 composable p v0 v1 /\
                 v == hide (op p v0 v1))
               (ensures fun _ _ _ -> True)

val gather (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:erased a)
           (v1:erased a)
  : SteelT (_:unit{composable p v0 v1})
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))

let fact_valid_compat (#a:Type) (#pcm:pcm a)
                      (fact:stable_property pcm)
                      (v:erased a)
  = squash (forall z. compatible pcm v z ==> fact z)

val witness (#a:Type) (#pcm:pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:erased a)
            (_:fact_valid_compat fact v)
  : Steel unit (pts_to r v)
               (fun _ -> pts_to r v)
               (requires fun _ -> True)
               (ensures fun _ _ _ -> witnessed r fact)

val recall (#a:Type u#1) (#pcm:pcm a)
           (fact:property a)
           (r:ref a pcm)
           (v:erased a)
  : Steel (erased a)
          (pts_to r v)
          (fun v1 -> pts_to r v)
          (requires fun _ -> witnessed r fact)
          (ensures fun _ v1 _ -> fact v1 /\ compatible pcm v v1)

val select_refine (#a:Type u#1) (#p:pcm a)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  frame_compatible p x v y})))
   : SteelT (v:a{compatible p x v /\ p.refine v})
            (pts_to r x)
            (fun v -> pts_to r (f v))

val upd_gen (#a:Type) (#p:pcm a) (r:ref a p) (x y:erased a)
            (f:frame_preserving_upd p x y)
  : SteelT unit
           (pts_to r x)
           (fun _ -> pts_to r y)
