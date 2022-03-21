(*
   Copyright 2021 Microsoft Research

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
module Steel.ST.GhostPCMReference
open FStar.Ghost
open Steel.ST.Util
open Steel.ST.Coercions
open FStar.PCM
open FStar.Universe
module UP = FStar.Universe.PCM
module G = Steel.GhostPCMReference

let ref (a:Type u#0) (p:pcm a) : Type u#0 =
    G.ref (raise_t u#0 u#1 a) (UP.raise p)

/// pts_to is fixed to ref contents in u#0
let pts_to (#a:Type u#0) (#pcm:pcm a) (r:ref a pcm) ([@@@smt_fallback] v:a)
  = G.pts_to #(raise_t a) #(UP.raise pcm) r (raise_val v)

/// Allocates a new reference, initially storing value [x].
let alloc (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : STGhost (ref a pcm) o
            emp
            (fun r -> pts_to r x)
            (requires pcm.refine x)
            (ensures fun _ -> True)
  = coerce_ghost (fun _ -> G.alloc (raise_val x))


let read (#o:inames)
         (#a:Type)
         (#pcm:pcm a)
         (#v0:a)
         (r:ref a pcm)
  : STGhost a o
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires True)
          (ensures fun v -> compatible pcm v0 v)
  = let v = coerce_ghost (fun _ -> G.read r) in
    downgrade_val v

let write (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (r:ref a pcm)
          (v0:a)
          (v1:a)
  : STGhost unit o
          (pts_to r v0)
          (fun _ -> pts_to r v1)
          (requires frame_preserving pcm v0 v1 /\ pcm.refine v1)
          (ensures fun _ -> True)
  = coerce_ghost (fun _ -> G.write r (raise_val v0) (raise_val v1))

let upd_gen (#o:inames)
            (#a:Type)
            (#p:pcm a)
            (r:ref a p)
            (x y:a)
            (f:frame_preserving_upd p x y)
  : STGhostT unit o
           (pts_to r x)
           (fun _ -> pts_to r y)
  = coerce_ghost (fun _ -> G.upd_gen r (raise_val x) (raise_val y) (UP.raise_frame_preserving_upd f))

/// Splits permission on reference [r], in a way that is compatible with the governing PCM.
let share (#o:inames)
          (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v:a)
          (v0:a)
          (v1:a)
  : STGhost unit o
          (pts_to r v)
          (fun _ -> pts_to r v0 `star` pts_to r v1)
          (requires
                 composable p v0 v1 /\
                 v == op p v0 v1)
          (ensures fun _ -> True)
  = coerce_ghost (fun _ -> G.share r (raise_val v) (raise_val v0) (raise_val v1))

/// Gather permissions on reference [r]
let gather (#o:inames)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:a)
           (v1:a)
  : STGhostT (_:unit{composable p v0 v1}) o
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))
  = let _ = coerce_ghost (fun _ -> G.gather r (raise_val v0) (raise_val v1)) in
    ()
