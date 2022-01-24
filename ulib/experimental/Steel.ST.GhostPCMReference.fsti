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

   Author: N. Swamy
*)
module Steel.ST.GhostPCMReference
open FStar.Ghost
open Steel.ST.Util
open FStar.PCM

(* This module provides a ghost reference in a PCM at universe 0,
   by specializing Steel.GhostPCMReference *)

[@@erasable]
val ref (a:Type u#0) (p:pcm a) : Type u#0

/// pts_to is fixed to ref contents in u#0
val pts_to (#a:Type u#0) (#pcm:pcm a) (r:ref a pcm) ([@@@smt_fallback] v:a)
  : vprop

/// Allocates a new reference, initially storing value [x].
val alloc (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : STGhost (ref a pcm) o
            emp
            (fun r -> pts_to r x)
            (requires pcm.refine x)
            (ensures fun _ -> True)

/// Reading the contents of reference [r] in memory.
/// The returned value [v] is ensured to be compatible with respect
/// to the PCM [pcm] with our current knowledge [v0]
val read (#o:inames)
         (#a:Type)
         (#pcm:pcm a)
         (#v0:a)
         (r:ref a pcm)
  : STGhost a o
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires True)
          (ensures fun v -> compatible pcm v0 v)

/// Writing value [v1] in reference [r], as long as it is frame-preserving with our
/// current knowledge [v0], and that [v1] is a refined value for the PCM [pcm].
///
/// Since [v1] is a refined value, this is unlikely to be the
/// primitive you want.  Instead, you would likely want to lift a
/// frame_preserving_upd in the PCM to a ghost action. See [upd_gen] below.
val write (#o:inames)
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

/// Updates our knowledge [x], with another, possibly partial knowledge [y],
/// as long as we can prove that this update is frame preserving
val upd_gen (#o:inames)
            (#a:Type)
            (#p:pcm a)
            (r:ref a p)
            (x y:a)
            (f:frame_preserving_upd p x y)
  : STGhostT unit o
           (pts_to r x)
           (fun _ -> pts_to r y)

/// Splits permission on reference [r], in a way that is compatible with the governing PCM.
val share (#o:inames)
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

/// Gather permissions on reference [r]
val gather (#o:inames)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:a)
           (v1:a)
  : STGhostT (_:unit{composable p v0 v1}) o
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))
