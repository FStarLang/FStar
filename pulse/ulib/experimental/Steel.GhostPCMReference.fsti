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

   Author: N. Swamy
*)
module Steel.GhostPCMReference
(* A ghost variant of Steel.PCMReference *)
open FStar.PCM
open FStar.Ghost

open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

/// This module exposes the core PCM-based memory model defined in Steel.Memory
/// as ghost Steel computations.

#set-options "--ide_id_info_off"

/// The type of a reference to ghost state in pcm [p]
[@@erasable]
val ref (a:Type) (p:pcm a) : Type0

/// pts_to is fixed to ref contents in u#1
val pts_to (#a:Type u#1) (#pcm:pcm a) (r:ref a pcm) (v:a)
  : vprop

/// Allocates a new reference, initially storing value [x].
val alloc (#o:inames)
          (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : SteelGhost (ref a pcm) o
          emp
          (fun r -> pts_to r x)
          (requires fun _ -> pcm.refine x)
          (ensures fun _ _ _ -> True)

/// Reading the contents of reference [r] in memory.
/// The returned value [v] is ensured to be compatible with respect
/// to the PCM [pcm] with our current knowledge [v0]
val read (#o:inames)
         (#a:Type)
         (#pcm:pcm a)
         (#v0:a)
         (r:ref a pcm)
  : SteelGhost a o
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires fun _ -> True)
          (ensures fun _ v _ -> compatible pcm v0 v)

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
  : SteelGhost unit o
          (pts_to r v0)
          (fun _ -> pts_to r v1)
          (requires fun _ -> frame_preserving pcm v0 v1 /\ pcm.refine v1)
          (ensures fun _ _ _ -> True)

/// Updates our knowledge [x], with another, possibly partial knowledge [y],
/// as long as we can prove that this update is frame preserving
val upd_gen (#o:inames)
            (#a:Type)
            (#p:pcm a)
            (r:ref a p)
            (x y:a)
            (f:frame_preserving_upd p x y)
  : SteelGhostT unit o
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
  : SteelGhost unit o
          (pts_to r v)
          (fun _ -> pts_to r v0 `star` pts_to r v1)
          (requires fun _ ->
                 composable p v0 v1 /\
                 v == op p v0 v1)
          (ensures fun _ _ _ -> True)

/// Gather permissions on reference [r]
val gather (#o:inames)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:a)
           (v1:a)
  : SteelGhostT (_:unit{composable p v0 v1}) o
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))

////////////////////////////////////////////////////////////////////////////////
// API for witness/recall of monotonic facts
////////////////////////////////////////////////////////////////////////////////
val witnessed (#a:Type u#1) (#p:pcm a) (r:ref a p) (fact:property a)
  : prop
  
/// If property [fact] is stable with respect to the governing PCM,
/// and if it is currently valid for any value that is compatible with
/// our current knowledge [v], then we can witness the property
val witness (#o:inames)
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

/// If we previously witnessed the validity of a predicate [fact],
/// then we can recall this validity on the current value [v1], which
/// is compatible with our previous knowledge [v]
val recall (#o: _) 
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
