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

module Steel.ST.PCMReference

open FStar.PCM
open FStar.Ghost

open Steel.ST.Util

/// This module exposes the core PCM-based memory model defined in Steel.Memory
/// as stateful Steel computations.

#set-options "--ide_id_info_off"

/// Lifting the pts_to separation logic, PCM-indexed predicate to a vprop.
/// Its selector is non-informative (it is unit)
[@@ __steel_reduce__]
unfold
let pts_to (#a:Type) (#pcm:pcm a) (r:ref a pcm) (v:a) = to_vprop (pts_to r v)

let pts_to_not_null
  (#opened: _)
  (#t: Type)
  (#p: pcm t)
  (r: ref t p)
  (v: t)
: STGhost unit opened
    (pts_to r v)
    (fun _ -> pts_to r v)
    True
    (fun _ -> r =!= null)
= extract_fact
    (pts_to r v)
    (r =!= null)
    (fun m -> pts_to_not_null r v m)

/// Reading the contents of reference [r] in memory.
/// The returned value [v] is ensured to be compatible with respect
/// to the PCM [pcm] with our current knowledge [v0]
val read (#a:Type)
         (#pcm:pcm a)
         (r:ref a pcm)
         (v0:erased a)
  : ST a
          (pts_to r v0)
          (fun _ -> pts_to r v0)
          (requires True)
          (ensures fun v -> compatible pcm v0 v /\ True)

/// Writing value [v1] in reference [r], as long as it is frame-preserving with our
/// current knowledge [v0], and that [v1] is a refined value for the PCM [pcm]
val write (#a:Type)
          (#pcm:pcm a)
          (r:ref a pcm)
          (v0:erased a)
          (v1:a)
  : ST unit
          (pts_to r v0)
          (fun _ -> pts_to r v1)
          (requires frame_preserving pcm v0 v1 /\ pcm.refine v1)
          (ensures fun _ -> True)

/// Allocates a new reference, initially storing value [x].
val alloc (#a:Type)
          (#pcm:pcm a)
          (x:a)
  : ST (ref a pcm)
          emp
          (fun r -> pts_to r x)
          (requires pcm.refine x)
          (ensures fun _ -> True)

/// Frees reference [r], as long as we have exclusive ownership of [r]
/// according to the governing PCM.
/// Freeing here sets the value to the unit value of the PCM, one can manually
/// call `drop` from Steel.Effect.Atomic to forget it entirely from the context
val free (#a:Type)
         (#p:pcm a)
         (r:ref a p)
         (x:erased a)
  : ST unit (pts_to r x) (fun _ -> pts_to r p.p.one)
          (requires exclusive p x /\ p.refine p.p.one)
          (ensures fun _ -> True)

/// Splits permission on reference [r], in a way that is compatible with the governing PCM.
val split (#inames: _)
          (#a:Type)
          (#p:pcm a)
          (r:ref a p)
          (v:erased a)
          (v0:erased a)
          (v1:erased a)
  : STGhost unit inames (pts_to r v)
               (fun _ -> pts_to r v0 `star` pts_to r v1)
               (requires
                 composable p v0 v1 /\
                 v == hide (op p v0 v1))
               (ensures fun _ -> True)

/// Gather permissions on reference [r]
val gather (#inames: _)
           (#a:Type)
           (#p:FStar.PCM.pcm a)
           (r:ref a p)
           (v0:erased a)
           (v1:erased a)
  : STGhostT (_:unit{composable p v0 v1}) inames
           (pts_to r v0 `star` pts_to r v1)
           (fun _ -> pts_to r (op p v0 v1))

let fact_valid_compat (#a:Type) (#pcm:pcm a)
                      (fact:stable_property pcm)
                      (v:erased a)
  = squash (forall z. compatible pcm v z ==> fact z)

/// If property [fact] is stable with respect to the governing PCM,
/// and if it is currently valid for any value that is compatible with
/// our current knowledge [v], then we can witness the property
val witness (#inames: _) (#a:Type) (#pcm:pcm a)
            (r:ref a pcm)
            (fact:stable_property pcm)
            (v:erased a)
            (_:fact_valid_compat fact v)
  : STAtomicUT (witnessed r fact) inames (pts_to r v)
               (fun _ -> pts_to r v)


/// If we previously witnessed the validity of a predicate [fact],
/// then we can recall this validity on the current value [v1], which
/// is compatible with our previous knowledge [v]
val recall (#inames: _) (#a:Type u#1) (#pcm:pcm a)
           (fact:property a)
           (r:ref a pcm)
           (v:erased a)
           (w:witnessed r fact)
  : STAtomicU (erased a) inames
          (pts_to r v)
          (fun v1 -> pts_to r v)
          (requires True)
          (ensures fun v1 -> fact v1 /\ compatible pcm v v1)

/// Refines our current knowledge [x] about reference [r] by applying function [f]
/// as long as we can prove that this refinement is frame compatible
val select_refine (#a:Type u#1) (#p:pcm a)
                  (r:ref a p)
                  (x:erased a)
                  (f:(v:a{compatible p x v}
                      -> GTot (y:a{compatible p y v /\
                                  frame_compatible p x v y})))
   : STT (v:a{compatible p x v /\ p.refine v})
            (pts_to r x)
            (fun v -> pts_to r (f v))

/// Updates our knowledge [x], with another, possibly partial knowledge [y],
/// as long as we can prove that this update is frame preserving
val upd_gen (#a:Type) (#p:pcm a) (r:ref a p) (x y:erased a)
            (f:frame_preserving_upd p x y)
  : STT unit
           (pts_to r x)
           (fun _ -> pts_to r y)


/// Atomic read and write
///
/// These are a little too powerful right now, allowing atomics on arbitrary types
/// We should allow only on [t]'s that are small enough, e.g. word-sized
///
/// The commonly used derivations of this module, e.g. Steel.ST.Reference, export
///   more restrictive atomic operations interface
///
/// If you use these functions directly from here, use with care


val atomic_read (#opened:_) (#a:Type) (#pcm:pcm a)
  (r:ref a pcm)
  (v0:erased a)
  : STAtomic a opened
      (pts_to r v0)
      (fun _ -> pts_to r v0)
      (requires True)
      (ensures fun v -> compatible pcm v0 v /\ True)

val atomic_write (#opened:_) (#a:Type) (#pcm:pcm a)
  (r:ref a pcm)
  (v0:erased a)
  (v1:a)
  : STAtomic unit opened
      (pts_to r v0)
      (fun _ -> pts_to r v1)
      (requires frame_preserving pcm v0 v1 /\ pcm.refine v1)
      (ensures fun _ -> True)
