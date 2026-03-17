(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.Core.Refs
open FStar.Ghost
open PulseCore.FractionalPermission
open PulseCore.Observability
open FStar.PCM
module T = FStar.Tactics.V2
open Pulse.Lib.Dv {}
open FStar.ExtractAs
open Pulse.Lib.Core

// These are PCM references in Type u#3 and should not be used directly.
// The modules Pulse.Lib.(Ghost)PCMReference provide universe-polymorphic wrappers.

////////////////////////////////////////////////////////
//Core PCM references
////////////////////////////////////////////////////////
val core_pcm_ref : Type0
val null_core_pcm_ref : core_pcm_ref
val is_null_core_pcm_ref (p:core_pcm_ref)
  : b:bool { b <==> p == null_core_pcm_ref }

let pcm_ref
    (#a:Type u#3)
    (p:FStar.PCM.pcm a)
: Type0
= core_pcm_ref

val pcm_pts_to
    #a
    (#p:pcm a)
    ([@@@mkey] r:pcm_ref p)
    (v:a)
: slprop

val timeless_pcm_pts_to
    #a
    (#p:pcm a)
    (r:pcm_ref p)
    (v:a)
: Lemma (timeless (pcm_pts_to r v))
        [SMTPat (timeless (pcm_pts_to r v))]

val on_pcm_pts_to_eq l #a #p r v : squash (on l (pcm_pts_to #a #p r v) == pcm_pts_to r v)

let pcm_ref_null
    (#a:Type)
    (p:FStar.PCM.pcm a)
: pcm_ref p
= null_core_pcm_ref

let is_pcm_ref_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
: b:bool { b <==> r == pcm_ref_null p }
= is_null_core_pcm_ref r

val pts_to_not_null
    (#a:Type)
    (#p:FStar.PCM.pcm a)
    (r:pcm_ref p)
    (v:a)
: stt_ghost (squash (not (is_pcm_ref_null r)))
            emp_inames
            (pcm_pts_to r v)
            (fun _ -> pcm_pts_to r v)

val alloc
    #a
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
      emp
      (fun r -> pcm_pts_to r x)

val read
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt (v:a{compatible p x v /\ p.refine v})
     (pcm_pts_to r x)
     (fun v -> pcm_pts_to r (f v))

val write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
     (pcm_pts_to r x)
     (fun _ -> pcm_pts_to r y)

val share
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> pcm_pts_to r v0 ** pcm_pts_to r v1)

[@@allow_ambiguous]
val gather
    (#a:Type)
    (#pcm:pcm a)
    (r:pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (pcm_pts_to r v0 ** pcm_pts_to r v1)
    (fun _ -> pcm_pts_to r (op pcm v0 v1))

/////////////////////////////////////////////////////////////////////////
[@@erasable]
val core_ghost_pcm_ref : Type0

val null_core_ghost_pcm_ref : core_ghost_pcm_ref

let ghost_pcm_ref
    (#a:Type u#3)
    (p:FStar.PCM.pcm a)
: Type0
= core_ghost_pcm_ref

val ghost_pcm_pts_to
    #a
    (#p:pcm a)
    ([@@@mkey] r:ghost_pcm_ref p)
    (v:a)
: slprop

val timeless_ghost_pcm_pts_to
    #a
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: Lemma (timeless (ghost_pcm_pts_to r v))
        [SMTPat (timeless (ghost_pcm_pts_to r v))]

val on_ghost_pcm_pts_to_eq l #a #p r v : squash (on l (ghost_pcm_pts_to #a #p r v) == ghost_pcm_pts_to r v)

val ghost_pts_to_not_null
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (v:a)
: stt_ghost (squash (r =!= null_core_ghost_pcm_ref))
            emp_inames
            (ghost_pcm_pts_to r v)
            (fun _ -> ghost_pcm_pts_to r v)

val ghost_alloc
    #a
    (#pcm:pcm a)
    (x:erased a{pcm.refine x})
: stt_ghost (ghost_pcm_ref pcm)
    emp_inames
    emp
    (fun r -> ghost_pcm_pts_to r x)

val ghost_read
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x:erased a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
: stt_ghost (erased (v:a{compatible p x v /\ p.refine v}))
    emp_inames
    (ghost_pcm_pts_to r x)
    (fun v -> ghost_pcm_pts_to r (f v))

val ghost_write
    (#a:Type)
    (#p:pcm a)
    (r:ghost_pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt_ghost unit
    emp_inames
    (ghost_pcm_pts_to r x)
    (fun _ -> ghost_pcm_pts_to r y)

val ghost_share
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a{composable pcm v0 v1})
: stt_ghost unit
    emp_inames
    (ghost_pcm_pts_to r (v0 `op pcm` v1))
    (fun _ -> ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)

[@@allow_ambiguous]
val ghost_gather
    (#a:Type)
    (#pcm:pcm a)
    (r:ghost_pcm_ref pcm)
    (v0:FStar.Ghost.erased a)
    (v1:FStar.Ghost.erased a)
: stt_ghost (squash (composable pcm v0 v1))
    emp_inames
    (ghost_pcm_pts_to r v0 ** ghost_pcm_pts_to r v1)
    (fun _ -> ghost_pcm_pts_to r (op pcm v0 v1))
