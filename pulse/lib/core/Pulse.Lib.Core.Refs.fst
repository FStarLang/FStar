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
friend PulseCore.InstantiatedSemantics
friend Pulse.Lib.Core
module I = PulseCore.InstantiatedSemantics
module A = PulseCore.Atomic
module T = FStar.Tactics.V2
open PulseCore.InstantiatedSemantics
open PulseCore.FractionalPermission
open PulseCore.Observability
module Sep = PulseCore.IndirectionTheorySep
open Pulse.Lib.Core

//////////////////////////////////////////////////////////////////////////
// References
//////////////////////////////////////////////////////////////////////////
let core_pcm_ref = PulseCore.Action.core_ref
let null_core_pcm_ref = PulseCore.Action.core_ref_null
let is_null_core_pcm_ref r = PulseCore.Action.is_core_ref_null r

let pcm_pts_to #a (#p:pcm a) (r:pcm_ref p) (v:a) =
  PulseCore.Action.pts_to #a #p r v
let timeless_pcm_pts_to #a #p r v = PulseCore.Action.timeless_pts_to #a #p r v
let on_pcm_pts_to_eq = PulseCore.Action.on_pcm_pts_to_eq
let pts_to_not_null #a #p r v = A.pts_to_not_null #a #p r v

let alloc
    (#a:Type)
    (#pcm:pcm a)
    (x:a{pcm.refine x})
: stt (pcm_ref pcm)
    emp
    (fun r -> pcm_pts_to r x)
= A.lift_atomic (A.alloc #a #pcm x)

let read
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
= A.lift_atomic (A.read r x f)

let write
    (#a:Type)
    (#p:pcm a)
    (r:pcm_ref p)
    (x y:Ghost.erased a)
    (f:FStar.PCM.frame_preserving_upd p x y)
: stt unit
    (pcm_pts_to r x)
    (fun _ -> pcm_pts_to r y)
= A.lift_atomic (A.write r x y f)

let share = A.share
let gather = A.gather

////////////////////////////////////////////////////////
// ghost refs
////////////////////////////////////////////////////////
let core_ghost_pcm_ref = PulseCore.Action.core_ghost_ref

let null_core_ghost_pcm_ref = PulseCore.Action.core_ghost_ref_null

let ghost_pcm_pts_to #a #p r v = PulseCore.Action.ghost_pts_to #a #p r v
let timeless_ghost_pcm_pts_to #a #p r v = PulseCore.Action.timeless_ghost_pts_to #a #p r v
let on_ghost_pcm_pts_to_eq = PulseCore.Action.on_ghost_pcm_pts_to_eq
let ghost_pts_to_not_null #a #p r v = A.ghost_pts_to_not_null #a #p r v
let ghost_alloc = A.ghost_alloc
let ghost_read = A.ghost_read
let ghost_write = A.ghost_write
let ghost_share = A.ghost_share
let ghost_gather = A.ghost_gather
