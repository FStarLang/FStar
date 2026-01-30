(*
   Copyright 2025 Microsoft Research

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
module Pulse.Lib.GhostPCMReference
#lang-pulse
open Pulse.Lib.SmallType
open Pulse.Lib.Core
open Pulse.Lib.Send
open Pulse.Main
open FStar.PCM

[@@erasable]
val core_ghost_pcm_ref : Type0

val null_core_ghost_pcm_ref : core_ghost_pcm_ref

[@@erasable]
let ghost_pcm_ref (#a: Type u#a) (p: pcm a) : Type0 = core_ghost_pcm_ref

let ghost_pcm_ref_null #a (p:pcm a) : ghost_pcm_ref p = null_core_ghost_pcm_ref

inline_for_extraction
instance non_informative_ghost_pcm_ref (a: Type u#a) (p:pcm a)
  : NonInformative.non_informative (ghost_pcm_ref p) =
  { reveal = ((fun x -> x) <: NonInformative.revealer (ghost_pcm_ref p)) }

[@@erasable]
let gref (#a:Type) (p:pcm a)
: Type0
= ghost_pcm_ref #a p

val pts_to
    (#a:Type)
    (#p:pcm a)
    ([@@@mkey]r:gref p)
    (v:a)
: slprop

instance val pts_to_placeless
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (v:a)
: placeless (pts_to r v)

val pts_to_is_timeless
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (v:a)
: Lemma (timeless (pts_to r v))
        [SMTPat (timeless (pts_to r v))]
        
ghost 
fn alloc u#a (#a:Type u#a)
    (#pcm:pcm a)
    {| inst: small_type u#a |}
    (x:a{pcm.refine x})
  requires emp
  returns  r : gref pcm
  ensures  pts_to r x

ghost 
fn read u#a
    (#a:Type u#a)
    (#p:pcm a)
    (r:gref p)
    (x:a)
    (f:(v:a{compatible p x v}
        -> GTot (y:a{compatible p y v /\
                     FStar.PCM.frame_compatible p x v y})))
                    
  requires pts_to r x
  returns  v : (v:a{compatible p x v /\ p.refine v})
  ensures  pts_to r (f v)

ghost
fn read_simple u#a
    (#a:Type u#a)
    (#p:pcm a)
    (r:gref p)
    (#x:a)
  requires pts_to r x
  returns  v : (v:a{compatible p x v /\ p.refine v})
  ensures  pts_to r x

ghost
fn write u#a
    (#a:Type u#a)
    (#p:pcm a)
    (r:gref p)
    (x y:a)
    (f:FStar.PCM.frame_preserving_upd p x y)
  requires pts_to r x
  ensures  pts_to r y

ghost
fn share u#a
    (#a:Type u#a)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a{composable pcm v0 v1})
  requires pts_to r (v0 `op pcm` v1)
  ensures  pts_to r v0 ** pts_to r v1

[@@allow_ambiguous]
ghost
fn gather u#a
    (#a:Type u#a)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a)
  requires pts_to r v0
  requires pts_to r v1
  returns  squash (composable pcm v0 v1)
  ensures  pts_to r (op pcm v0 v1)

ghost fn pts_to_not_null u#a (#a:Type u#a)
    (#p:pcm a) (r:gref p) (v:a)
  preserves pts_to r v
  ensures pure (r =!= ghost_pcm_ref_null p)