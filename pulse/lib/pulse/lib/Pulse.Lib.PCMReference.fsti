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
module Pulse.Lib.PCMReference
open Pulse.Lib.SmallType
open Pulse.Lib.Core
open Pulse.Main
open FStar.PCM
open FStar.Ghost
#lang-pulse

val core_pcm_ref : Type0
val null_core_pcm_ref : core_pcm_ref
val is_null_core_pcm_ref (r: core_pcm_ref) :
  b:bool { b <==> r == null_core_pcm_ref }

let pcm_ref (#a: Type u#a) (p: pcm a) : Type0 = core_pcm_ref

let pcm_ref_null #a (p:pcm a) : pcm_ref p = null_core_pcm_ref
let is_pcm_ref_null #a (#p: pcm a) (r: pcm_ref p) :
    b:bool { b <==> r == pcm_ref_null p } =
  is_null_core_pcm_ref r

val pcm_pts_to (#a:Type u#a) (#p:pcm a) ([@@@mkey] r:pcm_ref p) (v:a) : slprop

val timeless_pcm_pts_to (#a:Type u#a) (#p:pcm a) (r:pcm_ref p) (v:a)
: Lemma (timeless (pcm_pts_to r v)) [SMTPat (timeless (pcm_pts_to r v))]

ghost fn pts_to_small u#a (#a: Type u#a) (#p:FStar.PCM.pcm a) (r:pcm_ref p) (v:a)
  preserves pcm_pts_to r v
  returns inst: small_type u#a

ghost fn pts_to_not_null u#a (#a:Type u#a) (#p:FStar.PCM.pcm a) (r:pcm_ref p) (v:a)
  preserves pcm_pts_to r v
  ensures pure (not (is_pcm_ref_null r))

fn alloc u#a (#a:Type u#a) (#pcm:pcm a) {| small_type u#a |} (x:a{pcm.refine x})
  returns r: pcm_ref pcm
  ensures pcm_pts_to r x

fn read u#a (#a:Type u#a) (#p:pcm a) (r:pcm_ref p) (x:erased a)
    (f:(v:a{compatible p x v} -> GTot (y:a{compatible p y v /\ frame_compatible p x v y})))
  requires pcm_pts_to r x
  returns v:(v:a {compatible p x v /\ p.refine v})
  ensures pcm_pts_to r (f v)

fn write u#a (#a:Type u#a) (#p:pcm a) (r:pcm_ref p) (x y:erased a)
    (f:frame_preserving_upd p x y)
  requires pcm_pts_to r x
  ensures pcm_pts_to r y

ghost fn share u#a (#a:Type u#a) (#pcm:pcm a) (r:pcm_ref pcm)
    (v0:a) (v1:a {composable pcm v0 v1})
  requires pcm_pts_to r (v0 `op pcm` v1)
  ensures pcm_pts_to r v0
  ensures pcm_pts_to r v1

[@@allow_ambiguous]
ghost fn gather u#a (#a:Type u#a) (#pcm:pcm a) (r:pcm_ref pcm) (v0:a) (v1:a)
  requires pcm_pts_to r v0
  requires pcm_pts_to r v1
  returns _: squash (composable pcm v0 v1)
  ensures pcm_pts_to r (op pcm v0 v1)