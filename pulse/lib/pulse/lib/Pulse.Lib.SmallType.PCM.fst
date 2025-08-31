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
module Pulse.Lib.SmallType.PCM
open Pulse.Lib.SmallType
open Pulse.Lib.Core
module C = Pulse.Lib.Core
module U = Pulse.Lib.Raise
open Pulse.Main
open FStar.PCM
open FStar.Ghost
open Pulse.Lib.PCM.Raise
open Pulse.Lib.WithPure
#lang-pulse

let small_token (inst: small_type u#a) = emp

[@@pulse_unfold]
let pcm_pts_to (#a:Type u#a) (#p:pcm a) ([@@@mkey] r:pcm_ref p) (v:a) : slprop =
  exists* (inst: small_type u#a). big_pcm_pts_to #_ #(raise p) r (U.raise_val v) ** small_token inst

let timeless_pcm_pts_to #a #p r v =
  assert_norm (pcm_pts_to r v ==
    op_exists_Star fun (inst: small_type u#a) ->
      big_pcm_pts_to #_ #(raise p) r (U.raise_val v) ** small_token inst)

ghost fn pts_to_small u#a (#a:Type u#a) (#p:FStar.PCM.pcm a) (r:pcm_ref p) (v:a)
  preserves pcm_pts_to r v
  returns inst: small_type u#a
{
  with inst. assert small_token u#a inst;
  inst
}

ghost fn pts_to_not_null u#a (#a:Type u#a) (#p:FStar.PCM.pcm a) (r:pcm_ref p) (v:a)
  preserves pcm_pts_to r v
  ensures pure (not (is_pcm_ref_null r))
{
  big_pts_to_not_null _ _;
  ()
}

fn alloc u#a (#a:Type u#a) {| inst: small_type u#a |} (#pcm:pcm a) (x:a{pcm.refine x})
  returns r: pcm_ref pcm
  ensures pcm_pts_to r x
{
  fold small_token u#a inst;
  big_alloc #(U.raise_t a) #(raise pcm) (U.raise_val x);
}

fn read u#a (#a:Type u#a) (#p:pcm a) (r:pcm_ref p) (x:erased a)
    (f:(v:a{compatible p x v} -> GTot (y:a{compatible p y v /\ frame_compatible p x v y})))
  requires pcm_pts_to r x
  returns v:(v:a {compatible p x v /\ p.refine v})
  ensures pcm_pts_to r (f v)
{
  with inst. assert small_token inst;
  U.downgrade_val (big_read #(U.raise_t a) #(raise #a #inst p) r (hide (U.raise_val (reveal x))) (raise_refine p x f));
}

fn write u#a (#a:Type u#a) (#p:pcm a) (r:pcm_ref p) (x y:erased a)
    (f:frame_preserving_upd p x y)
  requires pcm_pts_to r x
  ensures pcm_pts_to r y
{
  with inst. assert small_token inst;
  big_write #(U.raise_t a) #(raise #a #inst p) r (hide (U.raise_val (reveal x))) (hide (U.raise_val (reveal y)))
    (raise_upd f)
}

ghost fn share u#a (#a:Type u#a) (#pcm:pcm a) (r:pcm_ref pcm)
    (v0:a) (v1:a {composable pcm v0 v1})
  requires pcm_pts_to r (v0 `op pcm` v1)
  ensures pcm_pts_to r v0
  ensures pcm_pts_to r v1
{
  with inst. assert small_token inst;
  fold small_token inst;
  big_share #(U.raise_t a) #(raise #a #inst pcm) r (U.raise_val v0) (U.raise_val v1);
}

[@@allow_ambiguous]
ghost fn gather u#a (#a:Type u#a) (#pcm:pcm a) (r:pcm_ref pcm) (v0:a) (v1:a)
  requires pcm_pts_to r v0
  requires pcm_pts_to r v1
  returns _: squash (composable pcm v0 v1)
  ensures pcm_pts_to r (op pcm v0 v1)
{
  with inst.  assert big_pcm_pts_to r (U.raise_val #a #inst  v0);
  with inst1. assert big_pcm_pts_to r (U.raise_val #a #inst1 v1);
  let inst = inst;
  drop_ (small_token inst1);
  rewrite each inst1 as inst;
  big_gather r (U.raise_val v0) (U.raise_val v1);
}