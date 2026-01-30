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
open FStar.PCM
module PR = Pulse.Lib.PCM.Raise
module U = Pulse.Lib.Raise
module C = Pulse.Lib.Core.Refs
open Pulse.Lib.PCM.Raise
open FStar.Ghost

let core_ghost_pcm_ref = C.core_ghost_pcm_ref
let null_core_ghost_pcm_ref = C.null_core_ghost_pcm_ref


let small_token (inst: small_type u#a) = emp

[@@pulse_unfold]
let pts_to (#a:Type u#a) (#p:pcm a) ([@@@mkey] r:ghost_pcm_ref p) (v:a) : slprop =
  exists* (inst: small_type u#a). C.ghost_pcm_pts_to #_ #(raise p) r (U.raise_val v) ** small_token inst

ghost fn placeless_ghost_pcm_pts_to' #a #p r v : placeless (C.ghost_pcm_pts_to #a #p r v) = l1 l2 {
  C.on_ghost_pcm_pts_to_eq l1 r v;
  C.on_ghost_pcm_pts_to_eq l2 r v;
  rewrite on l1 (C.ghost_pcm_pts_to r v) as on l2 (C.ghost_pcm_pts_to r v)
}
instance placeless_ghost_pcm_pts_to #a #p = placeless_ghost_pcm_pts_to' #a #p

instance pts_to_placeless #a #p r v = Tactics.Typeclasses.solve

let pts_to_is_timeless #a #p r v =
  assert_norm (pts_to r v ==
    op_exists_Star fun (inst: small_type u#a) ->
      C.ghost_pcm_pts_to #_ #(raise p) r (U.raise_val v) ** small_token inst)

ghost 
fn alloc u#a (#a:Type u#a)
    (#pcm:pcm a)
    {| inst: small_type u#a |}
    (x:a{pcm.refine x})
  returns  r : gref pcm
  ensures  pts_to r x
{
  fold small_token u#a inst;
  C.ghost_alloc #(U.raise_t a) #(raise pcm) (U.raise_val x);
}
  
ghost
fn read u#a
    (#a:Type u#a)
    (#p:pcm a)
    (r:gref p)
    (x:a)
    (f: (v:a{FStar.PCM.compatible #a p x v}
          -> GTot (y:a{compatible p y v /\
                        FStar.PCM.frame_compatible p x v y})))
  requires pts_to r x
  returns v:(v:a { compatible p x v /\ p.refine v })
  ensures pts_to r (f v)
{
  with inst. unfold small_token u#a inst; let inst = inst; fold small_token inst;
  U.downgrade_val (C.ghost_read #(U.raise_t a) #(raise p) r (hide (U.raise_val (reveal x))) (raise_refine p x f));
}


let identity_frame_compatible
      #a (p:FStar.PCM.pcm a)
      (x:a)
      (v:a{FStar.PCM.compatible p x v})
: y:a { FStar.PCM.compatible p y v /\ FStar.PCM.frame_compatible p x v y }
= x

let read_simple
    (#a:Type)
    (#p:pcm a)
    (r:gref p)
    (#x:a)
= read #a #p r x (identity_frame_compatible p x)

ghost
fn write u#a
    (#a:Type u#a)
    (#p:pcm a)
    (r:gref p)
    (x y:a)
    (f:FStar.PCM.frame_preserving_upd p x y)
  requires pts_to r x
  ensures  pts_to r y
{
  with inst. unfold small_token u#a inst; let inst = inst; fold small_token inst;
  C.ghost_write #(U.raise_t a) #(raise p) r (hide (U.raise_val (reveal x))) (hide (U.raise_val (reveal y)))
    (raise_upd f)
}

ghost
fn share u#a
    (#a:Type u#a)
    (#pcm:pcm a)
    (r:gref pcm)
    (v0:a)
    (v1:a{composable pcm v0 v1})
  requires pts_to r (v0 `op pcm` v1)
  ensures pts_to r v0
  ensures pts_to r v1
{
  with inst. unfold small_token u#a inst; let inst = inst;
  fold small_token inst;
  fold small_token inst;
  C.ghost_share #_ #(PR.raise pcm) r (U.raise_val v0) (U.raise_val v1)
}

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
{
  with inst. assert C.ghost_pcm_pts_to #_ #(raise #a #inst pcm) r (U.raise_val #a #inst v1);
  drop_ (small_token inst);
  C.ghost_gather #_ #(PR.raise #a #inst pcm) r (U.raise_val #a #inst v0) (U.raise_val #a #inst v1)
}

ghost fn pts_to_not_null u#a (#a:Type u#a)
    (#p:pcm a) (r:gref p) (v:a)
  preserves pts_to r v
  ensures pure (r =!= ghost_pcm_ref_null p)
{
  C.ghost_pts_to_not_null r _;
  ()
}