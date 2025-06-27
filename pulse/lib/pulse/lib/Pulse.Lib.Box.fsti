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

module Pulse.Lib.Box
#lang-pulse

open FStar.Ghost
open PulseCore.FractionalPermission

open Pulse.Lib.Core
open Pulse.Class.PtsTo

module T = FStar.Tactics.V2
module R = Pulse.Lib.Reference

new
val box ([@@@strictly_positive] a:Type0) : Type0

val null (#a:Type u#0) : box a

val is_null #a (r : box a) : b:bool{b <==> r == null #a}

val pts_to (#a:Type0)
           ([@@@mkey] b:box a)
           (#[T.exact (`1.0R)] p:perm)
           (v:a) : slprop

[@@pulse_unfold]
instance has_pts_to_box (a:Type u#0) : has_pts_to (box a) a = {
  pts_to = pts_to;
}

val pts_to_timeless (#a:Type) ([@@@mkey]r:box a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

fn alloc (#a:Type0) (x:a)
  returns  b : box a
  ensures  pts_to b x
  
fn ( ! ) (#a:Type0) (b:box a) (#v:erased a) (#p:perm)
  requires pts_to b #p v
  returns  x : a
  ensures  pts_to b #p v ** pure (eq2 #a (reveal v) x)

fn ( := ) (#a:Type0) (b:box a) (x:a) (#v:erased a)
  requires pts_to b v
  ensures  pts_to b (hide x)

fn free (#a:Type0) (b:box a) (#v:erased a)
  requires pts_to b v
  ensures  emp

ghost
fn share (#a:Type) (r:box a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v

[@@allow_ambiguous]
ghost
fn gather (#a:Type) (r:box a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:box a)
  requires pts_to r #p v0 ** pts_to r #q v1
  ensures  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)

val box_to_ref  (#a:Type0) (b:box a) : R.ref a

ghost
fn to_ref_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  requires pts_to b #p v
  ensures  R.pts_to (box_to_ref b) #p v

ghost
fn to_box_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  requires R.pts_to (box_to_ref b) #p v
  ensures pts_to b #p v

ghost
fn pts_to_not_null (#a:_) (#p:_) (r:box a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
