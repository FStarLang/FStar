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

module Pulse.Lib.GhostReference
#lang-pulse
open FStar.Tactics
open Pulse.Lib.Core
open Pulse.Main
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost

[@@erasable]
val ref ([@@@unused] a:Type u#0) : Type u#0

instance val non_informative_gref (a:Type0)
  : NonInformative.non_informative (ref a)

val pts_to (#a:Type)
           ([@@@mkey] r:ref a)
           (#[exact (`1.0R)] p:perm)
           (n:a)
: slprop

[@@pulse_unfold]
instance has_pts_to_ref (a:Type) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

ghost
fn alloc (#a:Type) (x:a)
  returns  r : ref a
  ensures  r |-> x
  
ghost
fn read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : erased a
  ensures  rewrites_to x n

(* alias for  read *)
ghost
fn ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : erased a
  ensures  rewrites_to x n

ghost
fn write (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

(* alias for write *)
ghost
fn ( := ) (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

ghost
fn free (#a:Type) (r:ref a) (#n:erased a)
  requires r |-> n
  ensures  emp

ghost
fn share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  requires r |-> Frac p v
  ensures (r |-> Frac (p /. 2.0R) v) ** (r |-> Frac (p /. 2.0R) v)

[@@allow_ambiguous]
ghost
fn gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires (r |-> Frac p0 x0) ** (r |-> Frac p1 x1)
  ensures  (r |-> Frac (p0 +. p1) x0) ** pure (x0 == x1)

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  preserves (r |-> Frac p v0) ** (r |-> Frac q v1)
  ensures  pure (v0 == v1)

ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures   pure (p <=. 1.0R)
