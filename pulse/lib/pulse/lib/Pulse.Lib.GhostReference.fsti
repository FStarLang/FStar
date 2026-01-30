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

module Pulse.Lib.GhostReference
#lang-pulse
open FStar.Tactics
open Pulse.Lib.Core
open Pulse.Lib.Send
open Pulse.Main
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.SmallType

[@@erasable]
val ref ([@@@unused] a:Type u#a) : Type u#0

val null #a : ref a
      
inline_for_extraction
instance non_informative_gref (a:Type u#a)
  : NonInformative.non_informative (ref a) =
  { reveal = ((fun x -> x) <: NonInformative.revealer (ref a)) }

val pts_to
  (#a:Type u#a)
  ([@@@mkey] r:ref a)
  (#[exact (`1.0R)] p:perm)
  (n:a)
: slprop

[@@pulse_unfold]
instance has_pts_to_ref (a:Type u#a) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

instance val pts_to_placeless (#a:Type u#a) (r:ref a) (p:perm) (n:a) :
  placeless (pts_to r #p n)

val pts_to_timeless (#a:Type u#a) (r:ref a) (p:perm) (n:a)
  : Lemma (timeless (pts_to r #p n)) [SMTPat (timeless (pts_to r #p n))]

ghost
fn alloc u#a (#a:Type u#a) {| small_type u#a |} (x:a)
  returns  r : ref a
  ensures  r |-> x
  
ghost
fn read u#a (#a:Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : erased a
  ensures  rewrites_to x n

(* alias for read *)
ghost
fn ( ! ) u#a (#a:Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves pts_to r #p n
  returns  x : erased a
  ensures  rewrites_to x n

ghost
fn write u#a (#a:Type u#a) (r:ref a) (x:erased a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

(* alias for write *)
ghost
fn ( := ) u#a (#a:Type u#a) (r:ref a) (x:erased a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

ghost
fn free u#a (#a:Type u#a) (r:ref a) (#n:erased a)
  requires pts_to r n
  ensures  emp

ghost
fn share u#a (#a:Type u#a) (r:ref a) (#v:erased a) (#p:perm)
  requires r |-> Frac p v
  ensures  (r |-> Frac (p /. 2.0R) v) **
           (r |-> Frac (p /. 2.0R) v)

[@@allow_ambiguous]
ghost
fn gather u#a (#a:Type u#a) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires (r |-> Frac p0 x0)
  requires (r |-> Frac p1 x1)
  ensures (r |-> Frac (p0 +. p1) x0)
  ensures pure (x0 == x1)

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq  u#a (#a:Type u#a)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  requires (r |-> Frac p v0)
  requires (r |-> Frac q v1)
  ensures (r |-> Frac p v0)
  ensures (r |-> Frac q v1)
  ensures pure (v0 == v1)

ghost
fn pts_to_perm_bound u#a (#a:Type u#a) (#p:_) (r:ref a) (#v:a)
  requires r |-> Frac p v
  ensures (r |-> Frac p v)
  ensures pure (p <=. 1.0R)

ghost
fn pts_to_not_null u#a (#a:Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (r =!= null)