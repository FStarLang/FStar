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

module Pulse.Lib.HigherReference
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
module T = FStar.Tactics
val ref ([@@@unused]a:Type u#1) : Type u#0

val pts_to (#a:Type) ([@@@mkey]r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a) : slprop

[@@pulse_unfold]
instance has_pts_to_ref (a:Type) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (n:a)
  : Lemma (timeless (pts_to r #p n))
          [SMTPat (timeless (pts_to r #p n))]

fn alloc (#a:Type) (x:a)
  returns  r : ref a
  ensures  r |-> x
  
fn read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  pure (n == x)

(* alias for read *)
fn ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  pure (n == x)

fn write (#a:Type) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

(* alias for write *)
fn ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

fn free (#a:Type) (r:ref a) (#n:erased a)
  requires pts_to r n
  ensures  emp

ghost
fn share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  requires r |-> Frac p v
  ensures  (r |-> Frac (p /. 2.0R) v) **
           (r |-> Frac (p /. 2.0R) v)

[@@allow_ambiguous]
ghost
fn gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires (r |-> Frac p0 x0) ** (r |-> Frac p1 x1)
  ensures  (r |-> Frac (p0 +. p1) x0) ** pure (x0 == x1)

val with_local
  (#a:Type u#1)
  (init:a)
  (#pre:slprop)
  (#ret_t:Type)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt ret_t pre post

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  requires (r |-> Frac p v0) ** (r |-> Frac q v1)
  ensures  (r |-> Frac p v0) ** (r |-> Frac q v1) ** pure (v0 == v1)

ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  requires r |-> Frac p v
  ensures  (r |-> Frac p v) ** pure (p <=. 1.0R)
