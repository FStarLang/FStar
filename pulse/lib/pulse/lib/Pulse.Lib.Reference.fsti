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

module Pulse.Lib.Reference
#lang-pulse

open FStar.Tactics
open FStar.Ghost
open Pulse.Main
open Pulse.Lib.Core
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission

val ref ([@@@unused] a:Type u#0) : Type u#0

val pts_to
    (#a:Type)
    ([@@@mkey] r:ref a)
    (#[exact (`1.0R)] p:perm)
    (n:a)
  : slprop

[@@pulse_unfold]
instance has_pts_to_ref (a:Type) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

val pts_to_timeless (#a:Type) ([@@@mkey] r:ref a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

[@@deprecated "Reference.alloc is unsound; use Box.alloc instead"]
fn alloc
  (#a:Type)
  (x:a)
  requires emp
  returns  r : ref a
  ensures  pts_to r x



(* ! *)
fn op_Bang
  (#a:Type)
  (r:ref a)
  (#n:erased a)
  (#p:perm)
  requires pts_to r #p n
  returns  x : a
  ensures  pts_to r #p n ** pure (reveal n == x)



(* := *)
fn op_Colon_Equals
  (#a:Type)
  (r:ref a)
  (x:a)
  (#n:erased a)
  requires pts_to r n
  ensures  pts_to r x


[@@deprecated "Reference.free is unsound; use Box.free instead"]

fn free
  (#a:Type)
  (r:ref a)
  (#n:erased a)
  requires pts_to r n
  ensures  emp



ghost
fn share
  (#a:Type)
  (r:ref a)
  (#v:erased a)
  (#p:perm)
  requires pts_to r #p v
  ensures  pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v


[@@allow_ambiguous]

ghost
fn gather
  (#a:Type)
  (r:ref a)
  (#x0 #x1:erased a)
  (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures  pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)



let cond b (p q:slprop) = if b then p else q

val with_local
  (#a:Type0)
  (init:a)
  (#pre:slprop)
  (#ret_t:Type)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                              (fun v -> post v ** op_exists_Star (pts_to r)))
  : stt ret_t pre post
(* NOTE: Pulse does not have  universe polymorphism yet,
(and ret_t is in a polymorphic universe), so we retain the val above.
The fn below is what it would look like internally in Pulse, but we have to
fix a universe for ret_t. *)
// 
// fn with_local
//   (#a:Type0)
//   (init:a)
//   (#pre:slprop)
//   (#ret_t:Type u#0)
//   (#post:ret_t -> slprop)
//   (body : (r:ref a) -> stt ret_t (pre ** pts_to r init)
//                                  (fun v -> post v ** op_exists_Star (pts_to r)))
//   requires pre
//   returns  v : ret_t
//   ensures  post v
// 

[@@allow_ambiguous]

ghost
fn pts_to_injective_eq
  (#a:Type0)
  (#p #q:perm)
  (#v0 #v1:a)
  (r:ref a)
  requires pts_to r #p v0 ** pts_to r #q v1
  ensures  pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1)



ghost
fn pts_to_perm_bound
  (#a:Type0)
  (#p:perm)
  (r:ref a)
  (#v:a)
  requires pts_to r #p v
  ensures  pts_to r #p v ** pure (p <=. 1.0R)



fn replace
  (#a:Type0)
  (r:ref a)
  (x:a)
  (#v:erased a)
  requires pts_to r v
  returns  res : a
  ensures  pts_to r x ** pure (res == reveal v)

