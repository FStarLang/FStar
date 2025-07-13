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
open Pulse.Lib.HigherArray
module T = FStar.Tactics
val ref ([@@@unused]a:Type u#1) : Type u#0

val null (#a:Type u#1) : ref a

val is_null #a (r : ref a) : b:bool{b <==> r == null #a}

val pts_to (#a:Type) ([@@@mkey]r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a) : slprop

[@@pulse_unfold]
instance has_pts_to_ref (a:Type) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (n:a)
  : Lemma (timeless (pts_to r #p n))
          [SMTPat (timeless (pts_to r #p n))]

val is_full_ref #a (x: ref a) : prop

[@@deprecated "HigherReference.alloc is unsound; only use for model implementations"]
fn alloc (#a:Type) (x:a)
  returns  r : ref a
  ensures  r |-> x
  ensures  pure (is_full_ref r)
  
fn read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n

(* alias for read *)
fn ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n

fn write (#a:Type) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

(* alias for write *)
fn ( := ) (#a:Type) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x

[@@deprecated "HigherReference.free is unsound; only use for model implementations"]
fn free (#a:Type) (r:ref a) (#n:erased a)
  requires pts_to r n
  requires pure (is_full_ref r)

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
  preserves (r |-> Frac p v0) ** (r |-> Frac q v1)
  ensures   pure (v0 == v1)

ghost
fn pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures   pure (p <=. 1.0R)

ghost
fn pts_to_not_null (#a:_) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))

val to_array_ghost #a (r: ref a) : GTot (array a)

unobservable
fn to_array #a (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures arr |-> Frac p (seq![reveal v])
  ensures pure (length arr == 1)

ghost
fn return_to_array #a (r: ref a) #p (#v: Seq.seq a)
  requires to_array_ghost r |-> Frac p v
  requires pure (length (to_array_ghost r) == 1)
  returns _: squash (Seq.length v == 1)
  ensures r |-> Frac p (Seq.index v 0)

val array_at_ghost #a (arr: array a) (i: nat { i < length arr }) : GTot (r:ref a { to_array_ghost r == gsub arr i (i+1) })

unobservable
fn array_at #a (arr: array a) (i: SizeT.t) #p (#v: erased (Seq.seq a) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr #p v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures r |-> Frac p (Seq.index v (SizeT.v i))
  ensures pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i)

ghost
fn return_array_at (#a: Type u#1) (arr: array a) (i: nat) (#p: perm) (#v: a) (#v': Seq.seq a { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires array_at_ghost arr i |-> Frac p v
  requires pts_to_mask arr #p v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr #p (Seq.upd v' i v) (fun k -> mask k \/ k == i)