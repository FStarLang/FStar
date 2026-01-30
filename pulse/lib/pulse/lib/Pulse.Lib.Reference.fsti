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
open Pulse.Main
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
open Pulse.Class.PtsTo
open Pulse.Lib.Array.Core
open Pulse.Lib.SmallType
open Pulse.Lib.Send
module T = FStar.Tactics
val ref ([@@@unused]a:Type) : Type0

val null #a : ref a

val is_null #a (r : ref a) : b:bool{b <==> r == null #a}

val pts_to_uninit (#a: Type u#a) ([@@@mkey]r: ref a) : slprop
val pts_to (#a:Type u#a) ([@@@mkey]r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a) : slprop

instance val is_send_pts_to #a r #p n : is_send (pts_to #a r #p n)
instance val is_send_pts_to_uninit #a r : is_send (pts_to_uninit #a r)

[@@pulse_unfold]
instance has_pts_to_ref (a:Type u#a) : has_pts_to (ref a) a = {
  pts_to = (fun r #f v -> pts_to r #f v);
}

val pts_to_timeless (#a: Type u#a) (r:ref a) (p:perm) (n:a)
  : Lemma (timeless (pts_to r #p n))
          [SMTPat (timeless (pts_to r #p n))]
val pts_to_uninit_timeless (#a: Type u#a) (r:ref a)
  : Lemma (timeless (pts_to_uninit r))
          [SMTPat (timeless (pts_to_uninit r))]

val is_full_ref #a (x: ref a) : prop

[@@pulse_intro]
ghost fn forget_init u#a (#a: Type u#a) (r: ref a) #n
  requires pts_to r n
  ensures pts_to_uninit r

[@@deprecated "Reference.alloc_uninit is unsound; only use for model implementations"]
fn alloc_uninit u#a (a: Type u#a) {| small_type u#a |} ()
  returns  r : ref a
  ensures  pts_to_uninit r
  ensures  pure (is_full_ref r)

fn read u#a (#a: Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n

(* alias for read *)
inline_for_extraction
fn ( ! ) u#a (#a: Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n

fn write u#a (#a: Type u#a) (r:ref a) (x:a)
  requires pts_to_uninit r
  ensures  r |-> x

(* alias for write *)
inline_for_extraction
fn ( := ) u#a (#a: Type u#a) (r:ref a) (x:a)
  requires pts_to_uninit r
  ensures  r |-> x

[@@deprecated "Reference.alloc is unsound; only use for model implementations"]
fn alloc u#a (#a: Type u#a) {| small_type u#a |} (x:a)
  returns  r : ref a
  ensures  r |-> x
  ensures  pure (is_full_ref r)

[@@deprecated "Reference.free is unsound; only use for model implementations"]
fn free u#a (#a: Type u#a) (r:ref a)
  requires pts_to_uninit r
  requires pure (is_full_ref r)

ghost
fn share u#a (#a: Type u#a) (r:ref a) (#v:erased a) (#p:perm)
  requires r |-> Frac p v
  ensures  (r |-> Frac (p /. 2.0R) v) **
           (r |-> Frac (p /. 2.0R) v)

[@@allow_ambiguous]
ghost
fn gather u#a (#a: Type u#a) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires (r |-> Frac p0 x0)
  requires (r |-> Frac p1 x1)
  ensures  (r |-> Frac (p0 +. p1) x0) ** pure (x0 == x1)

val with_local
  (#a:Type u#a) {| small_type u#a |}
  (init:a)
  (#pre:slprop)
  (#ret_t:Type u#b)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt ret_t pre (fun r -> post r)

let with_local0
  (#a:Type0)
  (init:a)
  (#pre:slprop)
  (#ret_t:Type u#b)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt ret_t pre (fun r -> post r)
  = with_local init body

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq u#a (#a: Type u#a)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  preserves (r |-> Frac p v0) ** (r |-> Frac q v1)
  ensures   pure (v0 == v1)

ghost
fn pts_to_perm_bound u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures   pure (p <=. 1.0R)

ghost
fn pts_to_not_null u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))

ghost
fn pts_to_uninit_not_null u#a (#a: Type u#a) (r:ref a)
  preserves pts_to_uninit r
  ensures  pure (not (is_null #a r))

val to_array_ghost #a (r: ref a) : GTot (array a)

unobservable
fn to_array_mask u#a (#a: Type u#a) (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures pts_to_mask arr #p seq![Some (reveal v)] (fun _ -> True)
  ensures pure (length arr == 1)

ghost
fn return_to_array_mask u#a (#a: Type u#a) (r: ref a) #p #v #m
  requires pts_to_mask (to_array_ghost r) #p v m
  requires pure (m 0)
  requires pure (Seq.length v == 1 /\ Some? (Seq.index v 0))
  returns _: squash (Seq.length v == 1)
  ensures exists* (v0:a). r |-> Frac p v0 ** pure (Seq.index v 0 == Some v0)

val array_at_ghost (#a: Type u#a) (arr: array a) (i: nat { i < length arr }) : GTot (r:ref a { to_array_ghost r == gsub arr i (i+1) })

unobservable
fn array_at u#a (#a: Type u#a) (arr: array a) (i: SizeT.t) #p
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v /\ Some? (Seq.index v (SizeT.v i)) }) #mask
  requires pts_to_mask arr #p v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures r |-> Frac p (Some?.v (Seq.index v (SizeT.v i)))
  ensures pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i)

unobservable
fn array_at_uninit u#a (#a: Type u#a) (arr: array a) (i: SizeT.t)
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures pts_to_uninit r
  ensures pts_to_mask arr v (fun k -> mask k /\ k <> SizeT.v i)

ghost
fn return_array_at u#a (#a: Type u#a) (arr: array a) (i: nat) (#p: perm) (#v: a) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires array_at_ghost arr i |-> Frac p v
  requires pts_to_mask arr #p v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr #p (Seq.upd v' i (Some v)) (fun k -> mask k \/ k == i)

ghost
fn return_array_at_uninit u#a (#a: Type u#a) (arr: array a) (i: nat) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires pts_to_uninit (array_at_ghost arr i)
  requires pts_to_mask arr v' mask
  requires pure (~(mask i))
  ensures exists* vi. pts_to_mask arr (Seq.upd v' i vi) (fun k -> mask k \/ k == i)

fn replace u#a (#a:Type u#a) (r:ref a) (x:a) (#v:erased a)
  requires r |-> v
  returns  res: a
  ensures  r |-> x
  ensures  rewrites_to res v