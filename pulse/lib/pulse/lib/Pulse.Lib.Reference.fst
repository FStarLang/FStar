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
open Pulse.Lib.Core
module A = Pulse.Lib.Array.Core

let ref a = A.array a

let null #a : ref a = A.null

let is_null #a (r : ref a)
  : b:bool{b <==> r == null #a}
= A.is_null r

let singleton #a (x:a) : Seq.seq a = Seq.create 1 x
let singleton_inj #a (x: a) : Lemma (Seq.index (singleton x) 0 == x) [SMTPat (singleton x)] = ()
let upd_singleton #a (x y: a) :
    Lemma (Seq.upd (singleton x) 0 y == singleton y)
      [SMTPat (Seq.upd (singleton x) 0 y)] =
  assert Seq.equal (Seq.upd (singleton x) 0 y) (singleton y)

let pts_to_uninit (#a: Type u#a) ([@@@mkey]r: ref a) : slprop =
  exists* s. pure (Seq.length s == 1) ** A.pts_to_mask r s (fun _ -> True)

let pts_to (#a: Type u#a) (r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a) =
  exists* s. pure (Seq.length s == 1 /\ Seq.index s 0 == Some n) **
    A.pts_to_mask r #p s (fun _ -> True)

let is_send_pts_to r n = Tactics.Typeclasses.solve
let is_send_pts_to_uninit r = Tactics.Typeclasses.solve

let pts_to_timeless r p n = assert_norm (timeless (pts_to r #p n))
let pts_to_uninit_timeless r = assert_norm (timeless (pts_to_uninit r))

let is_full_ref = A.is_full_array

[@@pulse_intro]
ghost fn forget_init u#a (#a: Type u#a) (r: ref a) #n
  requires pts_to r n
  ensures pts_to_uninit r
{
  unfold pts_to r n;
  fold pts_to_uninit r;
}

fn alloc_uninit u#a (a: Type u#a) {| small_type u#a |} ()
  returns  r : ref a
  ensures  pts_to_uninit r
  ensures  pure (is_full_ref r)
{
  let r = A.mask_alloc a 1sz;
  fold (pts_to_uninit r);
  r
}

fn read u#a (#a: Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n
{
  unfold pts_to r #p n;
  let x = A.mask_read r 0sz;
  fold (pts_to r #p n);
  x
}

inline_for_extraction
let ( ! ) #a = read #a

fn write u#a (#a: Type u#a) (r:ref a) (x:a)
  requires pts_to_uninit r
  ensures  r |-> x
{
  unfold pts_to_uninit r;
  A.mask_write r 0sz x;
  fold pts_to r #1.0R x;
}

inline_for_extraction
let ( := ) #a = write #a

fn alloc u#a (#a: Type u#a) {| small_type u#a |} (x:a)
  returns r:ref a
  ensures pts_to r x
  ensures pure (is_full_ref r)
{
  let r = alloc_uninit a ();
  r := x;
  r
}

fn free u#a (#a: Type u#a) (r:ref a)
  requires pts_to_uninit r
  requires pure (is_full_ref r)
{
  unfold pts_to_uninit r;
  A.mask_free r;
}

ghost
fn share u#a (#a: Type u#a) (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  A.mask_share r;
  fold (pts_to r #(p /. 2.0R) v);
  fold (pts_to r #(p /. 2.0R) v);
}

ghost
fn gather u#a (#a: Type u#a) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0
  requires pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  A.mask_gather r;
  fold (pts_to r #(p0 +. p1) x0)
}

fn with_local u#a u#b
  (#a:Type u#a) {| small_type u#a |}
  (init:a)
  (#pre:slprop)
  (#ret_t:Type u#b)
  (#post:ret_t -> slprop)
  (body:(r:ref a) -> stt ret_t (pre ** pts_to r init)
                               (fun v -> post v ** (exists* (x:a). pts_to r x)))
  : stt ret_t pre (fun r -> post r) =
{
  let x = alloc init;
  let r = body x;
  free x;
  r
}

ghost
fn pts_to_injective_eq
    u#a (#a: Type u#a)
    (#p0 #p1:perm)
    (#v0 #v1:a)
    (r:ref a)
  requires pts_to r #p0 v0
  requires pts_to r #p1 v1
  ensures (pts_to r #p0 v0 ** pts_to r #p1 v1) ** pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  A.pts_to_mask_injective_eq r;
  fold pts_to r #p0 v0;
  fold pts_to r #p1 v1;
}


ghost
fn pts_to_perm_bound u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  A.pts_to_mask_perm_bound r;
  fold pts_to r #p v;
}

ghost
fn pts_to_not_null u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  A.pts_to_mask_not_null r;
  fold pts_to r #p v;
}

ghost
fn pts_to_uninit_not_null u#a (#a: Type u#a) (r:ref a)
  preserves pts_to_uninit r
  ensures  pure (not (is_null #a r))
{
  unfold pts_to_uninit r;
  A.pts_to_mask_not_null r;
  fold pts_to_uninit r;
}

let to_array_ghost r = r

unobservable
fn to_array_mask u#a (#a: Type u#a) (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures pts_to_mask arr #p seq![Some (reveal v)] (fun _ -> True)
  ensures pure (length arr == 1)
{
  unfold pts_to r #p v;
  pts_to_mask_len r;
  with v'. assert pts_to_mask r #p v' _;
  assert pure (v' `Seq.equal` seq![Some (reveal v)]);
  r
}

ghost
fn return_to_array_mask u#a (#a: Type u#a) (r: ref a) #p #v #m
  requires pts_to_mask (to_array_ghost r) #p v m
  requires pure (m 0)
  requires pure (Seq.length v == 1 /\ Some? (Seq.index v 0))
  returns _: squash (Seq.length v == 1)
  ensures exists* (v0:a). r |-> Frac p v0 ** pure (Seq.index v 0 == Some v0)
{
  pts_to_mask_len r;
  mask_mext r (fun _ -> True);
  fold pts_to r #p (Some?.v (Seq.index v 0));
}

let array_at_ghost arr i = gsub arr i (i+1)

unobservable
fn array_at u#a (#a: Type u#a) (arr: array a) (i: SizeT.t) #p
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v /\ Some? (Seq.index v (SizeT.v i)) }) #mask
  requires pts_to_mask arr #p v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures r |-> Frac p (Some?.v (Seq.index v (SizeT.v i)))
  ensures pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i)
{
  let res = sub arr i (SizeT.v i + 1);
  mask_ext res (singleton (Seq.index v (SizeT.v i))) (fun _ -> True);
  fold pts_to res #p (Some?.v (Seq.index v (SizeT.v i)));
  mask_mext arr (fun k -> mask k /\ k <> SizeT.v i);
  res
}

unobservable
fn array_at_uninit u#a (#a: Type u#a) (arr: array a) (i: SizeT.t)
    (#v: erased (Seq.seq (option a)) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures pts_to_uninit r
  ensures pts_to_mask arr v (fun k -> mask k /\ k <> SizeT.v i)
{
  let res = sub arr i (SizeT.v i + 1);
  mask_ext res (singleton (Seq.index v (SizeT.v i))) (fun _ -> True);
  fold pts_to_uninit res;
  mask_mext arr (fun k -> mask k /\ k <> SizeT.v i);
  res
}

ghost
fn return_array_at u#a (#a: Type u#a) (arr: array a) (i: nat) (#p: perm) (#v: a) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires array_at_ghost arr i |-> Frac p v
  requires pts_to_mask arr #p v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr #p (Seq.upd v' i (Some v)) (fun k -> mask k \/ k == i)
{
  unfold pts_to (array_at_ghost arr i) #p v;
  gsub_elim arr i (i+1);
  join_mask arr;
  mask_ext arr (Seq.upd v' i (Some v)) (fun k -> mask k \/ k == i);
}

ghost
fn return_array_at_uninit u#a (#a: Type u#a) (arr: array a) (i: nat) (#v': Seq.seq (option a) { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires pts_to_uninit (array_at_ghost arr i)
  requires pts_to_mask arr v' mask
  requires pure (~(mask i))
  ensures exists* vi. pts_to_mask arr (Seq.upd v' i vi) (fun k -> mask k \/ k == i)
{
  unfold pts_to_uninit (array_at_ghost arr i);
  with vi. assert pts_to_mask (array_at_ghost arr i) vi _;
  gsub_elim arr i (i+1);
  join_mask arr;
  mask_ext arr (Seq.upd v' i (Seq.index vi 0)) (fun k -> mask k \/ k == i);
}

fn replace u#a (#a:Type u#a) (r:ref a) (x:a) (#v:erased a)
  requires r |-> v
  returns  res: a
  ensures  r |-> x
  ensures  rewrites_to res v
{
  let y = !r;
  r := x;
  y
}