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
open Pulse.Lib.Core
module A = Pulse.Lib.HigherArray

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

let pts_to (#a: Type u#a) (r:ref a) (#[T.exact (`1.0R)] p:perm) (n:a)
= A.pts_to r #p (singleton n)
let pts_to_timeless _ _ _ = ()

let is_full_ref = A.is_full_array

fn alloc u#a (#a: Type u#a) {| small_type u#a |} (x:a)
  returns r:ref a
  ensures pts_to r x
  ensures pure (is_full_ref r)
{
  let r = A.alloc x 1sz;
  fold (pts_to r #1.0R x);
  r
}

fn read u#a (#a: Type u#a) (r:ref a) (#n:erased a) (#p:perm)
  preserves r |-> Frac p n
  returns  x : a
  ensures  rewrites_to x n
{
  unfold pts_to r #p n;
  let x = A.(r.(0sz));
  fold (pts_to r #p n);
  x
}

inline_for_extraction
let ( ! ) #a = read #a

fn write u#a (#a: Type u#a) (r:ref a) (x:a) (#n:erased a)
  requires r |-> n
  ensures  r |-> x
{
  unfold pts_to r #1.0R n;
  A.(r.(0sz) <- x);
  fold pts_to r #1.0R x;
}

inline_for_extraction
let ( := ) #a = write #a


fn free u#a (#a: Type u#a) (r:ref a) (#n:erased a)
  requires pts_to r #1.0R n
  requires pure (is_full_ref r)
{
  unfold pts_to r #1.0R n;
  A.free r;
}

ghost
fn share u#a (#a: Type u#a) (r:ref a) (#v:erased a) (#p:perm)
  requires pts_to r #p v
  ensures pts_to r #(p /. 2.0R) v ** pts_to r #(p /. 2.0R) v
{
  unfold pts_to r #p v;
  A.share r;
  fold (pts_to r #(p /. 2.0R) v);
  fold (pts_to r #(p /. 2.0R) v);
}

ghost
fn gather u#a (#a: Type u#a) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  requires pts_to r #p0 x0 ** pts_to r #p1 x1
  ensures pts_to r #(p0 +. p1) x0 ** pure (x0 == x1)
{ 
  unfold pts_to r #p0 x0;
  unfold pts_to r #p1 x1;
  A.gather r;
  fold (pts_to r #(p0 +. p1) x0)
}

(* this is universe-polymorphic in ret_t; so can't define it in Pulse yet *)

fn alloc_with_frame u#a (#a: Type u#a) {| small_type u#a |} (init: a) pre
  requires pre
  returns r: ref a
  ensures no_extrude <| (pre ** pts_to r init) ** pure (is_full_ref r)
{
  alloc init
}

fn free_with_frame u#a (#a: Type u#a) (r:ref a) (frame:slprop)
  requires no_extrude <| ((frame ** (exists* (x: a). pts_to r x)) ** pure (is_full_ref r))
  ensures frame
{
  free r;
}

let with_local
    (#a: Type u#a) {| small_type u#a |}
    (init:a)
    (#pre:slprop)
    (#ret_t:Type u#b)
    (#post:ret_t -> slprop) 
    (body: (r:ref a -> stt ret_t (pre ** pts_to u#a r init) (fun v -> post v ** (exists* (x:a). pts_to u#a r x))))
= bind_stt (alloc_with_frame init pre) fun r ->
  bind_stt (frame_stt (pure (is_full_ref r)) (body r)) fun ret ->
  bind_stt (free_with_frame r _) fun _ ->
  return_stt_noeq ret post
  

ghost
fn pts_to_injective_eq
    u#a (#a: Type u#a)
    (#p0 #p1:perm)
    (#v0 #v1:a)
    (r:ref a)
  requires pts_to r #p0 v0 ** pts_to r #p1 v1
  ensures (pts_to r #p0 v0 ** pts_to r #p1 v1) ** pure (v0 == v1)
{
  unfold pts_to r #p0 v0;
  unfold pts_to r #p1 v1;
  A.pts_to_injective_eq r;
  fold pts_to r #p0 v0;
  fold pts_to r #p1 v1;
}


ghost
fn pts_to_perm_bound u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  requires pts_to r #p v
  ensures pts_to r #p v ** pure (p <=. 1.0R)
{
  unfold pts_to r #p v;
  A.pts_to_perm_bound r;
  fold pts_to r #p v;
}

ghost
fn pts_to_not_null u#a (#a: Type u#a) (#p:_) (r:ref a) (#v:a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  A.pts_to_not_null r;
  fold pts_to r #p v;
}

let to_array_ghost r = r

unobservable
fn to_array u#a (#a: Type u#a) (r: ref a) #p (#v: erased a)
  requires r |-> Frac p v
  returns arr: array a
  ensures rewrites_to arr (to_array_ghost r)
  ensures arr |-> Frac p (seq![reveal v])
  ensures pure (length arr == 1)
{
  unfold pts_to r #p v;
  pts_to_len r;
  assert pure (Seq.equal seq![reveal v] (singleton (reveal v)));
  r
}

ghost
fn return_to_array u#a (#a: Type u#a) (r: ref a) #p (#v: Seq.seq a)
  requires to_array_ghost r |-> Frac p v
  requires pure (length (to_array_ghost r) == 1)
  returns _: squash (Seq.length v == 1)
  ensures r |-> Frac p (Seq.index v 0)
{
  pts_to_len r;
  assert pure (singleton (Seq.Base.index v 0) `Seq.equal` v);
  fold pts_to r #p (Seq.index v 0);
}

let array_at_ghost arr i = gsub arr i (i+1)

unobservable
fn array_at u#a (#a: Type u#a) (arr: array a) (i: SizeT.t) #p (#v: erased (Seq.seq a) { SizeT.v i < length arr /\ length arr == Seq.length v }) #mask
  requires pts_to_mask arr #p v mask
  requires pure (mask (SizeT.v i))
  returns r: ref a
  ensures rewrites_to r (array_at_ghost arr (SizeT.v i))
  ensures r |-> Frac p (Seq.index v (SizeT.v i))
  ensures pts_to_mask arr #p v (fun k -> mask k /\ k <> SizeT.v i)
{
  let res = sub arr i (SizeT.v i + 1);
  mask_ext res (singleton (Seq.index v (SizeT.v i))) (fun _ -> True);
  from_mask res;
  fold pts_to res #p (Seq.index v (SizeT.v i));
  mask_mext arr (fun k -> mask k /\ k <> SizeT.v i);
  res
}

ghost
fn return_array_at u#a (#a: Type u#a) (arr: array a) (i: nat) (#p: perm) (#v: a) (#v': Seq.seq a { i < length arr /\ length arr == Seq.length v' }) (#mask: nat->prop)
  requires array_at_ghost arr i |-> Frac p v
  requires pts_to_mask arr #p v' mask
  requires pure (~(mask i))
  ensures pts_to_mask arr #p (Seq.upd v' i v) (fun k -> mask k \/ k == i)
{
  unfold pts_to (array_at_ghost arr i) #p v;
  to_mask (array_at_ghost arr i);
  gsub_elim arr i (i+1);
  join_mask arr;
  mask_ext arr (Seq.upd v' i v) (fun k -> mask k \/ k == i);
}
