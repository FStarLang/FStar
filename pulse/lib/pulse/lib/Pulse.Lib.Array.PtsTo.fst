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

module Pulse.Lib.Array.PtsTo
#lang-pulse
open Pulse.Main
open FStar.Tactics.V2
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.WithPure

let pts_to (#elt: Type u#a) (a: array elt) (#p: perm) (s: Seq.seq elt) : Tot slprop =
  exists* (s': Seq.seq (option elt)). pts_to_mask a #p s' (fun i -> True)
    ** pure (Seq.length s == Seq.length s' /\
      forall (i: nat). i < Seq.length s' ==> Some (Seq.index s i) == Seq.index s' i)

let is_send_pts_to _ _ = Tactics.Typeclasses.solve

ghost fn to_mask u#a (#t: Type u#a) (arr: array t) #f (#v: erased _)
  requires arr |-> Frac f v
  ensures exists* (s: Seq.seq (option t)).
    pts_to_mask arr #f s (fun _ -> True) **
    pure (Seq.length s == Seq.length v /\
      (forall (i: nat). i < Seq.length s ==>
        Seq.index s i == Some (Seq.index v i)))
{
  unfold pts_to arr #f v;
}

ghost fn from_mask u#a (#t: Type u#a) (arr: array t) #f #v #mask
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> mask i /\ Some? (Seq.index v i))
  ensures exists* (v': Seq.seq t).
    arr |-> Frac f v' **
    pure (Seq.length v' == Seq.length v /\
      (forall (i: nat). i < Seq.length v' ==>
        Some (Seq.index v' i) == Seq.index v i))
{
  mask_mext arr (fun _ -> True);
  fold pts_to #t arr #f (Seq.init_ghost (Seq.length v) (fun i -> Some?.v (Seq.index v i)));
}

let pts_to_timeless x p s =
  assert_norm (timeless (pts_to x #p s))

ghost
fn pts_to_len
  u#a (#elt: Type u#a)
  (a:array elt)
  (#p:perm)
  (#x:Seq.seq elt)
  preserves pts_to a #p x
  ensures pure (length a == Seq.length x)
{
  unfold pts_to a #p x;
  pts_to_mask_len a;
  fold pts_to a #p x;
}

ghost
fn pts_to_not_null u#a (#a: Type u#a) (#p:_) (r:array a) (#v:Seq.seq a)
  preserves r |-> Frac p v
  ensures  pure (not (is_null #a r))
{
  unfold pts_to r #p v;
  pts_to_mask_not_null r;
  fold pts_to r #p v;
}

module R = Pulse.Lib.Reference

fn alloc
    u#a (#elt: Type u#a) {| small_type u#a |}
    (x: elt)
    (n: SZ.t)
  returns a:array elt
ensures 
  pts_to a (Seq.create (SZ.v n) x) **
  pure (length a == SZ.v n /\ is_full_array a)
{
  let a = mask_alloc elt n;
  let mut i = 0sz;
  while (((R.read i) `SZ.lt` n))
    invariant live i
    invariant exists* (s: Seq.seq (option elt)).
      pts_to_mask a #1.0R s (fun _ -> True) **
      pure (SZ.v (R.read i) <= SZ.v n /\ Seq.length s == SZ.v n /\
        (forall (j: nat). j < SZ.v (R.read i) ==> Seq.index s j == Some x))
  {
    mask_write a (R.read i) x;
    R.write i ((R.read i) `SZ.add` 1sz);
  };
  fold pts_to a (Seq.create (SZ.v n) x);
  a
}

inline_for_extraction
fn read
    u#a (#t: Type u#a)
    (a: array t)
    (i: SZ.t)
    (#p: perm)
    (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
  preserves pts_to a #p s
  returns res:t
  ensures pure (res == Seq.index s (SZ.v i))
{
  unfold pts_to a #p s;
  let res = mask_read a i;
  fold pts_to a #p s;
  res
}

let op_Array_Access = read

inline_for_extraction
fn write
    u#a (#t: Type u#a)
    (a: array t)
    (i: SZ.t)
    (v: t)
    (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
  requires pts_to a s
  ensures exists* s'. pts_to a s' ** pure (s' == Seq.upd s (SZ.v i) v)
{
  unfold pts_to a #1.0R s;
  mask_write a i v;
  fold pts_to a #1.0R (Seq.upd s (SZ.v i) v);
}

let op_Array_Assignment = write

inline_for_extraction
fn free
    u#a (#elt: Type u#a)
    (a: array elt)
    (#s: Ghost.erased (Seq.seq elt))
  requires pts_to a s
  requires pure (is_full_array a)
{
  unfold pts_to a s;
  mask_free a;
}

ghost
fn share
  u#a (#elt: Type u#a)
  (arr:array elt)
  (#s:Ghost.erased (Seq.seq elt))
  (#p:perm)
  requires pts_to arr #p s
  ensures pts_to arr #(p /. 2.0R) s
  ensures pts_to arr #(p /. 2.0R) s
{
  unfold pts_to arr #p s;
  mask_share arr;
  fold pts_to arr #(p /. 2.0R) s;
  fold pts_to arr #(p /. 2.0R) s;
}

[@@allow_ambiguous]
ghost
fn gather
  u#a (#a: Type u#a)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0
  requires pts_to arr #p1 s1
  ensures pts_to arr #(p0 +. p1) s0
  ensures pure (s0 == s1)
{
  unfold pts_to arr #p0 s0;
  unfold pts_to arr #p1 s1;
  mask_gather arr;
  assert pure (s0 `Seq.equal` s1);
  fold pts_to arr #(p0 +. p1) s0;
}

[@@allow_ambiguous]
ghost
fn pts_to_injective_eq
    u#a (#a: Type u#a)
    (#p0 #p1:perm)
    (#s0 #s1:Seq.seq a)
    (arr:array a)
  preserves pts_to arr #p0 s0
  preserves pts_to arr #p1 s1
  ensures pure (s0 == s1)
{
  unfold pts_to arr #p0 s0;
  unfold pts_to arr #p1 s1;
  pts_to_mask_injective_eq arr;
  assert pure (Seq.equal s0 s1);
  fold pts_to arr #p0 s0;
  fold pts_to arr #p1 s1;
}

ghost
fn pts_to_perm_bound u#a (#a: Type u#a) (#p:_) (arr: array a) (#s:Seq.seq a)
  preserves pts_to arr #p s
  requires pure (Seq.length s > 0)
  ensures pure (p <=. 1.0R)
{
  unfold pts_to arr #p s;
  pts_to_mask_perm_bound arr;
  fold pts_to arr #p s;
}

fn with_local u#a (#a:Type0) (init:a) (len:SZ.t) (#pre:slprop) (ret_t:Type u#a)
    (#post:ret_t -> slprop)
    (body:(arr:array a) -> stt ret_t (pre **
                                      (pts_to arr (Seq.create (SZ.v len) init) **
                                      (pure (is_full_array arr) **
                                        pure (length arr == SZ.v len))))
                                    (fun r -> post r ** (exists* v. pts_to arr v)))
  requires pre
  returns r: ret_t
  ensures post r
{
  let arr = alloc init len;
  let r = body arr;
  free arr;
  r
}