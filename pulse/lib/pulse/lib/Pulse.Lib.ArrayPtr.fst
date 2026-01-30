(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.ArrayPtr
#lang-pulse

type base_t t = A.array t

let base_len (#t: Type) (base: base_t t) : GTot nat = if A.is_null base then 0 else A.length base

noeq
type ptr t = {
    base: A.array u#0 t;
    offset: (offset: SZ.t { SZ.v offset <= base_len base})
}

let base a = a.base
let offset a = SZ.v a.offset

let null #_ = {
  base = A.null;
  offset = 0sz;
}

let g_is_null a = A.is_null a.base

let pts_to s #p v =
  A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v

ghost fn pts_to_not_null
  (#t:Type)
  (s:ptr t)
  (#p:perm)
  (#v : Seq.seq t)
requires
  (pts_to s #p v)
ensures
  (pts_to s #p v ** pure (not (g_is_null s)))
{
  unfold (pts_to s #p v);
  A.pts_to_range_prop s.base;
  fold (pts_to s #p v);
}

fn is_null
  (#t:Type)
  (s:ptr t)
  (#p:perm)
  (#v : Ghost.erased (Seq.seq t))
requires
  (pts_to_or_null s #p v)
returns res: bool
ensures
  (pts_to_or_null s #p v ** pure (res == g_is_null s))
{
  A.is_null s.base
}

let pts_to_timeless x p s = ()

let is_from_array s sz a =
    pure (sz == A.length a /\ s.base == a)

fn from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
    requires A.pts_to a #p v
    returns s: ptr t
    ensures pts_to s #p v ** is_from_array s (Seq.length v) a
{
    A.pts_to_len a;
    let res = {
        base = a;
        offset = 0sz;
    };
    fold (is_from_array res (Seq.length v) a);
    A.pts_to_range_intro a p v;
    rewrite (A.pts_to_range a 0 (A.length a) #p v)
        as (A.pts_to_range res.base (SZ.v res.offset) (SZ.v res.offset + Seq.length v) #p v);
    fold pts_to res #p v;
    res
}

ghost
fn to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#v: Seq.seq t)
    requires pts_to s #p v
    requires is_from_array s (Seq.length v) a
    ensures A.pts_to a #p v
{
    unfold is_from_array s (Seq.length v) a;
    unfold pts_to s #p v;
    A.pts_to_range_prop s.base;
    rewrite (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v)
        as (A.pts_to_range a 0 (A.length a) #p v);
    A.pts_to_range_elim a _ _;
}

let is_from_ref #t s a = rewrites_to s.base (to_array_ghost a) ** pure (s.offset == 0sz /\ A.length (to_array_ghost a) == 1)

module RA = Pulse.Lib.Reference.Array

fn from_ref (#t: Type) (a: ref t) (#p: perm) (#v: Ghost.erased (t))
requires
    (R.pts_to a #p v)
returns s: ptr t
ensures
    (pts_to s #p (Seq.create 1 (Ghost.reveal v)) ** is_from_ref s a)
{
  let arr = RA.to_array a;
  A.pts_to_range_intro arr _ _;
  let res = {
    base = arr;
    offset = 0sz;
  };
  assert (pure (Seq.equal (Seq.cons (Ghost.reveal v) Seq.empty) (Seq.Base.create 1 (Ghost.reveal v))));
  with from to len va . rewrite A.pts_to_range from
      to
      len
      #p
      va
  as A.pts_to_range res.base
      (SZ.v res.offset)
      (SZ.v res.offset + Seq.Base.length (Seq.Base.create 1 v))
      #p
      (Seq.Base.create 1 (Ghost.reveal v));
  fold pts_to res #p (Seq.create 1 (Ghost.reveal v));
  fold (is_from_ref res a);
  res
}

ghost fn to_ref (#t: Type) : to_ref_t t =
  (s: _) (a: _) (#p: _) (#v: _)
{
  unfold is_from_ref s a;
  unfold pts_to s #p v;
  A.pts_to_range_prop _;
  rewrite A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + Seq.Base.length v) #p v
    as A.pts_to_range (R.to_array_ghost a) 0 (A.length s.base) #p v;
  A.pts_to_range_elim _ _ _;
  RA.return_to_array a;
  ()
}

open Pulse.Lib.WithPure

let is_as_ref #t s p a : slprop =
  with_pure (SZ.v s.offset < base_len s.base) fun _ ->
  exists* (w: Seq.seq (option t)).
  rewrites_to a (array_at_ghost s.base (SizeT.v s.offset)) **
  pts_to_mask s.base #p w (fun _ -> False)

fn as_ref (#t: Type) : as_ref_t t =
  (s: _) (#p: _) (#v: _)
{
  unfold (pts_to s #p v);
  A.pts_to_range_prop _;
  unfold_pts_to_range _ _ _ _;
  gsub_elim _ _ _;
  let res = R.array_at s.base s.offset;
  mask_mext _ (fun _ -> False);
  fold (is_as_ref s p res);
  res
}

ghost fn return_as_ref (#t: Type) (a: ref t) (#p: perm) (#v:t) (#s: ptr t)
requires
    (R.pts_to a #p v ** is_as_ref s p a)
ensures
    (pts_to s #p (Seq.create 1 (Ghost.reveal v)))
{
  unfold (is_as_ref s p a);
  A.pts_to_mask_len _;
  R.return_array_at s.base (SZ.v s.offset);
  A.gsub_intro s.base (SZ.v s.offset) (SZ.v s.offset + 1);
  A.fold_pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + 1) (Seq.create 1 v);
  fold (pts_to s #p (Seq.create 1 (Ghost.reveal v)));
}

fn op_Array_Access
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t))
   requires
     pts_to a #p s ** pure (SZ.v i < Seq.length s)
   returns res: t
   ensures
            pts_to a #p s **
            pure (
              SZ.v i < Seq.length s /\
              res == Seq.index s (SZ.v i))
{
    unfold pts_to a #p s;
    A.pts_to_range_prop a.base;
    let res = A.pts_to_range_index a.base (SZ.add a.offset i);
    fold pts_to a #p s;
    res
}

fn op_Array_Assignment
        (#t: Type)
        (a: ptr t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t))
   requires
     pts_to a s ** pure (SZ.v i < Seq.length s)
   ensures exists* s' .
            pts_to a s' **
            pure (SZ.v i < Seq.length s /\
              s' == Seq.upd s (SZ.v i) v
            )
{
    unfold pts_to a s;
    A.pts_to_range_prop a.base;
    let res = A.pts_to_range_upd a.base (SZ.add a.offset i) v;
    rewrite
      A.pts_to_range a.base (SZ.v a.offset) (SZ.v a.offset + Seq.length s) (Seq.upd s (SZ.v i) v)
    as
      A.pts_to_range a.base (SZ.v a.offset) (SZ.v a.offset + Seq.length (Seq.upd s (SZ.v i) v)) (Seq.upd s (SZ.v i) v);
    fold pts_to a (Seq.upd s (SZ.v i) v);
    ();
}

ghost
fn share
  (#a:Type)
  (arr:ptr a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
  requires pts_to arr #p s
  ensures pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s
{
    unfold pts_to arr #p s;
    A.pts_to_range_share arr.base;
    fold pts_to arr #(p /. 2.0R) s;
    fold pts_to arr #(p /. 2.0R) s;
}

ghost
fn gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0
  requires pts_to arr #p1 s1
  requires pure (Seq.length s0 == Seq.length s1)
  ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
    unfold pts_to arr #p0 s0;
    unfold pts_to arr #p1 s1;
    rewrite each Seq.length s1 as Seq.length s0;
    A.pts_to_range_gather arr.base #_ #_ #s0 #s1 #p0 #p1;
    fold pts_to arr #(p0 +. p1) s0
}

fn split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns s' : ptr t
  ensures
    pts_to s #p (Seq.slice v 0 (SZ.v i)) **
    pts_to s' #p (Seq.slice v (SZ.v i) (Seq.length v)) **
    pure (adjacent s (SZ.v i) s')
{
    unfold pts_to s #p v;
    A.pts_to_range_prop s.base;
    let s' = {
        base = s.base;
        offset = SZ.add s.offset i;
    };
    A.pts_to_range_split s.base _ (SZ.v s'.offset) _;
    with s1. assert A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1;
    rewrite
        (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1)
        as (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + Seq.length s1) #p s1);
    fold pts_to s #p s1;
    with s2. assert A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2;
    rewrite
        (A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2)
        as (A.pts_to_range s'.base (SZ.v s'.offset) (SZ.v s'.offset + Seq.length s2) #p s2);
    fold pts_to s' #p s2;
    s'
}

ghost fn ghost_split (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns s' : erased (ptr t)
  ensures
    pts_to s #p (Seq.slice v 0 (SZ.v i)) **
    pts_to (reveal s') #p (Seq.slice v (SZ.v i) (Seq.length v)) **
    pure (adjacent s (SZ.v i) s')
{
    unfold pts_to s #p v;
    A.pts_to_range_prop s.base;
    let s' = {
        base = s.base;
        offset = SZ.add s.offset i;
    };
    A.pts_to_range_split s.base _ (SZ.v s'.offset) _;
    with s1. assert A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1;
    rewrite
        (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s'.offset) #p s1)
        as (A.pts_to_range s.base (SZ.v s.offset) (SZ.v s.offset + Seq.length s1) #p s1);
    fold pts_to s #p s1;
    with s2. assert A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2;
    rewrite
        (A.pts_to_range s.base (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2)
        as (A.pts_to_range s'.base (SZ.v s'.offset) (SZ.v s'.offset + Seq.length s2) #p s2);
    fold pts_to s' #p s2;
    s'
}


ghost
fn join (#t: Type) (s1: ptr t) (#p: perm) (#v1: Seq.seq t) (s2: ptr t) (#v2: Seq.seq t)
    requires pts_to s1 #p v1
    requires pts_to s2 #p v2
    requires pure (adjacent s1 (Seq.length v1) s2)
    ensures pts_to s1 #p (Seq.append v1 v2)
{
    unfold pts_to s1 #p v1;
    unfold pts_to s2 #p v2;
    rewrite (A.pts_to_range s2.base (SZ.v s2.offset) (SZ.v s2.offset + Seq.length v2) #p v2)
        as (A.pts_to_range s1.base (SZ.v s1.offset + Seq.length v1) (SZ.v s1.offset + Seq.length (Seq.append v1 v2)) #p v2);
    A.pts_to_range_join s1.base (SZ.v s1.offset) (SZ.v s1.offset + Seq.length v1) (SZ.v s1.offset + Seq.length (Seq.append v1 v2));
    fold pts_to s1 #p (Seq.append v1 v2)
}

fn memcpy
    (#t:Type0) (#p0:perm)
    (src:ptr t) (idx_src: SZ.t)
    (dst:ptr t) (idx_dst: SZ.t)
    (len: SZ.t)
    (#s0:Ghost.erased (Seq.seq t) { SZ.v idx_src + SZ.v len <= Seq.length s0 })
    (#s1:Ghost.erased (Seq.seq t) { SZ.v idx_dst + SZ.v len <= Seq.length s1 })
  requires pts_to src #p0 s0
  requires pts_to dst s1
  ensures pts_to src #p0 s0 **
    pts_to dst (Seq.slice s0 0 (SZ.v len) `Seq.append` Seq.slice s1 (SZ.v len) (Seq.length s1))
{
  let mut i = 0sz;
  while (SZ.lt !i len)
    invariant exists* s1' vi.
      R.pts_to i vi **
      pts_to src #p0 s0 **
      pts_to dst s1' **
      pure (SZ.lte vi len /\
        Seq.length s1' == Seq.length s1 /\
        forall (j:nat). j < Seq.length s1' ==>
          Seq.index s1' j == (if j < SZ.v vi then Seq.index s0 j else Seq.index s1 j))
  {
    let vi = !i;
    let x = src.(vi);
    dst.(vi) <- x;
    i := SZ.add vi 1sz;
  };
  with s1'. assert pts_to dst s1';
  assert pure (s1' `Seq.equal`
    (Seq.slice s0 0 (SZ.v len) `Seq.append` Seq.slice s1 (SZ.v len) (Seq.length s1)))
}
