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

module Pulse.Lib.Slice
#lang-pulse

module AP = Pulse.Lib.ArrayPtr

noeq
type slice t = {
    elt: AP.ptr t;
    len: SZ.t;
}

let len s = s.len

let pts_to #t s #p v =
    AP.pts_to s.elt #p v **
    pure (Seq.length v == SZ.v s.len)

let pts_to_is_slprop2 x p v = ()

ghost
fn pts_to_len (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t)
  requires pts_to s #p v
  ensures pts_to s #p v ** pure (Seq.length v == SZ.v (len s))
{
    unfold (pts_to s #p v);
    fold (pts_to s #p v)
}

let is_from_array a s =
  AP.is_from_array s.elt (SZ.v s.len) a

fn from_array (#t: Type) (a: array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  (alen: SZ.t { SZ.v alen == A.length a })
  requires A.pts_to a #p v
  returns s: (slice t)
  ensures 
    pts_to s #p v **
    is_from_array a s
{
    A.pts_to_len a;
    let ptr = AP.from_array a;
    let res : slice t = {
        elt = ptr;
        len = alen;
    };
    fold pts_to res #p v;
    fold is_from_array a res;
    res
}

ghost
fn to_array
    (#t: Type) (s: slice t) (#p: perm) (#v: Seq.seq t) (#a: array t)
requires    (pts_to s #p v ** is_from_array a s)
ensures    (A.pts_to a #p v)
{
    unfold (pts_to s #p v);
    unfold is_from_array a s;
    AP.to_array s.elt a
}

fn op_Array_Access
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
        requires
            pts_to a #p s
returns res : t
ensures
            pts_to a #p s **
            pure (res == Seq.index s (SZ.v i))
{
    unfold (pts_to a #p s);
    let res = AP.op_Array_Access a.elt i;
    fold (pts_to a #p s);
    res
}

fn op_Array_Assignment
        (#t: Type)
        (a: slice t)
        (i: SZ.t)
        (v: t)
        (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
        requires
            pts_to a s
        ensures
            pts_to a (Seq.upd s (SZ.v i) v)
{
    unfold (pts_to a s);
    AP.op_Array_Assignment a.elt i v;
    fold (pts_to a (Seq.upd s (SZ.v i) v))
}

ghost
fn share
  (#a:Type)
  (arr:slice a)
  (#s:Ghost.erased (Seq.seq a))
  (#p:perm)
requires
    pts_to arr #p s
ensures pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s
{
    unfold (pts_to arr #p s);
    AP.share arr.elt;
    fold (pts_to arr #(p /. 2.0R) s);
    fold (pts_to arr #(p /. 2.0R) s)
}

ghost
fn gather
  (#a:Type)
  (arr:slice a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
    unfold (pts_to arr #p0 s0);
    unfold (pts_to arr #p1 s1);
    AP.gather arr.elt;
    fold (pts_to arr #(p0 +. p1) s0)
}

let is_split #t s s1 s2 =
    pure (
        s1.elt == s.elt /\
        AP.adjacent s1.elt (SZ.v s1.len) s2.elt /\
        SZ.v s.len == SZ.v s1.len + SZ.v s2.len
    )

let is_split_is_slprop2 s s1 s2 = ()

fn split (#t: Type) (s: slice t) (#p: perm) (i: SZ.t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns res : slice_pair t
  ensures
    (let SlicePair s1 s2 = res in
    pts_to s1 #p (Seq.slice v 0 (SZ.v i)) **
    pts_to s2 #p (Seq.slice v (SZ.v i) (Seq.length v)) **
    is_split s s1 s2)
{
    unfold (pts_to s #p v);
    Seq.lemma_split v (SZ.v i);
    let elt' = AP.split s.elt #p #v i;
    let s1 = {
        elt = s.elt;
        len = i;
    };
    fold pts_to s1 #p (Seq.slice v 0 (SZ.v i));
    let s2 = {
        elt = elt';
        len = s.len `SZ.sub` i;
    };
    fold pts_to s2 #p (Seq.slice v (SZ.v i) (Seq.length v));
    fold (is_split s s1 s2);
    (s1 `SlicePair` s2)
}

ghost
fn join (#t: Type) (s1: slice t) (#p: perm) (#v1: Seq.seq t) (s2: slice t) (#v2: Seq.seq t) (s: slice t)
    requires pts_to s1 #p v1 ** pts_to s2 #p v2 ** is_split s s1 s2
    ensures pts_to s #p (Seq.append v1 v2)
{
    unfold (is_split s s1 s2);
    unfold (pts_to s1 #p v1);
    unfold (pts_to s2 #p v2);
    AP.join s1.elt s2.elt;
    fold (pts_to s #p (Seq.append v1 v2))
}

fn copy
  (#t: Type) (dst: slice t) (#p: perm) (src: slice t) (#v: Ghost.erased (Seq.seq t))
requires
  (exists* v_dst . pts_to dst v_dst ** pts_to src #p v ** pure (len src == len dst))
ensures
  (pts_to dst v ** pts_to src #p v)
{
  with v_dst . assert (pts_to dst v_dst);
  unfold (pts_to dst v_dst);
  unfold (pts_to src #p v);
  AP.blit src.elt 0sz dst.elt 0sz src.len;
  fold (pts_to src #p v);
  fold (pts_to dst v)
}
