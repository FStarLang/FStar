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

noeq
type base_t ([@@@strictly_positive] a: Type0) =
| Null
| Ref of R.ref a
| Array of A.array a

let base_length
  (#t: Type)
  (b: base_t t)
: GTot nat
= match b with
  | Null -> 0
  | Ref _ -> 1
  | Array a -> A.length a

noeq
type ptr t = {
    base: base_t t;
    offset: (offset: SZ.t { SZ.v offset <= base_length base})
}

let base a = a.base
let offset a = SZ.v a.offset

let null #t = { base = Null; offset = 0sz }

let g_is_null p = Null? p.base

let v_is_empty (#t: Type) (s: ptr t) (v: Seq.seq t) : Tot slprop =
  pure (offset s <= 1 /\ Seq.length v == 0)

let pts_to s #p v =
  match s.base with
  | Array a -> A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v
  | Ref a -> if offset s = 0 && Seq.length v = 1 then R.pts_to a #p (Seq.index v 0) else v_is_empty s v
  | Null -> pure False

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
  if Null? s.base {
    rewrite (pts_to s #p v) as (pure False);
    rewrite emp as (pts_to s #p v)
  } else {
    ()
  }
}

ghost fn pts_to_length
  (#t:Type)
  (s:ptr t)
  (#p:perm)
  (#v : Seq.seq t)
requires
  (pts_to s #p v)
ensures
  (pts_to s #p v ** pure (offset s + Seq.length v <= base_length (base s)))
{
  pts_to_not_null s;
  if (Array? s.base) {
    let Array a = s.base;
    rewrite pts_to s #p v
      as A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v;
    A.pts_to_range_prop _;
    rewrite A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v
      as pts_to s #p v;
  } else if (s.offset = 0sz && Seq.length v = 1) {
    ()
  } else {
    let Ref a = s.base;
    rewrite (pts_to s #p v) as (v_is_empty s v);
    unfold (v_is_empty s v);
    fold (v_is_empty s v);
    rewrite (v_is_empty s v) as (pts_to s #p v)
  }
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
  Null? s.base
}

let pts_to_timeless x p s = ()

let is_from_array s sz a =
    pure (sz == A.length a /\ s.base == Array a)

fn from_array (#t: Type) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
    requires A.pts_to a #p v
    returns s: ptr t
    ensures pts_to s #p v ** is_from_array s (Seq.length v) a
{
    A.pts_to_len a;
    let res = {
        base = Array a;
        offset = 0sz;
    };
    fold (is_from_array res (Seq.length v) a);
    A.pts_to_range_intro a p v;
    rewrite (A.pts_to_range a 0 (A.length a) #p v)
        as (pts_to res #p v);
    res
}

ghost
fn to_array (#t: Type) (s: ptr t) (a: array t) (#p: perm) (#v: Seq.seq t)
    requires pts_to s #p v ** is_from_array s (Seq.length v) a
    ensures A.pts_to a #p v
{
    unfold is_from_array s (Seq.length v) a;
    rewrite (pts_to s #p v)
      as (A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v); 
    A.pts_to_range_prop a;
    rewrite (A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v)
        as (A.pts_to_range a 0 (A.length a) #p v);
    A.pts_to_range_elim a _ _;
}

let is_from_ref s a =
    pure (s.base == Ref a)

fn from_ref (#t: Type) (a: R.ref t) (#p: perm) (#v: Ghost.erased (t))
    requires R.pts_to a #p v
    returns s: ptr t
    ensures pts_to s #p (Seq.create 1 (Ghost.reveal v)) ** is_from_ref s a
{
    let res = {
        base = Ref a;
        offset = 0sz;
    };
    fold (is_from_ref res a);
    rewrite (R.pts_to a #p v)
        as (pts_to res #p (Seq.create 1 (Ghost.reveal v)));
    res
}

ghost
fn to_ref (#t: Type) : to_ref_t t
= (s: ptr t) (a: ref t) (#p: perm) (#v: Seq.seq t)
{
    pts_to_length s;
    unfold is_from_ref s a;
    rewrite (pts_to s #p v)
      as (R.pts_to a #p (Seq.index v 0))
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
    pts_to_not_null a;
  if (Array? a.base) {
    let Array ar = a.base;    
    rewrite (pts_to a #p s)
      as (A.pts_to_range ar (SZ.v a.offset) (SZ.v a.offset + Seq.length s) #p s); 
    A.pts_to_range_prop ar;
    let res = A.pts_to_range_index ar (SZ.add a.offset i);
    rewrite (A.pts_to_range ar (SZ.v a.offset) (SZ.v a.offset + Seq.length s) #p s)
      as (pts_to a #p s);
    res
  } else {
    pts_to_length a;
    let Ref r = a.base;
    rewrite (pts_to a #p s) as (R.pts_to r #p (Seq.index s 0));
    let res = !r;
    rewrite (R.pts_to r #p (Seq.index s 0)) as (pts_to a #p s);
    res
  }
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
    pts_to_not_null a;
  if (Array? a.base) {
    let Array ar = a.base;
    rewrite (pts_to a s)
      as (A.pts_to_range ar (SZ.v a.offset) (SZ.v a.offset + Seq.length s) s);
    A.pts_to_range_prop ar;
    let res = A.pts_to_range_upd ar (SZ.add a.offset i) v;
    rewrite
      A.pts_to_range ar (SZ.v a.offset) (SZ.v a.offset + Seq.length s) (Seq.upd s (SZ.v i) v)
    as
      pts_to a (Seq.upd s (SZ.v i) v);
    ();
  } else {
    pts_to_length a;
    let Ref r = a.base;
    rewrite (pts_to a s) as (R.pts_to r (Seq.index s 0));
    r := v;
    rewrite (R.pts_to r v) as (pts_to a (Seq.upd s (SZ.v i) v));
  }
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
    pts_to_not_null arr;
  if (Array? arr.base) {
    let Array a = arr.base;
    rewrite (pts_to arr #p s)
      as (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s) #p s);
    A.pts_to_range_share a;
    rewrite (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s) #(p /. 2.0R) s)
      as (pts_to arr #(p /. 2.0R) s);
    rewrite (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s) #(p /. 2.0R) s)
      as (pts_to arr #(p /. 2.0R) s);
  } else {
    let test = (offset arr = 0 && Seq.length (Ghost.reveal s) = 1);
    if (test) {
      let Ref a = arr.base;
      rewrite (pts_to arr #p s)
        as (R.pts_to a #p (Seq.index s 0));
      R.share a;
      rewrite (R.pts_to a #(p /. 2.0R) (Seq.index s 0))
        as (pts_to arr #(p /. 2.0R) s);
      rewrite (R.pts_to a #(p /. 2.0R) (Seq.index s 0))
        as (pts_to arr #(p /. 2.0R) s);
    } else {
      rewrite (pts_to arr #p s)
        as (v_is_empty arr s);
      unfold (v_is_empty arr s);
      fold (v_is_empty arr s);
      rewrite (v_is_empty arr s)
        as (pts_to arr #(p /. 2.0R) s);
      fold (v_is_empty arr s);
      rewrite (v_is_empty arr s)
        as (pts_to arr #(p /. 2.0R) s);
    }
  }
}

ghost
fn gather
  (#a:Type)
  (arr:ptr a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0 ** pts_to arr #p1 s1 ** pure (Seq.length s0 == Seq.length s1)
  ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
    pts_to_not_null arr #p0;
  if (Array? arr.base) {
    let Array a = arr.base;
    rewrite (pts_to arr #p0 s0)
      as (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s0) #(p0) s0);
    rewrite pts_to arr #p1 s1
      as (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s0) #(p1) s1);
    A.pts_to_range_gather a #_ #_ #s0 #s1 #p0 #p1;
    rewrite (A.pts_to_range a (SZ.v arr.offset) (SZ.v arr.offset + Seq.length s0) #(p0 +. p1) s0)
      as pts_to arr #(p0 +. p1) s0
  } else {
    let test = (offset arr = 0 && Seq.length (Ghost.reveal s0) = 1);
    if (test) {
      let Ref a = arr.base;
      rewrite (pts_to arr #p0 s0)
        as (R.pts_to a #p0 (Seq.index s0 0));
      rewrite (pts_to arr #p1 s1)
        as (R.pts_to a #p1 (Seq.index s1 0));
      R.gather a;
      assert (pure (Seq.equal s0 s1));
      rewrite (R.pts_to a #(p0 +. p1) (Seq.index s0 0))
        as (pts_to arr #(p0 +. p1) s0);
    } else {
      rewrite (pts_to arr #p0 s0)
        as (v_is_empty arr s0);
      unfold (v_is_empty arr s0);
      rewrite (pts_to arr #p1 s1)
        as (v_is_empty arr s1);
      unfold (v_is_empty arr s1);
      assert (pure (Seq.equal s0 s1));
      fold (v_is_empty arr s0);
      rewrite (v_is_empty arr s0)
        as (pts_to arr #(p0 +. p1) s0);
    }
  }
}

let shift
  (#t: Type) (s: ptr t) (i: SZ.t { SZ.v s.offset + SZ.v i <= base_length s.base })
: Tot (ptr t)
= 
  {
        base = s.base;
        offset = SZ.add s.offset i;
  }

ghost fn ghost_shift (#t: Type) (s: ptr t) (#p: perm) (i: SZ.t)
    (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns res: squash (SZ.v s.offset + SZ.v i <= base_length s.base)
  ensures
    pts_to s #p (Seq.slice v 0 (SZ.v i)) **
    pts_to (shift s i) #p (Seq.slice v (SZ.v i) (Seq.length v))
{
    pts_to_not_null s;
  if (Array? s.base) {
    let Array a = s.base;
    rewrite pts_to s #p v
      as A.pts_to_range a (SZ.v s.offset) (SZ.v s.offset + Seq.length v) #p v;
    A.pts_to_range_prop a;
    let s' = shift s i;
    A.pts_to_range_split a _ (SZ.v s'.offset) _;
    with s1. assert A.pts_to_range a (SZ.v s.offset) (SZ.v s'.offset) #p s1;
    rewrite
        (A.pts_to_range a (SZ.v s.offset) (SZ.v s'.offset) #p s1)
        as pts_to s #p s1;
    with s2. assert A.pts_to_range a (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2;
    rewrite
        (A.pts_to_range a (SZ.v s'.offset) (SZ.v s.offset + Seq.length v) #p s2)
        as pts_to (shift s i) #p s2;
    ()
  } else {
    pts_to_length s;
    let res : squash (SZ.v s.offset + SZ.v i <= base_length s.base) = ();
    let Ref a = s.base;
    let test = (SZ.v i + 1 <= Seq.length v);
    if (test) {
      assert (pure (Seq.equal v (Seq.slice v (SZ.v i) (Seq.length v))));
      rewrite pts_to s #p v
        as pts_to (shift s i) #p (Seq.slice v (SZ.v i) (Seq.length v));
      fold (v_is_empty s (Seq.slice v 0 (SZ.v i)));
      rewrite (v_is_empty s (Seq.slice v 0 (SZ.v i)))
        as pts_to s #p (Seq.slice v 0 (SZ.v i));
    } else {
      assert (pure (Seq.equal v (Seq.slice v 0 (SZ.v i))));
      rewrite pts_to s #p v
        as pts_to s #p (Seq.slice v 0 (SZ.v i));
      fold (v_is_empty s (Seq.slice v (SZ.v i) (Seq.length v)));
      rewrite (v_is_empty s (Seq.slice v (SZ.v i) (Seq.length v)))
        as pts_to (shift s i) #p (Seq.slice v (SZ.v i) (Seq.length v));
      res
    }
  }
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
    ghost_shift s i;
    shift s i
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
    ghost_shift s i;
    shift s i
}


ghost
fn join (#t: Type) (s1: ptr t) (#p: perm) (#v1: Seq.seq t) (s2: ptr t) (#v2: Seq.seq t)
    requires pts_to s1 #p v1 ** pts_to s2 #p v2 ** pure (adjacent s1 (Seq.length v1) s2)
    ensures pts_to s1 #p (Seq.append v1 v2)
{
    pts_to_not_null s1;
  if (Array? s1.base) {
    let Array a = s1.base;
    rewrite pts_to s1 #p v1
      as (A.pts_to_range a (SZ.v s1.offset) (SZ.v s1.offset + Seq.length v1) #p v1);
    rewrite pts_to s2 #p v2
        as (A.pts_to_range a (SZ.v s1.offset + Seq.length v1) (SZ.v s1.offset + Seq.length v1 + Seq.length v2) #p v2);
    A.pts_to_range_join a (SZ.v s1.offset) (SZ.v s1.offset + Seq.length v1) (SZ.v s1.offset + Seq.length v1 + Seq.length v2);
    rewrite (A.pts_to_range a (SZ.v s1.offset) (SZ.v s1.offset + Seq.length v1 + Seq.length v2) #p (Seq.append v1 v2))
    as pts_to s1 #p (Seq.append v1 v2)
  } else {
    pts_to_length s1;
    pts_to_length s2;
    if (Seq.length v2 = 0) {
      rewrite pts_to s2 #p v2 as v_is_empty s2 v2;
      unfold v_is_empty s2 v2;
      assert (pure (Seq.equal v1 (Seq.append v1 v2)));
      rewrite pts_to s1 #p v1 as pts_to s1 #p (Seq.append v1 v2);
    } else {
      let Ref a = s1.base;
      rewrite pts_to s1 #p v1 as v_is_empty s1 v1;
      unfold v_is_empty s1 v1;
      assert (pure (Seq.equal v2 (Seq.append v1 v2)));
      rewrite pts_to s2 #p v2 as pts_to s1 #p (Seq.append v1 v2);
    }
  }
}

fn memcpy
    (#t:Type0) (#p0:perm)
    (src:ptr t) (idx_src: SZ.t)
    (dst:ptr t) (idx_dst: SZ.t)
    (len: SZ.t)
    (#s0:Ghost.erased (Seq.seq t) { SZ.v idx_src + SZ.v len <= Seq.length s0 })
    (#s1:Ghost.erased (Seq.seq t) { SZ.v idx_dst + SZ.v len <= Seq.length s1 })
  requires pts_to src #p0 s0 ** pts_to dst s1
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
