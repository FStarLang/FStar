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

module Pulse.Lib.Array.Core
#lang-pulse
open Pulse.Main
open Pulse.Lib.Core
module H = Pulse.Lib.HigherArray
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U = Pulse.Lib.Raise

let base_t = H.base_t
inline_for_extraction
let array a = H.array (U.raise_t a)
let length #a x = H.length x
let base_of x = H.base_of x
let offset_of x = H.offset_of x
let is_full_array #a x = H.is_full_array x
let raise_seq (#a:Type0) (x:FStar.Seq.seq a)
  : FStar.Seq.seq (U.raise_t u#0 u#1 a)
  = FStar.Seq.map_seq U.raise_val x
let map_seq_len #a #b (x:FStar.Seq.seq a) (f:a -> b)
: Lemma (ensures Seq.length (Seq.map_seq f x) ==  Seq.length x)
        [SMTPat (Seq.length (Seq.map_seq f x))]
= FStar.Seq.map_seq_len f x
let map_seq_index #a #b (x:FStar.Seq.seq a) (f:a -> b) (i:nat { i < Seq.length x })
: Lemma (ensures Seq.index (Seq.map_seq f x) i == f (Seq.index x i))
        [SMTPat (Seq.index (Seq.map_seq f x) i)]
= FStar.Seq.map_seq_index f x i

let raise_seq_len #a (x:FStar.Seq.seq a)
: Lemma (ensures Seq.length (raise_seq x) == Seq.length x)
        [SMTPat (Seq.length (raise_seq x))]
= ()//FStar.Seq.map_seq_len (U.raise_val u#0 u#1) x
let raise_seq_index #a (x:FStar.Seq.seq a) (i:nat)
: Lemma
  (requires i < Seq.length x)
  (ensures Seq.index (raise_seq x) i == U.raise_val u#0 u#1 (Seq.index x i))
  [SMTPat (Seq.index (raise_seq x) i)]
=  ()//FStar.Seq.map_seq_index (U.raise_val u#0 u#1) x i

let downgrade_seq #a (x: Seq.seq (U.raise_t u#0 u#1 a)) : Seq.seq a
= Seq.map_seq U.downgrade_val x
let raise_seq_downgrade_seq #a (x: Seq.seq (U.raise_t a))
: Lemma (raise_seq (downgrade_seq x) == x) [SMTPat (raise_seq (downgrade_seq x))]
= assert Seq.equal (raise_seq (downgrade_seq x)) x

let raise_seq_inv (#elt:Type0) (x:FStar.Seq.seq elt)
: Lemma (ensures downgrade_seq (raise_seq x)
                 `Seq.equal` x)
        [SMTPat (raise_seq x)]
= ()

let downgrade_seq_inv (#elt:Type0) (x:FStar.Seq.seq (U.raise_t u#0 u#1 elt))
: Lemma (ensures raise_seq (downgrade_seq x)
                 `Seq.equal` x)
        [SMTPat (downgrade_seq x)]
= ()

inline_for_extraction
let null #a : array a = H.null
inline_for_extraction
let is_null r = H.is_null r

[@@pulse_unfold]
let pts_to_mask #t ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop =
  H.pts_to_mask a #f (raise_seq v) mask

let pts_to_mask_timeless (#a:Type) (x:array a) (p:perm) (s:Seq.seq a) mask =
  ()

ghost
fn pts_to_mask_len #t (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)
{
  H.pts_to_mask_len a;
}

ghost
fn pts_to_mask_not_null #a #p (r:array a) (#v:Seq.seq a) #mask
  preserves pts_to_mask r #p v mask
  ensures pure (not (is_null r))
{
  H.pts_to_mask_not_null r;
}

ghost fn mask_vext #t (arr: array t) #f #v v' #mask
  requires pts_to_mask arr #f v mask
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask
{
  H.mask_vext arr (raise_seq v');
}

ghost fn mask_mext #t (arr: array t) #f #v #mask (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  ensures pts_to_mask arr #f v mask'
{
  H.mask_mext arr mask';
}

ghost fn mask_ext #t (arr: array t) #f #v #mask v' (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask'
{
  H.mask_ext arr (raise_seq v') mask';
}

ghost
fn mask_share #a (arr:array a) (#s: Seq.seq a) #p #mask
  requires pts_to_mask arr #p s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
{
  H.mask_share arr;
}

[@@allow_ambiguous]
ghost fn mask_gather #t (arr: array t) #p1 #p2 #s1 #s2 #mask1 #mask2
  requires pts_to_mask arr #p1 s1 mask1
  requires pts_to_mask arr #p2 s2 mask2
  requires pure (forall i. mask1 i <==> mask2 i)
  ensures exists* (v: Seq.seq t). pts_to_mask arr #(p1 +. p2) v mask1 **
    pure ((Seq.length v == Seq.length s1 /\ Seq.length v == Seq.length s2) /\
      (forall (i: nat). i < Seq.length v /\ mask1 i ==> Seq.index v i == Seq.index s1 i /\ Seq.index v i == Seq.index s2 i))
{
  H.mask_gather arr;
  H.mask_mext arr mask1;
  with v. assert H.pts_to_mask arr #(p1 +. p2) v mask1;
  fold pts_to_mask arr #(p1 +. p2) (downgrade_seq v) mask1;
}

ghost fn split_mask #t (arr: array t) #f #v #mask (pred: nat -> prop)
  requires pts_to_mask arr #f v mask
  ensures pts_to_mask arr #f v (mask_isect mask pred)
  ensures pts_to_mask arr #f v (mask_diff mask pred)
{
  H.split_mask arr pred;
}

[@@allow_ambiguous]
ghost fn join_mask #t (arr: array t) #f #v1 #v2 #mask1 #mask2
  requires pts_to_mask arr #f v1 mask1
  requires pts_to_mask arr #f v2 mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures exists* (v: Seq.seq t).
    pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i) **
    pure (Seq.length v == Seq.length v1 /\ Seq.length v == Seq.length v2 /\
      (forall (i: nat). i < Seq.length v ==>
        (mask1 i ==> Seq.index v i == Seq.index v1 i) /\
        (mask2 i ==> Seq.index v i == Seq.index v2 i)))
{
  H.join_mask arr #f #_ #_ #mask1 #mask2;
  with v. assert H.pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i);
  fold pts_to_mask arr #f (downgrade_seq v) (fun i -> mask1 i \/ mask2 i);
}

[@@allow_ambiguous]
ghost fn join_mask' #t (arr: array t) #f (#v: erased (Seq.seq t)) #mask1 #mask2
  requires pts_to_mask arr #f v mask1
  requires pts_to_mask arr #f v mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i)
{
  H.join_mask' arr #_ #_ #mask1 #mask2;
}

[@@allow_ambiguous]
ghost
fn pts_to_mask_injective_eq #a #p0 #p1 #s0 #s1 #mask0 #mask1 (arr:array a)
  preserves pts_to_mask arr #p0 s0 mask0
  preserves pts_to_mask arr #p1 s1 mask1
  ensures pure (Seq.length s0 == Seq.length s1 /\
    (forall (i: nat). i < Seq.length s0 /\ mask0 i /\ mask1 i ==>
      Seq.index s0 i == Seq.index s1 i))
{
  H.pts_to_mask_injective_eq arr;
}

inline_for_extraction
fn mask_read #t (a: array t) (i: SZ.t) #p (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  preserves pts_to_mask a #p s mask
  requires pure (mask (SZ.v i))
  returns res: t
  ensures pure (res == Seq.index s (SZ.v i))
{
  U.downgrade_val (H.mask_read a i)
}

inline_for_extraction
fn mask_write #t (a: array t) (i: SZ.t) (v: t) (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  requires pts_to_mask a s mask
  requires pure (mask (SZ.v i))
  ensures pts_to_mask a (Seq.upd s (SZ.v i) v) mask
{
  H.mask_write a i (U.raise_val v);
  with s'. assert H.pts_to_mask a s' mask;
  assert pure (Seq.equal s' (raise_seq (Seq.upd s (SZ.v i) v)));
}

let gsub #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr }) : GTot (array t) =
  H.gsub arr i j

ghost fn gsub_intro #t (arr: array t) #f #mask (i j: nat) (#v: erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
  requires pts_to_mask arr #f v mask
  requires pure (forall (k: nat). mask k ==> i <= k /\ k < j)
  returns _: squash (length arr == Seq.length v)
  ensures pts_to_mask (gsub arr i j) #f (Seq.slice v i j) (fun k -> mask (k + i))
{
  H.gsub_intro arr i j;
  with v'. assert H.pts_to_mask (gsub arr i j) #f v' (fun k -> mask (k + i));
  assert pure (Seq.equal v' (raise_seq (Seq.slice v i j)));
}

ghost fn gsub_elim #t (arr: array t) #f (#mask: nat->prop) (i j: nat)
    (#v: erased (Seq.seq t) { i <= j /\ j <= length arr })
  requires pts_to_mask (gsub arr i j) #f v mask
  returns _: squash (j - i == Seq.length v)
  ensures exists* v'.
    pts_to_mask arr #f v' (fun k -> i <= k /\ k < j /\ mask (k - i)) **
    pure (Seq.length v' == length arr /\ (forall (k:nat). k < j - i ==> Seq.index v k == Seq.index v' (k + i)))
{
  H.gsub_elim arr i j;
  with v' mask'. assert H.pts_to_mask arr #f v' mask';
  assert pts_to_mask arr #f (downgrade_seq v') mask';
}

inline_for_extraction
unobservable
fn sub #t (arr: array t) #f #mask (i: SZ.t) (j: SZ.t)
    (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length (reveal v) })
  requires pts_to_mask arr #f v mask
  returns sub: (sub: array t { length arr == Seq.length (reveal v) })
  ensures rewrites_to sub (gsub arr (SZ.v i) (SZ.v j))
  ensures pts_to_mask sub #f (Seq.slice v (SZ.v i) (SZ.v j)) (fun k -> mask (k + SZ.v i))
  ensures pts_to_mask arr #f v (fun k -> mask k /\ ~(SZ.v i <= k /\ k < SZ.v j))
{
  let sub = H.sub arr i j #(raise_seq v);
  with v' mask'. assert H.pts_to_mask sub #f v' mask';
  assert pure (Seq.equal v' (raise_seq (Seq.slice v (SZ.v i) (SZ.v j))));
  sub
}

[@@allow_ambiguous]
ghost fn return_sub #t (arr: array t) #f (#v #vsub: erased (Seq.seq t)) #mask #masksub (#i: nat) (#j: nat { i <= j /\ j <= length arr })
  requires pts_to_mask arr #f v mask
  requires pts_to_mask (gsub arr i j) #f vsub masksub
  requires pure (forall (k: nat). i <= k /\ k < j ==> ~(mask k))
  ensures exists* v'. pts_to_mask arr #f v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)))
    ** pure (Seq.length v == Seq.length v' /\ i + Seq.length vsub == j /\ j <= Seq.length v /\
      (forall (k: nat). k < Seq.length v' ==>
      Seq.index v' k == (if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k)))
{
  H.return_sub arr;
  with v' mask'. assert H.pts_to_mask arr #f v' mask';
  assert pts_to_mask arr #f (downgrade_seq v') mask';
}

let pts_to #a 
    (r:array a)
    (#[exact (`1.0R)] p:perm)
    (v:FStar.Seq.seq a)
= H.pts_to r #p (raise_seq v)

ghost fn to_mask #t (arr: array t) #f #v
  requires arr |-> Frac f v
  ensures pts_to_mask arr #f v (fun _ -> True)
{
  unfold pts_to arr #f v;
  H.to_mask arr;
}

ghost fn from_mask #t (arr: array t) #f #v #mask
  requires pts_to_mask arr #f v mask
  requires pure (forall i. mask i)
  ensures arr |-> Frac f v
{
  H.from_mask arr;
  fold pts_to arr #f v;
}

let pts_to_timeless _ _ _ = ()


ghost
fn pts_to_len (#t:Type) (a:array t) (#p:perm) (#x:FStar.Seq.seq t)
  requires pts_to a #p x
  ensures pts_to a #p x ** pure (length a == Seq.length x)
{
  unfold (pts_to a #p x);
  H.pts_to_len a;
  fold (pts_to a #p x)
}



inline_for_extraction
fn alloc (#elt:Type0) (x:elt) (n:SZ.t)
  requires emp
  returns a:array elt
ensures
  pts_to a (Seq.create (SZ.v n) x) **
  pure (length a == SZ.v n /\ is_full_array a)
{
  let a = H.alloc (U.raise_val x) n;
  with w. assert H.pts_to a w;
  assert pure (raise_seq (Seq.create (SZ.v n) x) `Seq.equal` w);
  fold (pts_to a (Seq.create (SZ.v n) x));
  a
}



inline_for_extraction
fn op_Array_Access
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (#p: perm)
    (#s: Ghost.erased (Seq.seq t){SZ.v i < Seq.length s})
preserves pts_to a #p s
returns res:t
ensures rewrites_to res (Seq.index s (SZ.v i))
{
  unfold (pts_to a #p s);
  let res = H.(a.(i));
  fold (pts_to a #p s);
  U.downgrade_val res
}



inline_for_extraction
fn op_Array_Assignment
    (#t: Type)
    (a: array t)
    (i: SZ.t)
    (v: t)
    (#s: Ghost.erased (Seq.seq t) {SZ.v i < Seq.length s})
requires
  pts_to a s
ensures
  pts_to a (Seq.upd s (SZ.v i) v)
{
  unfold (pts_to a s);
  H.(a.(i) <- U.raise_val v);
  with w. assert H.pts_to a w;
  assert pure (raise_seq (Seq.upd s (SZ.v i) v) `Seq.equal` w);
  fold (pts_to a (Seq.upd s (SZ.v i) v))
}


inline_for_extraction
fn free
    (#elt: Type)
    (a: array elt)
    (#s: Ghost.erased (Seq.seq elt))
requires
  pts_to a s ** pure (is_full_array a)
ensures
  emp
{
  unfold (pts_to a s);
  H.free a;
}


let share #a arr #s #p = H.share arr #(raise_seq s) #p


ghost
fn gather
  (#a:Type)
  (arr:array a)
  (#s0 #s1:Ghost.erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
  ensures pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold (pts_to arr #p0 s0);
  unfold (pts_to arr #p1 s1);
  H.gather arr #_ #_ #p0 #p1;
  fold (pts_to arr #(p0 +. p1) s0);
}


let pts_to_range
  (#a:Type)
  ([@@@mkey] x:array a)
  ([@@@mkey] i : nat)
  (j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a)
: slprop
= H.pts_to_range x i j #p (raise_seq s)

let pts_to_range_timeless _ _ _ _ _ = ()


ghost
fn pts_to_range_prop
  (#elt: Type)
  (a: array elt)
  (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
requires
  pts_to_range a i j #p s
ensures
  pts_to_range a i j #p s **
  pure (
      (i <= j /\ j <= length a /\ Seq.length s == (j - i))
  )
{
  unfold (pts_to_range a i j #p s);
  H.pts_to_range_prop a #i #j #p #(raise_seq s);
  fold (pts_to_range a i j #p s);
}

let pts_to_range_intro a p s = H.pts_to_range_intro a p (raise_seq s)
let pts_to_range_elim a p s = H.pts_to_range_elim a p (raise_seq s)


ghost
fn pts_to_range_split
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
  requires
    pts_to_range a i j #p s **
    pure (i <= m /\ m <= j)
  ensures
    exists* s1 s2.
      pts_to_range a i m #p s1 **
      pts_to_range a m j #p s2 **
      pure (
        i <= m /\ m <= j /\ j <= length a /\
        eq2 #int (Seq.length s) (j - i) /\
        s1 == Seq.slice s 0 (m - i) /\
        s2 == Seq.slice s (m - i) (Seq.length s) /\
        s == Seq.append s1 s2
      )
{
  unfold (pts_to_range a i j #p s);
  H.pts_to_range_split a i m j #p #(raise_seq s);
  with s1 s2. _;
  fold (pts_to_range a i m #p (downgrade_seq s1));
  fold (pts_to_range a m j #p (downgrade_seq s2));  
  let s1 = downgrade_seq s1;
  let s2 = downgrade_seq s2;
  assert pure ( 
    s1 `Seq.equal` Seq.slice s 0 (m - i) /\
    s2 `Seq.equal` Seq.slice s (m - i) (Seq.length s) /\
    s `Seq.equal` Seq.append s1 s2
  )
}



ghost
fn pts_to_range_join
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
requires
  pts_to_range a i m #p s1 **
  pts_to_range a m j #p s2
ensures
  pts_to_range a i j #p (s1 `Seq.append` s2)
{
  unfold (pts_to_range a i m #p s1);
  unfold (pts_to_range a m j #p s2);
  H.pts_to_range_join a i m j;
  assert pure (
    Seq.append (raise_seq s1) (raise_seq s2) `Seq.equal`
    raise_seq (s1 `Seq.append` s2)
  );
  fold (pts_to_range a i j #p (s1 `Seq.append` s2));
}



inline_for_extraction
fn pts_to_range_index
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
requires
  pts_to_range a l r #p s
  returns res:t
ensures 
  pts_to_range a l r #p s **
  pure (eq2 #int (Seq.length s) (r - l) /\
        res == Seq.index s (SZ.v i - l))
{
  unfold (pts_to_range a l r #p s);
  let res = H.pts_to_range_index a i;
  fold (pts_to_range a l r #p s);
  U.downgrade_val res
}



inline_for_extraction
fn pts_to_range_upd
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
  requires pts_to_range a l r s0
  ensures
    exists* s.
      pts_to_range a l r s **
      pure(
        eq2 #int (Seq.length s0) (r - l) /\
        s == Seq.upd s0 (SZ.v i - l) v
      )
{
  unfold (pts_to_range a l r s0);
  H.pts_to_range_upd a i (U.raise_val v);
  with s. _;
  assert (
    pure (
      s `Seq.equal` (raise_seq (Seq.upd s0 (SZ.v i - l) v))
    )
  );
  fold (pts_to_range a l r (Seq.upd s0 (SZ.v i - l) v));
}


let with_pre (pre:slprop) (#a:Type) (#post:a -> slprop)(m:stt a emp post)
: stt a pre (fun v -> pre ** post v)
= let m1 = frame_stt pre m in
  let pf_post : slprop_post_equiv (fun r -> post r ** pre) (fun r -> pre ** post r)
    = intro_slprop_post_equiv _ _ (fun r -> slprop_equiv_comm (post r) pre)
  in
  sub_stt _ _ (slprop_equiv_unit pre) pf_post m1


fn alloc_with_pre
    (#a:Type u#0)
    (init:a)
    (len:SZ.t)
    (pre:slprop)
  requires pre
  returns arr:array a
  ensures (pre **
         (pts_to arr (Seq.create (SZ.v len) init) ** (
          pure (is_full_array arr) **
          pure (length arr == SZ.v len)))) **
        pure (is_full_array arr)
{
  alloc init len
}



fn free_with_post (#a:Type u#0) (arr:array a) (post:slprop)
  requires (post ** (exists* v. pts_to arr v)) ** pure (is_full_array arr)
  ensures post
{
  free arr  
}

ghost
fn pts_to_range_share
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
      requires pts_to_range arr l r #p s
      ensures pts_to_range arr l r #(p /. 2.0R) s ** pts_to_range arr l r #(p /. 2.0R) s
{
  unfold (pts_to_range arr l r #p s);
  H.pts_to_range_share arr;
  fold (pts_to_range arr l r #(p /. 2.0R) s);
  fold (pts_to_range arr l r #(p /. 2.0R) s);
}

ghost
fn pts_to_range_gather
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
      requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1
      ensures pts_to_range arr l r #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold (pts_to_range arr l r #p0 s0);
  unfold (pts_to_range arr l r #p1 s1);
  H.pts_to_range_gather arr;
  fold (pts_to_range arr l r #(p0 +. p1) s0)
}

(* this is universe-polymorphic in ret_t; so can't define it in Pulse yet *)
let with_local
    (#a:Type u#0)
    (init:a)
    (len:SZ.t)
    (#pre:slprop)
    (ret_t:Type u#a)
    (#post:ret_t -> slprop) 
      (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) ** (
                                     pure (is_full_array arr) **
                                     pure (length arr == SZ.v len))))
                                   (fun r -> post r ** (exists* v. pts_to arr v)))

: stt ret_t pre post
= let m1 = alloc_with_pre init len pre in
   let body (arr:array a)
    : stt ret_t 
         ((pre ** 
          (pts_to arr (Seq.create (SZ.v len) init) ** (
           pure (is_full_array arr) **
           pure (length arr == SZ.v len)))) **
         pure (is_full_array arr))
        post
    = bind_stt
        (frame_stt (pure (is_full_array arr)) (body arr))
        (fun r ->
          bind_stt
            (free_with_post arr (post r)) 
            (fun _ -> return_stt_noeq r post))
  in
  bind_stt m1 body
