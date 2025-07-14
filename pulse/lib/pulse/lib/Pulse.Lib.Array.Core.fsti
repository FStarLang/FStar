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
open FStar.Tactics.V2
open Pulse.Lib.Core
open Pulse.Main
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq

[@@erasable] val base_t : Type0

inline_for_extraction
val array ([@@@strictly_positive] a:Type u#0) : Type u#0

val length (#a:Type u#0) (x:array a) : Ghost nat (requires True) (ensures SZ.fits)
val base_of #t (a: array t) : base_t
val offset_of #t (a: array t) : GTot nat

type elseq (a:Type) (l:SZ.t) = s:erased (Seq.seq a) { Seq.length s == SZ.v l }

inline_for_extraction
type larray t (n:nat) = a:array t { length a == n }

val is_full_array (#a:Type u#0) (x:array a) : prop

inline_for_extraction
val null #a : array a
inline_for_extraction
val is_null #a (r: array a) : b:bool {b <==> r == null #a}

val pts_to_mask #t ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop

val pts_to_mask_timeless (#a:Type) (x:array a) (p:perm) (s:Seq.seq a) mask
  : Lemma (timeless (pts_to_mask x #p s mask))
          [SMTPat (timeless (pts_to_mask x #p s mask))]

ghost
fn pts_to_mask_len #t (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)

ghost
fn pts_to_mask_not_null #a #p (r:array a) (#v:Seq.seq a) #mask
  preserves pts_to_mask r #p v mask
  ensures pure (not (is_null r))

ghost fn mask_vext #t (arr: array t) #f #v v' #mask
  requires pts_to_mask arr #f v mask
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask

ghost fn mask_mext #t (arr: array t) #f #v #mask (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  ensures pts_to_mask arr #f v mask'

ghost fn mask_ext #t (arr: array t) #f #v #mask v' (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask'

ghost
fn mask_share #a (arr:array a) (#s: Seq.seq a) #p #mask
  requires pts_to_mask arr #p s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask

[@@allow_ambiguous]
ghost fn mask_gather #t (arr: array t) #p1 #p2 #s1 #s2 #mask1 #mask2
  requires pts_to_mask arr #p1 s1 mask1
  requires pts_to_mask arr #p2 s2 mask2
  requires pure (forall i. mask1 i <==> mask2 i)
  ensures exists* (v: Seq.seq t). pts_to_mask arr #(p1 +. p2) v mask1 **
    pure ((Seq.length v == Seq.length s1 /\ Seq.length v == Seq.length s2) /\
      (forall (i: nat). i < Seq.length v /\ mask1 i ==> Seq.index v i == Seq.index s1 i /\ Seq.index v i == Seq.index s2 i))

// We need to give names to these combinators, otherwise unfold can't
// distinguish them when we have multiple pts_to_mask resources.
include Pulse.Lib.HigherArray {mask_isect, mask_diff}

ghost fn split_mask #t (arr: array t) #f #v #mask (pred: nat -> prop)
  requires pts_to_mask arr #f v mask
  ensures pts_to_mask arr #f v (mask_isect mask pred)
  ensures pts_to_mask arr #f v (mask_diff mask pred)

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

[@@allow_ambiguous]
ghost fn join_mask' #t (arr: array t) #f (#v: erased (Seq.seq t)) #mask1 #mask2
  requires pts_to_mask arr #f v mask1
  requires pts_to_mask arr #f v mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i)

[@@allow_ambiguous]
ghost
fn pts_to_mask_injective_eq #a #p0 #p1 #s0 #s1 #mask0 #mask1 (arr:array a)
  preserves pts_to_mask arr #p0 s0 mask0
  preserves pts_to_mask arr #p1 s1 mask1
  ensures pure (Seq.length s0 == Seq.length s1 /\
    (forall (i: nat). i < Seq.length s0 /\ mask0 i /\ mask1 i ==>
      Seq.index s0 i == Seq.index s1 i))

inline_for_extraction
fn mask_read #t (a: array t) (i: SZ.t) #p (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  preserves pts_to_mask a #p s mask
  requires pure (mask (SZ.v i))
  returns res: t
  ensures pure (res == Seq.index s (SZ.v i))

inline_for_extraction
fn mask_write #t (a: array t) (i: SZ.t) (v: t) (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  requires pts_to_mask a s mask
  requires pure (mask (SZ.v i))
  ensures pts_to_mask a (Seq.upd s (SZ.v i) v) mask

val gsub #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr }) : GTot (array t)

ghost fn gsub_intro #t (arr: array t) #f #mask (i j: nat) (#v: erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
  requires pts_to_mask arr #f v mask
  requires pure (forall (k: nat). mask k /\ k < Seq.length v ==> i <= k /\ k < j)
  returns _: squash (length arr == Seq.length v)
  ensures pts_to_mask (gsub arr i j) #f (Seq.slice v i j) (fun k -> mask (k + i))

ghost fn gsub_elim #t (arr: array t) #f (#mask: nat->prop) (i j: nat)
    (#v: erased (Seq.seq t) { i <= j /\ j <= length arr })
  requires pts_to_mask (gsub arr i j) #f v mask
  returns _: squash (j - i == Seq.length v)
  ensures exists* (v': Seq.seq t).
    pts_to_mask arr #f v' (fun k -> i <= k /\ k < j /\ mask (k - i)) **
    pure (Seq.length v' == length arr /\ (forall (k:nat). k < j - i ==> Seq.index v k == Seq.index v' (k + i)))

inline_for_extraction
unobservable
fn sub #t (arr: array t) #f #mask (i: SZ.t) (j: SZ.t)
    (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length (reveal v) })
  requires pts_to_mask arr #f v mask
  returns sub: (sub: array t { length arr == Seq.length (reveal v) })
  ensures rewrites_to sub (gsub arr (SZ.v i) (SZ.v j))
  ensures pts_to_mask sub #f (Seq.slice v (SZ.v i) (SZ.v j)) (fun k -> mask (k + SZ.v i))
  ensures pts_to_mask arr #f v (fun k -> mask k /\ ~(SZ.v i <= k /\ k < SZ.v j))

[@@allow_ambiguous]
ghost fn return_sub #t (arr: array t) #f (#v #vsub: erased (Seq.seq t)) #mask #masksub (#i: nat) (#j: nat { i <= j /\ j <= length arr })
  requires pts_to_mask arr #f v mask
  requires pts_to_mask (gsub arr i j) #f vsub masksub
  requires pure (forall (k: nat). i <= k /\ k < j ==> ~(mask k))
  ensures exists* v'. pts_to_mask arr #f v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)))
    ** pure (Seq.length v == Seq.length v' /\ i + Seq.length vsub == j /\ j <= Seq.length v /\
      (forall (k: nat). k < Seq.length v' ==>
      Seq.index v' k == (if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k)))

val pts_to (#a:Type u#0) ([@@@mkey]x:array a) (#[exact (`1.0R)] p:perm) (s: Seq.seq a) : slprop

[@@pulse_unfold]
instance has_pts_to_array (a:Type u#0) : has_pts_to (array a) (Seq.seq a) = {
  pts_to = pts_to;
}
[@@pulse_unfold]
instance has_pts_to_larray (a:Type u#0) (n : nat) : has_pts_to (larray a n) (Seq.seq a) = {
  pts_to = pts_to;
}

ghost fn to_mask #t (arr: array t) #f #v
  requires arr |-> Frac f v
  ensures pts_to_mask arr #f v (fun _ -> True)

ghost fn from_mask #t (arr: array t) #f #v #mask
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> mask i)
  ensures arr |-> Frac f v

val pts_to_timeless (#a:Type) (x:array a) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to x #p s))
          [SMTPat (timeless (pts_to x #p s))]

ghost
fn pts_to_len (#t:Type0) (a:array t) (#p:perm) (#x:Seq.seq t)
  requires pts_to a #p x
  ensures  pts_to a #p x ** pure (length a == Seq.length x)

[@@deprecated "Array.Core.alloc is meant to be generated by the Pulse elaborator, not called directly; use Vec.alloc instead"]
inline_for_extraction
fn alloc (#elt: Type) (x: elt) (n: SZ.t)
  requires emp
  returns  a : array elt
  ensures  pts_to a (Seq.create (SZ.v n) x) **
           pure (length a == SZ.v n /\ is_full_array a)

(* Written x.(i) *)
inline_for_extraction
fn op_Array_Access
  (#t: Type) (a: array t) (i: SZ.t)
  (#p: perm) (#s: erased (Seq.seq t){SZ.v i < Seq.length s})
  preserves pts_to a #p s
  returns  res : t
  ensures  rewrites_to res (Seq.index s (SZ.v i))

(* Written a.(i) <- v *)
inline_for_extraction
fn op_Array_Assignment
        (#t: Type)
        (a: array t)
        (i: SZ.t)
        (v: t)
        (#s: erased (Seq.seq t) {SZ.v i < Seq.length s})
  requires pts_to a s
  ensures  pts_to a (Seq.upd s (SZ.v i) v)

[@@deprecated "Array.Core.free is not meant to be called directly; use Vec.free instead"]
inline_for_extraction
fn free (#elt: Type) (a: array elt) (#s: erased (Seq.seq elt))
  requires pts_to a s ** pure (is_full_array a)
  ensures emp

ghost
fn share
  (#a:Type)
  (arr:array a)
  (#s:erased (Seq.seq a))
  (#p:perm)
  requires pts_to arr #p s
  ensures  pts_to arr #(p /. 2.0R) s ** pts_to arr #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn gather
  (#a:Type)
  (arr:array a)
  (#s0 #s1:erased (Seq.seq a))
  (#p0 #p1:perm)
  requires pts_to arr #p0 s0 ** pts_to arr #p1 s1
  ensures  pts_to arr #(p0 +. p1) s0 ** pure (s0 == s1)

val pts_to_range
  (#a:Type u#0)
  ([@@@mkey] x:array a)
  ([@@@mkey] i : nat)
  (j : nat)
  (* ^NOTE: only using the start as matching key. *)
  (#[exact (`1.0R)] p:perm)
  (s: Seq.seq a) : slprop

val pts_to_range_timeless (#a:Type) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to_range x i j #p s))
          [SMTPat (timeless (pts_to_range x i j #p s))]

let is_subarray #elt (a: array elt) (i j: nat) (b: array elt) : prop =
  base_of b == base_of a /\
  offset_of b == offset_of a + i /\
  i + length b == j /\
  j <= length a

ghost
fn pts_to_range_prop
  (#elt: Type0) (a: array elt) (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
  requires pts_to_range a i j #p s
  ensures  pts_to_range a i j #p s
           ** pure ( (i <= j /\ j <= length a /\ Seq.length s == j - i))

ghost
fn pts_to_range_intro
  (#elt: Type0) (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to a #p s
  ensures  pts_to_range a 0 (length a) #p s

ghost
fn pts_to_range_elim
  (#elt: Type0) (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to_range a 0 (length a) #p s
  ensures  pts_to a #p s

ghost
fn pts_to_range_split
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
 requires pts_to_range a i j #p s ** pure (i <= m /\ m <= j)
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

ghost
fn pts_to_range_join
  (#elt: Type0)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
  requires pts_to_range a i m #p s1 ** pts_to_range a m j #p s2
  ensures  pts_to_range a i j #p (s1 `Seq.append` s2)

inline_for_extraction
fn pts_to_range_index
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (#l: erased nat{l <= SZ.v i})
  (#r: erased nat{SZ.v i < r})
  (#s: erased (Seq.seq t))
  (#p: perm)
  requires pts_to_range a l r #p s
  returns  res : t
  ensures pts_to_range a l r #p s **
          pure (eq2 #int (Seq.length s) (r - l) /\
                res == Seq.index s (SZ.v i - l))

inline_for_extraction
fn pts_to_range_upd
  (#t: Type)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: erased nat{l <= SZ.v i})
  (#r: erased nat{SZ.v i < r})
  (#s0: erased (Seq.seq t))
  requires pts_to_range a l r s0
  ensures
    exists* s.
      pts_to_range a l r s **
      pure(
        eq2 #int (Seq.length s0) (r - l) /\
        s == Seq.upd s0 (SZ.v i - l) v
      )

ghost
fn pts_to_range_share
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
  requires pts_to_range arr l r #p s
  ensures  pts_to_range arr l r #(p /. 2.0R) s **
           pts_to_range arr l r #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn pts_to_range_gather
  (#a:Type)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
  requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1
  ensures  pts_to_range arr l r #(p0 +. p1) s0 **
           pure (s0 == s1)

(* Called by elaboration, not to be used directly. *)
val with_local
  (#a:Type0)
  (init:a)
  (len:SZ.t)
  (#pre:slprop)
  (ret_t:Type)
  (#post:ret_t -> slprop)
  (body:(arr:array a) -> stt ret_t (pre **
                                    (pts_to arr (Seq.create (SZ.v len) init) **
                                     (pure (is_full_array arr) **
                                      pure (length arr == SZ.v len))))
                                   (fun r -> post r ** (exists* v. pts_to arr v)))
  : stt ret_t pre post
