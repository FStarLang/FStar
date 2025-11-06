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

module Pulse.Lib.Array.Core
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Core
open Pulse.Main
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
open Pulse.Lib.SmallType

[@@erasable] val base_t : Type0

val array ([@@@unused] a:Type u#a) : Type u#0

val length (#a:Type) (x:array a) : Ghost nat (requires True) (ensures SZ.fits)
val base_of #t (a: array t) : base_t
val offset_of #t (a: array t) : GTot nat

type elseq (a:Type) (l:SZ.t) = s:erased (Seq.seq a) { Seq.length s == SZ.v l }

inline_for_extraction
type larray t (n:nat) = a:array t { length a == n }

val is_full_array (#a:Type) (x:array a) : prop

val null #a : array a
val is_null #a (r: array a) : b:bool {b <==> r == null #a}

val pts_to_mask (#t: Type u#a) ([@@@mkey] a: array t) (#[full_default()] f: perm) (v: erased (Seq.seq t)) (mask: nat -> prop) : slprop

val pts_to_mask_timeless (#a:Type u#a) (x:array a) (p:perm) (s:Seq.seq a) mask
  : Lemma (timeless (pts_to_mask x #p s mask))
          [SMTPat (timeless (pts_to_mask x #p s mask))]

ghost
fn pts_to_mask_len u#a (#t: Type u#a) (a:array t) (#p:perm) (#x:Seq.seq t) #mask
  preserves pts_to_mask a #p x mask
  ensures pure (length a == Seq.length x)

ghost
fn pts_to_mask_perm_bound u#a (#t: Type u#a) (arr: array t) #p (#s:Seq.seq t) #mask
  preserves pts_to_mask arr #p s mask
  requires pure (exists (i: nat). i < Seq.length s /\ mask i)
  ensures pure (p <=. 1.0R)

ghost
fn pts_to_mask_not_null u#a (#a: Type u#a) #p (r:array a) (#v:Seq.seq a) #mask
  preserves pts_to_mask r #p v mask
  ensures pure (not (is_null r))

ghost fn mask_vext u#a (#t: Type u#a) (arr: array t) #f #v v' #mask
  requires pts_to_mask arr #f v mask
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask

ghost fn mask_mext u#a (#t: Type u#a) (arr: array t) #f #v #mask (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  ensures pts_to_mask arr #f v mask'

ghost fn mask_ext u#a (#t: Type u#a) (arr: array t) #f #v #mask v' (mask': nat -> prop)
  requires pts_to_mask arr #f v mask
  requires pure (forall (i: nat). i < Seq.length v ==> (mask i <==> mask' i))
  requires pure (Seq.length v' == Seq.length v /\
    (forall (i: nat). mask i /\ i < Seq.length v ==> Seq.index v i == Seq.index v' i))
  ensures pts_to_mask arr #f v' mask'

fn mask_alloc u#a (#elt: Type u#a) {| small_type u#a |} (x: elt) (n: SZ.t)
  returns a: array elt
  ensures pts_to_mask a (Seq.create (SZ.v n) x) (fun _ -> True)
  ensures pure (length a == SZ.v n /\ is_full_array a)

fn mask_free u#a (#elt: Type u#a) (a: array elt) (#s: Ghost.erased (Seq.seq elt)) #mask
  requires pts_to_mask a s mask
  requires pure (forall i. mask i)
  requires pure (is_full_array a)

ghost
fn mask_share u#a (#a: Type u#a) (arr:array a) (#s: Seq.seq a) #p #mask
  requires pts_to_mask arr #p s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask
  ensures pts_to_mask arr #(p /. 2.0R) s mask

[@@allow_ambiguous]
ghost fn mask_gather u#a (#t: Type u#a) (arr: array t) #p1 #p2 #s1 #s2 #mask1 #mask2
  requires pts_to_mask arr #p1 s1 mask1
  requires pts_to_mask arr #p2 s2 mask2
  requires pure (forall i. mask1 i <==> mask2 i)
  ensures exists* (v: Seq.seq t). pts_to_mask arr #(p1 +. p2) v mask1 **
    pure ((Seq.length v == Seq.length s1 /\ Seq.length v == Seq.length s2) /\
      (forall (i: nat). i < Seq.length v /\ mask1 i ==> Seq.index v i == Seq.index s1 i /\ Seq.index v i == Seq.index s2 i))

// We need to give names to these combinators, otherwise unfold can't
// distinguish them when we have multiple pts_to_mask resources.
unfold let mask_isect (mask pred: nat -> prop) : nat -> prop = fun i -> mask i /\ pred i
unfold let mask_diff (mask pred: nat -> prop) : nat -> prop = fun i -> mask i /\ ~(pred i)

ghost fn split_mask u#a (#t: Type u#a) (arr: array t) #f #v #mask (pred: nat -> prop)
  requires pts_to_mask arr #f v mask
  ensures pts_to_mask arr #f v (mask_isect mask pred)
  ensures pts_to_mask arr #f v (mask_diff mask pred)

[@@allow_ambiguous]
ghost fn join_mask u#a (#t: Type u#a) (arr: array t) #f #v1 #v2 #mask1 #mask2
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
ghost fn join_mask' u#a (#t: Type u#a) (arr: array t) #f (#v: erased (Seq.seq t)) #mask1 #mask2
  requires pts_to_mask arr #f v mask1
  requires pts_to_mask arr #f v mask2
  requires pure (forall i. ~(mask1 i /\ mask2 i))
  ensures pts_to_mask arr #f v (fun i -> mask1 i \/ mask2 i)

[@@allow_ambiguous]
ghost
fn pts_to_mask_injective_eq u#a (#a: Type u#a) #p0 #p1 #s0 #s1 #mask0 #mask1 (arr:array a)
  preserves pts_to_mask arr #p0 s0 mask0
  preserves pts_to_mask arr #p1 s1 mask1
  ensures pure (Seq.length s0 == Seq.length s1 /\
    (forall (i: nat). i < Seq.length s0 /\ mask0 i /\ mask1 i ==>
      Seq.index s0 i == Seq.index s1 i))

fn mask_read u#a (#t: Type u#a) (a: array t) (i: SZ.t) #p (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  preserves pts_to_mask a #p s mask
  requires pure (mask (SZ.v i))
  returns res: t
  ensures pure (res == Seq.index s (SZ.v i))

fn mask_write u#a (#t: Type u#a) (a: array t) (i: SZ.t) (v: t) (#s: erased (Seq.seq t) { SZ.v i < Seq.length s }) #mask
  requires pts_to_mask a s mask
  requires pure (mask (SZ.v i))
  ensures pts_to_mask a (Seq.upd s (SZ.v i) v) mask

val gsub #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr }) : GTot (array t)

val gsub_null #t (arr: array t) (i: nat) (j: nat { i <= j /\ j <= length arr}) : Lemma
  (arr == null ==> gsub arr i j == null)

val length_gsub #t arr i j : Lemma (length (gsub #t arr i j) == j - i) [SMTPat (length (gsub arr i j))]
val offset_of_gsub #t arr i j : Lemma (offset_of (gsub #t arr i j) == offset_of arr + i) [SMTPat (offset_of (gsub arr i j))]
val base_of_gsub #t arr i j : Lemma (base_of (gsub #t arr i j) == base_of arr) [SMTPat (base_of (gsub arr i j))]

ghost fn gsub_intro u#a (#t: Type u#a) (arr: array t) #f #mask (i j: nat) (#v: erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
  requires pts_to_mask arr #f v mask
  requires pure (forall (k: nat). mask k /\ k < Seq.length v ==> i <= k /\ k < j)
  returns _: squash (length arr == Seq.length v)
  ensures pts_to_mask (gsub arr i j) #f (Seq.slice v i j) (fun k -> mask (k + i))

ghost fn gsub_elim u#a (#t: Type u#a) (arr: array t) #f (#mask: nat->prop) (i j: nat)
    (#v: erased (Seq.seq t) { i <= j /\ j <= length arr })
  requires pts_to_mask (gsub arr i j) #f v mask
  returns _: squash (j - i == Seq.length v)
  ensures exists* (v': Seq.seq t).
    pts_to_mask arr #f v' (fun k -> i <= k /\ k < j /\ mask (k - i)) **
    pure (Seq.length v' == length arr /\ (forall (k:nat). k < j - i ==> Seq.index v k == Seq.index v' (k + i)))

unobservable
fn sub u#a (#t: Type u#a) (arr: array t) #f #mask (i: SZ.t) (j: erased nat)
    (#v: erased (Seq.seq t) { SZ.v i <= j /\ j <= Seq.length (reveal v) })
  requires pts_to_mask arr #f v mask
  returns sub: (sub: array t { length arr == Seq.length (reveal v) })
  ensures rewrites_to sub (gsub arr (SZ.v i) j)
  ensures pts_to_mask sub #f (Seq.slice v (SZ.v i) j) (fun k -> mask (k + SZ.v i))
  ensures pts_to_mask arr #f v (fun k -> mask k /\ ~(SZ.v i <= k /\ k < j))

[@@allow_ambiguous]
ghost fn return_sub u#a (#t: Type u#a) (arr: array t) #f (#v #vsub: erased (Seq.seq t)) #mask #masksub (#i: nat) (#j: nat { i <= j /\ j <= length arr })
  requires pts_to_mask arr #f v mask
  requires pts_to_mask (gsub arr i j) #f vsub masksub
  requires pure (forall (k: nat). i <= k /\ k < j ==> ~(mask k))
  ensures exists* v'. pts_to_mask arr #f v' (fun k -> mask k \/ (i <= k /\ k < j /\ masksub (k - i)))
    ** pure (Seq.length v == Seq.length v' /\ i + Seq.length vsub == j /\ j <= Seq.length v /\
      (forall (k: nat). k < Seq.length v' ==>
      Seq.index v' k == (if i <= k && k < j then Seq.index vsub (k - i) else Seq.index v k)))