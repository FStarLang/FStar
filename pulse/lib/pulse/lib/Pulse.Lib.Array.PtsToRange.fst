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

module Pulse.Lib.Array.PtsToRange
#lang-pulse
open Pulse.Main
open FStar.Tactics.V2
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open FStar.PCM
module Frac = Pulse.Lib.PCM.Fraction
module PM = Pulse.Lib.PCM.Map
open Pulse.Lib.PCM.Array
module PA = Pulse.Lib.PCM.Array
open Pulse.Lib.WithPure

let pts_to_range
  (#a: Type u#a)
  ([@@@mkey] x:array a)
  (i j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a)
: slprop
= with_pure (i <= j /\ j <= length x) fun _ -> pts_to (gsub x i j) #p s

let is_send_pts_to_range x i j p s = Tactics.Typeclasses.solve

ghost fn fold_pts_to_range u#a (#a: Type u#a) (x: array a)
    (i: nat) (j: nat { i <= j /\ j <= length x }) #p #s0 s #mask
  requires pts_to_mask (gsub x i j) #p s0 mask
  requires pure (Seq.length s == Seq.length s0 /\
    (forall (i: nat). i < Seq.length s ==> Some (Seq.index s i) == Seq.index s0 i))
  requires pure (forall (k: nat). k < j - i ==> mask k)
  ensures pts_to_range x i j #p s
{
  pts_to_mask_len (gsub x i j);
  mask_ext (gsub x i j) s0 (fun _ -> True);
  from_mask (gsub x i j);
  with v. fold pts_to_range x i j #p v;
  assert pure (v `Seq.equal` s);
}

ghost fn unfold_pts_to_range u#a (#a: Type u#a) (x: array a) (i j: nat) #p s
  requires pts_to_range x i j #p s
  returns _: squash (i <= j /\ j <= length x)
  ensures exists* (s' : Seq.seq (option a)).
    pts_to_mask (gsub x i j) #p s' (fun _ -> True) **
    pure (Seq.length s' == Seq.length s /\
      (forall (i: nat). i < Seq.length s' ==>
        Seq.index s' i == Some (Seq.index s i)))
{
  unfold pts_to_range x i j #p s;
  to_mask (gsub x i j);
  ()
}

let pts_to_range_timeless (#a: Type u#a) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to_range x i j #p s))
          [SMTPat (timeless (pts_to_range x i j #p s))]
  = ()

ghost
fn pts_to_range_prop
  u#a (#elt: Type u#a)
  (a: array elt)
  (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
  requires pts_to_range a i j #p s
  ensures pts_to_range a i j #p s ** pure (
      (~ (is_null a)) /\
      (i <= j /\ j <= length a /\ Seq.length s == j - i)
    )
{
  unfold_pts_to_range a i j #p s;
  pts_to_mask_not_null _;
  gsub_null a i j;
  pts_to_mask_len (gsub a i j);
  fold_pts_to_range a i j #p s;
}

ghost
fn pts_to_range_intro
  u#a (#elt: Type u#a)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to a #p s
  ensures pts_to_range a 0 (length a) #p s
{
  to_mask a;
  pts_to_mask_len a;
  gsub_intro a 0 (length a);
  fold_pts_to_range a 0 (length a) #p s;
}

ghost
fn pts_to_range_elim
  u#a (#elt: Type u#a)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to_range a 0 (length a) #p s
  ensures pts_to a #p s
{
  unfold_pts_to_range a 0 (length a) #p s;
  gsub_elim a 0 (length a);
  from_mask a;
  with s'. assert pts_to a #p s' ** pure (s `Seq.equal` s');
}

ghost
fn pts_to_range_split
  u#a (#elt: Type u#a)
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
  unfold_pts_to_range a i j s;
  gsub_elim a i j;
  with v' mask. assert pts_to_mask a #p v' mask;
  let pred : (nat -> prop) = (fun k -> k < m);
  split_mask a pred;
  gsub_intro a #_ #(mask_isect mask pred) i m;
  gsub_intro a #_ #(mask_diff mask pred) m j;
  let s1 = Seq.slice s 0 (m - i);
  let s2 = Seq.slice s (m - i) (Seq.length s);
  fold_pts_to_range a i m #p s1;
  fold_pts_to_range a m j #p s2;
  assert pure (s `Seq.equal` Seq.append s1 s2);
}

ghost
fn pts_to_range_join
  u#a (#elt: Type u#a)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
requires
  pts_to_range a i m #p s1 ** pts_to_range a m j #p s2
  ensures pts_to_range a i j #p (s1 `Seq.append` s2)
{
  unfold_pts_to_range a i m #p s1;
  unfold_pts_to_range a m j #p s2;
  gsub_elim a i m;
  gsub_elim a m j;
  join_mask a;
  gsub_intro a i j;
  fold_pts_to_range a i j #p (Seq.append s1 s2);
}

inline_for_extraction
fn pts_to_range_index
  u#a (#t: Type u#a)
  (a: array t)
  (i: SZ.t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s: Ghost.erased (Seq.seq t))
  (#p: perm)
  requires pts_to_range a l r #p s
  returns res:t
  ensures
    pts_to_range a l r #p s **
    pure (eq2 #int (Seq.length s) (r - l) /\
          res == Seq.index s (SZ.v i - l))
{
  pts_to_range_prop a;
  unfold_pts_to_range a l r #p s;
  with s1 m1. assert pts_to_mask (gsub a l r) #p s1 m1;
  assert pure (Seq.index s1 (SZ.v i - l) == Some (Seq.index s (SZ.v i - l)));
  gsub_elim a l r;
  let res = mask_read a i;
  gsub_intro a l r;
  fold_pts_to_range a l r #p s;
  res
}

inline_for_extraction
fn pts_to_range_upd
  u#a (#t: Type u#a)
  (a: array t)
  (i: SZ.t)
  (v: t)
  (#l: Ghost.erased nat{l <= SZ.v i})
  (#r: Ghost.erased nat{SZ.v i < r})
  (#s0: Ghost.erased (Seq.seq t))
  requires pts_to_range a l r #1.0R s0
  ensures
    exists* s.
      pts_to_range a l r s **
      pure (
          eq2 #int (Seq.length s0) (r - l) /\
          s == Seq.upd s0 (SZ.v i - l) v
      )
{
  unfold_pts_to_range a l r #1.0R s0;
  gsub_elim a l r;
  mask_write a i v;
  gsub_intro a l r;
  let s = hide (Seq.upd s0 (SZ.v i - l) v);
  fold_pts_to_range a l r #1.0R s;
}

ghost
fn pts_to_range_share
  u#a (#a: Type u#a)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
      requires pts_to_range arr l r #p s
      ensures pts_to_range arr l r #(p /. 2.0R) s ** pts_to_range arr l r #(p /. 2.0R) s
{
  unfold_pts_to_range arr l r #p s;
  mask_share (gsub arr l r);
  fold_pts_to_range arr l r s;
  fold_pts_to_range arr l r s;
}

ghost
fn pts_to_range_gather
  u#a (#a: Type u#a)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
      requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1
      ensures pts_to_range arr l r #(p0 +. p1) s0 ** pure (s0 == s1)
{
  unfold_pts_to_range arr l r s0;
  unfold_pts_to_range arr l r s1;
  mask_gather (gsub arr l r);
  assert pure (s0 `Seq.equal` s1);
  fold_pts_to_range arr l r s0;
}
