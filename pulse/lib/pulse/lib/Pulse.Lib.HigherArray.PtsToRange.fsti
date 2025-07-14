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

module Pulse.Lib.HigherArray.PtsToRange
#lang-pulse
open FStar.Tactics.V2
open Pulse.Lib.Core
open Pulse.Main
open Pulse.Class.PtsTo
open PulseCore.FractionalPermission
open FStar.Ghost
module SZ = FStar.SizeT
module Seq = FStar.Seq
open Pulse.Lib.HigherArray.Core
open Pulse.Lib.HigherArray.PtsTo
open Pulse.Lib.SmallType

val pts_to_range
  (#a:Type u#a)
  ([@@@mkey]x:array a)
  ([@@@mkey] i [@@@mkey] j : nat)
  (#[exact (`1.0R)] p:perm)
  (s : Seq.seq a) : slprop

val pts_to_range_timeless (#a: Type u#a) (x:array a) (i j : nat) (p:perm) (s:Seq.seq a)
  : Lemma (timeless (pts_to_range x i j #p s))
          [SMTPat (timeless (pts_to_range x i j #p s))]

let is_subarray #elt (a: array elt) (i j: nat) (b: array elt) : prop =
  base_of b == base_of a /\
  offset_of b == offset_of a + i /\
  i + length b == j /\
  j <= length a

ghost
fn pts_to_range_prop
  u#a (#elt: Type u#a) (a: array elt) (#i #j: nat)
  (#p: perm)
  (#s: Seq.seq elt)
  requires pts_to_range a i j #p s
  ensures  pts_to_range a i j #p s ** pure (
   (i <= j /\ j <= length a /\ eq2 #nat (Seq.length s) (j - i))
  )

ghost
fn pts_to_range_intro
  u#a (#elt: Type u#a)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to a #p s
  ensures  pts_to_range a 0 (length a) #p s

ghost
fn pts_to_range_elim
  u#a (#elt: Type u#a)
  (a: array elt)
  (p: perm)
  (s: Seq.seq elt)
  requires pts_to_range a 0 (length a) #p s
  ensures  pts_to a #p s

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

ghost
fn pts_to_range_join
  u#a (#elt: Type u#a)
  (a: array elt)
  (i m j: nat)
  (#p: perm)
  (#s1 #s2: Seq.seq elt)
  requires pts_to_range a i m #p s1 ** pts_to_range a m j #p s2
  ensures  pts_to_range a i j #p (s1 `Seq.append` s2)

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
  returns  res : t
  ensures
    pts_to_range a l r #p s **
    pure (eq2 #int (Seq.length s) (r - l) /\
          res == Seq.index s (SZ.v i - l))

inline_for_extraction
fn pts_to_range_upd
  u#a (#t: Type u#a)
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
      pure (
        eq2 #int (Seq.length s0) (r - l) /\
        s == Seq.upd s0 (SZ.v i - l) v
      )

ghost
fn pts_to_range_share
  u#a (#a: Type u#a)
  (arr:array a)
  (#l #r: nat)
  (#s:Seq.seq a)
  (#p:perm)
  requires pts_to_range arr l r #p s
  ensures  pts_to_range arr l r #(p /. 2.0R) s ** pts_to_range arr l r #(p /. 2.0R) s

[@@allow_ambiguous]
ghost
fn pts_to_range_gather
  u#a (#a: Type u#a)
  (arr:array a)
  (#l #r: nat)
  (#s0 #s1: Seq.seq a)
  (#p0 #p1:perm)
  requires pts_to_range arr l r #p0 s0 ** pts_to_range arr l r #p1 s1
  ensures  pts_to_range arr l r #(p0 +. p1) s0 ** pure (s0 == s1)
