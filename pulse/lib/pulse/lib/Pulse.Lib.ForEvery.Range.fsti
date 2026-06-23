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

(* Helper lemmas for working with `forall+` over a contiguous range of
   naturals, i.e. slprops of the form

     forall+ (k:nat{i <= k /\ k < j}). p k

   These replace the (now removed) `Pulse.Lib.OnRange` API. *)

module Pulse.Lib.ForEvery.Range
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery
open Pulse.Lib.Trade

ghost
fn range_rebound (p: nat -> slprop) (i j i' j': nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires pure (forall (k:nat). (i <= k /\ k < j) <==> (i' <= k /\ k < j'))
  ensures forall+ (k:nat{i' <= k /\ k < j'}). p k

ghost
fn range_empty_intro (p: nat -> slprop) (i: nat)
  ensures forall+ (k:nat{i <= k /\ k < i}). p k

ghost
fn range_empty_elim (p: nat -> slprop) (i: nat)
  requires forall+ (k:nat{i <= k /\ k < i}). p k
  ensures emp

ghost
fn range_uncons (p: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires pure (i < j)
  ensures p i
  ensures forall+ (k:nat{i + 1 <= k /\ k < j}). p k

ghost
fn range_cons (p: nat -> slprop) (i j: nat)
  requires p i
  requires forall+ (k:nat{i + 1 <= k /\ k < j}). p k
  requires pure (i < j)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k

ghost
fn range_cons_down (p: nat -> slprop) (i: nat { 1 <= i }) (hi: nat)
  requires p (i - 1)
  requires forall+ (k:nat{i <= k /\ k < hi}). p k
  requires pure (i <= hi)
  ensures forall+ (k:nat{i - 1 <= k /\ k < hi}). p k

ghost
fn range_unsnoc (p: nat -> slprop) (i: nat) (j: nat { i < j })
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures p (j - 1)
  ensures forall+ (k:nat{i <= k /\ k < j - 1}). p k

ghost
fn range_snoc (p: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires p j
  requires pure (i <= j)
  ensures forall+ (k:nat{i <= k /\ k < j + 1}). p k

ghost
fn range_singleton_intro (p: nat -> slprop) (i: nat)
  requires p i
  ensures forall+ (k:nat{i <= k /\ k < i + 1}). p k

ghost
fn range_singleton_elim (p: nat -> slprop) (i: nat)
  requires forall+ (k:nat{i <= k /\ k < i + 1}). p k
  ensures p i

ghost
fn range_split (p: nat -> slprop) (i m j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires pure (i <= m /\ m <= j)
  ensures forall+ (k:nat{i <= k /\ k < m}). p k
  ensures forall+ (k:nat{m <= k /\ k < j}). p k

ghost
fn range_join (p: nat -> slprop) (i m j: nat)
  requires forall+ (k:nat{i <= k /\ k < m}). p k
  requires forall+ (k:nat{m <= k /\ k < j}). p k
  requires pure (i <= m /\ m <= j)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k

ghost
fn range_get (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures forall+ (kk:nat{i <= kk /\ kk < j}). p kk
  ensures p j
  ensures forall+ (kk:nat{j + 1 <= kk /\ kk < k}). p kk

ghost
fn range_put (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < j}). p kk
  requires p j
  requires forall+ (kk:nat{j + 1 <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures forall+ (kk:nat{i <= kk /\ kk < k}). p kk

ghost
fn range_focus (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures p j
  ensures (p j @==> (forall+ (kk:nat{i <= kk /\ kk < k}). p kk))

ghost
fn range_weaken (p p': nat -> slprop) (i j: nat)
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i <= k /\ k < j}). p' k

ghost
fn range_weaken_and_shift (p p': nat -> slprop) (delta: int)
  (i: nat { i + delta >= 0 }) (j: nat { j + delta >= 0 })
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' (k + delta)))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i + delta <= k /\ k < j + delta}). p' k

ghost
fn range_weaken_and_shift_down (p p': nat -> slprop) (delta: nat)
  (i: nat { delta <= i }) (j: nat { delta <= j })
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' (k - delta)))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i - delta <= k /\ k < j - delta}). p' k

ghost
fn range_zip (p q: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires forall+ (k:nat{i <= k /\ k < j}). q k
  ensures forall+ (k:nat{i <= k /\ k < j}). (p k ** q k)

ghost
fn range_unzip (p q: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). (p k ** q k)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i <= k /\ k < j}). q k
