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
{
  forevery_refine_ext #nat #(fun k -> i <= k /\ k < j) (fun k -> i' <= k /\ k < j') p;
}

ghost
fn range_empty_intro (p: nat -> slprop) (i: nat)
  ensures forall+ (k:nat{i <= k /\ k < i}). p k
{
  forevery_intro_empty #(k:nat{i <= k /\ k < i}) (fun k -> p k);
}

ghost
fn range_uncons (p: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires pure (i < j)
  ensures p i
  ensures forall+ (k:nat{i + 1 <= k /\ k < j}). p k
{
  forevery_remove' #nat (fun k -> i <= k /\ k < j) p i;
  forevery_refine_ext #nat #(fun k -> (i <= k /\ k < j) /\ k =!= i)
                      (fun k -> i + 1 <= k /\ k < j) p;
}

ghost
fn range_cons (p: nat -> slprop) (i j: nat)
  requires p i
  requires forall+ (k:nat{i + 1 <= k /\ k < j}). p k
  requires pure (i < j)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k
{
  forevery_insert #nat #(fun k -> i + 1 <= k /\ k < j) p i;
  forevery_refine_ext #nat #(fun k -> (i + 1 <= k /\ k < j) \/ i == k)
                      (fun k -> i <= k /\ k < j) p;
}

ghost
fn range_cons_down (p: nat -> slprop) (i: nat { 1 <= i }) (hi: nat)
  requires p (i - 1)
  requires forall+ (k:nat{i <= k /\ k < hi}). p k
  requires pure (i <= hi)
  ensures forall+ (k:nat{i - 1 <= k /\ k < hi}). p k
{
  forevery_insert #nat #(fun k -> i <= k /\ k < hi) p (i - 1);
  forevery_refine_ext #nat #(fun k -> (i <= k /\ k < hi) \/ (i - 1 <: nat) == k)
                      (fun k -> i - 1 <= k /\ k < hi) p;
}

ghost
fn range_unsnoc (p: nat -> slprop) (i: nat) (j: nat { i < j })
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures p (j - 1)
  ensures forall+ (k:nat{i <= k /\ k < j - 1}). p k
{
  forevery_remove' #nat (fun k -> i <= k /\ k < j) p (j - 1);
  forevery_refine_ext #nat #(fun k -> (i <= k /\ k < j) /\ k =!= (j - 1 <: nat))
                      (fun k -> i <= k /\ k < j - 1) p;
}

ghost
fn range_snoc (p: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires p j
  requires pure (i <= j)
  ensures forall+ (k:nat{i <= k /\ k < j + 1}). p k
{
  forevery_insert #nat #(fun k -> i <= k /\ k < j) p j;
  forevery_refine_ext #nat #(fun k -> (i <= k /\ k < j) \/ j == k)
                      (fun k -> i <= k /\ k < j + 1) p;
}

ghost
fn range_empty_elim (p: nat -> slprop) (i: nat)
  requires forall+ (k:nat{i <= k /\ k < i}). p k
  ensures emp
{
  forevery_elim_empty #(k:nat{i <= k /\ k < i}) (fun k -> p k);
}

ghost
fn range_singleton_intro (p: nat -> slprop) (i: nat)
  requires p i
  ensures forall+ (k:nat{i <= k /\ k < i + 1}). p k
{
  range_empty_intro p (i + 1);
  range_cons p i (i + 1);
}

ghost
fn range_singleton_elim (p: nat -> slprop) (i: nat)
  requires forall+ (k:nat{i <= k /\ k < i + 1}). p k
  ensures p i
{
  range_uncons p i (i + 1);
  range_empty_elim p (i + 1);
}

ghost
fn rec range_split (p: nat -> slprop) (i m j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires pure (i <= m /\ m <= j)
  ensures forall+ (k:nat{i <= k /\ k < m}). p k
  ensures forall+ (k:nat{m <= k /\ k < j}). p k
  decreases (m - i)
{
  if (i = m) {
    forevery_refine_ext #nat #(fun k -> i <= k /\ k < j) (fun k -> m <= k /\ k < j) p;
    range_empty_intro p i;
    forevery_refine_ext #nat #(fun k -> i <= k /\ k < i) (fun k -> i <= k /\ k < m) p;
  } else {
    range_uncons p i j;
    range_split p (i + 1) m j;
    range_cons p i m;
  }
}

ghost
fn rec range_join (p: nat -> slprop) (i m j: nat)
  requires forall+ (k:nat{i <= k /\ k < m}). p k
  requires forall+ (k:nat{m <= k /\ k < j}). p k
  requires pure (i <= m /\ m <= j)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k
  decreases (m - i)
{
  if (i = m) {
    forevery_refine_ext #nat #(fun k -> i <= k /\ k < m) (fun k -> i <= k /\ k < i) p;
    range_empty_elim p i;
    forevery_refine_ext #nat #(fun k -> m <= k /\ k < j) (fun k -> i <= k /\ k < j) p;
  } else {
    range_uncons p i m;
    range_join p (i + 1) m j;
    range_cons p i j;
  }
}

ghost
fn range_get (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures forall+ (kk:nat{i <= kk /\ kk < j}). p kk
  ensures p j
  ensures forall+ (kk:nat{j + 1 <= kk /\ kk < k}). p kk
{
  range_split p i j k;
  range_uncons p j k;
}

ghost
fn range_put (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < j}). p kk
  requires p j
  requires forall+ (kk:nat{j + 1 <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures forall+ (kk:nat{i <= kk /\ kk < k}). p kk
{
  range_cons p j k;
  range_join p i j k;
}

ghost
fn range_focus (p: nat -> slprop) (i j k: nat)
  requires forall+ (kk:nat{i <= kk /\ kk < k}). p kk
  requires pure (i <= j /\ j < k)
  ensures p j
  ensures (p j @==> (forall+ (kk:nat{i <= kk /\ kk < k}). p kk))
{
  range_get p i j k;
  intro (p j @==> (forall+ (kk:nat{i <= kk /\ kk < k}). p kk))
    #((forall+ (kk:nat{i <= kk /\ kk < j}). p kk) ** (forall+ (kk:nat{j + 1 <= kk /\ kk < k}). p kk))
    fn _ {
    range_put p i j k;
  };
}

ghost
fn range_weaken (p p': nat -> slprop) (i j: nat)
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i <= k /\ k < j}). p' k
{
  forevery_map #(k:nat{i <= k /\ k < j}) (fun k -> p k) (fun k -> p' k) phi;
}

ghost
fn range_zip (p q: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  requires forall+ (k:nat{i <= k /\ k < j}). q k
  ensures forall+ (k:nat{i <= k /\ k < j}). (p k ** q k)
{
  forevery_zip #(k:nat{i <= k /\ k < j}) (fun k -> p k) (fun k -> q k);
}

ghost
fn range_unzip (p q: nat -> slprop) (i j: nat)
  requires forall+ (k:nat{i <= k /\ k < j}). (p k ** q k)
  ensures forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i <= k /\ k < j}). q k
{
  forevery_unzip #(k:nat{i <= k /\ k < j}) (fun k -> p k) (fun k -> q k);
}

ghost
fn rec range_weaken_and_shift (p p': nat -> slprop) (delta: int)
  (i: nat { i + delta >= 0 }) (j: nat { j + delta >= 0 })
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' (k + delta)))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i + delta <= k /\ k < j + delta}). p' k
  decreases (if j <= i then 0 else j - i)
{
  if (i >= j) {
    forevery_elim_empty #(k:nat{i <= k /\ k < j}) (fun k -> p k);
    forevery_intro_empty #(k:nat{i + delta <= k /\ k < j + delta}) (fun k -> p' k);
  } else {
    range_uncons p i j;
    ghost
    fn phi_aux (k:nat{i + 1 <= k /\ k < j})
      requires p k
      ensures p' (k + delta)
    { phi k };
    range_weaken_and_shift p p' delta (i + 1) j phi_aux;
    forevery_refine_ext #nat #(fun k -> (i + 1) + delta <= k /\ k < j + delta)
                        (fun k -> (i + delta) + 1 <= k /\ k < j + delta) p';
    phi i;
    range_cons p' (i + delta) (j + delta);
  }
}

ghost
fn rec range_weaken_and_shift_down (p p': nat -> slprop) (delta: nat)
  (i: nat { delta <= i }) (j: nat { delta <= j })
  (phi: (k:nat{i <= k /\ k < j}) -> stt_ghost unit emp_inames (p k) (fun _ -> p' (k - delta)))
  requires forall+ (k:nat{i <= k /\ k < j}). p k
  ensures forall+ (k:nat{i - delta <= k /\ k < j - delta}). p' k
  decreases (if j <= i then 0 else j - i)
{
  if (i >= j) {
    forevery_elim_empty #(k:nat{i <= k /\ k < j}) (fun k -> p k);
    forevery_intro_empty #(k:nat{i - delta <= k /\ k < j - delta}) (fun k -> p' k);
  } else {
    range_uncons p i j;
    ghost
    fn phi_aux (k:nat{i + 1 <= k /\ k < j})
      requires p k
      ensures p' (k - delta)
    { phi k };
    range_weaken_and_shift_down p p' delta (i + 1) j phi_aux;
    forevery_refine_ext #nat #(fun k -> (i + 1) - delta <= k /\ k < j - delta)
                        (fun k -> (i - delta) + 1 <= k /\ k < j - delta) p';
    phi i;
    range_cons p' (i - delta) (j - delta);
  }
}
