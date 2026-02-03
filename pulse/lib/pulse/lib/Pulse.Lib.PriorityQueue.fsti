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

module Pulse.Lib.PriorityQueue

#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.TotalOrder
open FStar.Mul

module Seq = FStar.Seq
module SZ = FStar.SizeT
module SeqP = FStar.Seq.Properties

/// A min-heap priority queue with fixed capacity
val pqueue (t:Type0) {| total_order t |} : Type0

/// Count occurrences of x in sequence s
let count (#t:eqtype) (x:t) (s:Seq.seq t) : nat = SeqP.count x s

/// Predicate: x is <= all elements in s (x is the minimum)
let is_minimum (#t:Type0) {| total_order t |} (x:t) (s:Seq.seq t) : prop =
  forall (i:nat). i < Seq.length s ==> x <=? Seq.index s i

/// extends s0 s1 x: s1 is s0 extended with one occurrence of x
/// i.e., count of x increases by 1, all other counts stay same
let extends (#t:eqtype) (s0 s1:Seq.seq t) (x:t) : prop =
  count x s1 == count x s0 + 1 /\
  (forall (y:t). y =!= x ==> count y s1 == count y s0)

/// Predicate relating pqueue to its logical sequence and capacity
val is_pqueue (#t:Type0) {| total_order t |} ([@@@mkey]pq:pqueue t) (s:Seq.seq t) (cap:nat) : slprop

/// Create empty priority queue with given capacity
fn create (#t:Type0) {| total_order t |} (capacity:SZ.t{SZ.v capacity > 0})
  requires emp
  returns pq : pqueue t
  ensures is_pqueue pq Seq.empty (SZ.v capacity)

/// Check if empty
fn is_empty (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
  returns b:bool
  ensures is_pqueue pq 's0 cap ** pure (b <==> Seq.length 's0 == 0)

/// Get size
fn size (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
  returns n:SZ.t
  ensures is_pqueue pq 's0 cap ** pure (SZ.v n == Seq.length 's0)

/// Get capacity
fn get_capacity (#t:Type0) {| total_order t |} (pq:pqueue t) (#s0:erased (Seq.seq t)) (#cap:erased nat)
  requires is_pqueue pq s0 cap
  returns n:SZ.t
  ensures is_pqueue pq s0 cap ** pure (SZ.v n == cap)

/// Insert element - returns true on success, false if at capacity
/// On success: s1 extends s0 with x, and length was < capacity
/// On failure: length == capacity (queue is full)
fn insert (#t:eqtype) {| total_order t |} (pq:pqueue t) (x:t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
  returns b:bool
  ensures (if b 
           then exists* s1. is_pqueue pq s1 cap ** pure (extends 's0 s1 x /\ Seq.length 's0 < cap)
           else is_pqueue pq 's0 cap ** pure (Seq.length 's0 == cap))

/// Peek at minimum (root of heap) - returns the smallest element
fn peek_min (#t:Type0) {| total_order t |} (pq:pqueue t)
  (#s0:erased (Seq.seq t){Seq.length s0 > 0})
  (#cap:erased nat)
  requires is_pqueue pq s0 cap
  returns x:t
  ensures is_pqueue pq s0 cap ** pure (x == Seq.index s0 0 /\ is_minimum x s0)

/// Extract minimum - removes and returns the smallest element
/// The resulting sequence s1 satisfies: extends s1 s0 x (i.e., s0 extends s1 with x)
fn extract_min (#t:eqtype) {| total_order t |} (pq:pqueue t)
  (#s0:erased (Seq.seq t){Seq.length s0 > 0 /\ SZ.fits (2 * Seq.length s0 + 2)})
  (#cap:erased nat)
  requires is_pqueue pq s0 cap
  returns x:t
  ensures exists* s1. is_pqueue pq s1 cap ** 
          pure (x == Seq.index s0 0 /\ is_minimum x s0 /\ extends s1 s0 x)

/// Free the queue
fn free (#t:Type0) {| total_order t |} (pq:pqueue t) (#cap:erased nat)
  requires is_pqueue pq 's0 cap
  ensures emp
