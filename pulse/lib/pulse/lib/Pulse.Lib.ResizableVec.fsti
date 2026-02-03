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

(**
  A bounded vector implementation for Pulse.
  
  This provides a vector with a fixed maximum capacity set at creation time.
  Elements can be added (push) up to the capacity, and removed (pop) from the end.
  Internally stores `option t` elements, using `None` as default for uninitialized slots.
*)

module Pulse.Lib.ResizableVec

#lang-pulse

open Pulse.Lib.Pervasives
module Seq = FStar.Seq
module SZ = FStar.SizeT

/// Abstract bounded vector type
val rvec (t:Type0) : Type0

/// Predicate relating a bounded vector to its logical contents and capacity
/// The sequence represents the actual elements, cap is the maximum capacity
val is_rvec (#t:Type0) ([@@@mkey]v:rvec t) (s:Seq.seq t) (cap:nat) : slprop

/// Create a new bounded vector with given capacity
/// Capacity must be positive
fn create (#t:Type0) (capacity:SZ.t{SZ.v capacity > 0})
  returns v:rvec t
  ensures is_rvec v Seq.empty (SZ.v capacity)

/// Get the current number of elements
fn len (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  preserves is_rvec v s cap
  returns n:SZ.t
  ensures pure (SZ.v n == Seq.length s)

/// Get the capacity
fn get_capacity (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  preserves is_rvec v s cap
  returns n:SZ.t
  ensures pure (SZ.v n == cap)

/// Read element at index i
/// Requires: i < length
fn get (#t:Type0) (v:rvec t) (i:SZ.t) (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased nat)
  preserves is_rvec v s cap
  returns x:t
  ensures pure (x == Seq.index s (SZ.v i))

/// Write element at index i
/// Requires: i < length
fn set (#t:Type0) (v:rvec t) (i:SZ.t) (x:t) (#s:erased (Seq.seq t){SZ.v i < Seq.length s}) (#cap:erased nat)
  requires is_rvec v s cap
  ensures is_rvec v (Seq.upd s (SZ.v i) x) cap

/// Check if there is room to push (length < capacity)
fn has_room (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  preserves is_rvec v s cap
  returns b:bool
  ensures pure (b <==> Seq.length s < cap)

/// Try to append element to end of vector
/// Returns true and appends if length < capacity
/// Returns false if length == capacity (no room)
fn push (#t:Type0) (v:rvec t) (x:t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
  returns b:bool
  ensures (if b then is_rvec v (Seq.snoc s x) cap ** pure (Seq.length s < cap)
           else is_rvec v s cap ** pure (Seq.length s == cap))

/// Remove and return the last element
/// Requires: vector is non-empty
fn pop (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t){Seq.length s > 0}) (#cap:erased nat)
  requires is_rvec v s cap
  returns x:t
  ensures is_rvec v (Seq.slice s 0 (Seq.length s - 1)) cap ** 
          pure (x == Seq.index s (Seq.length s - 1))

/// Free the bounded vector
fn free (#t:Type0) (v:rvec t) (#s:erased (Seq.seq t)) (#cap:erased nat)
  requires is_rvec v s cap
