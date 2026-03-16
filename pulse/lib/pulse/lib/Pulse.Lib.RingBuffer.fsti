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

module Pulse.Lib.RingBuffer

#lang-pulse
open Pulse.Lib.Pervasives
open FStar.SizeT
module Seq = FStar.Seq
module SZ = FStar.SizeT

/// A ring buffer (circular buffer) with fixed capacity and FIFO semantics
/// Implemented with array-backed storage and modular arithmetic for wrap-around
val ringbuffer (t:Type0) : Type0

/// Abstract predicate relating a concrete ring buffer to an abstract sequence
/// The sequence represents the logical contents from front to back (FIFO order)
/// Key invariants encoded in this predicate:
/// - The length of the sequence is always <= capacity
/// - Elements are stored in FIFO order
val is_ringbuffer (#t:Type0) ([@@@mkey]rb:ringbuffer t) (s:Seq.seq t) (cap:nat{cap > 0})
  : Tot slprop

/// Create a new ring buffer with the given capacity
/// The capacity must be positive
/// Initially the ring buffer is empty
fn create (#t:Type0) (capacity:SZ.t{SZ.v capacity > 0}) (init:t)
  returns rb : ringbuffer t
  ensures is_ringbuffer rb Seq.empty (SZ.v capacity)

/// Get the capacity of the ring buffer (maximum number of elements)
fn capacity (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns n : SZ.t
  ensures pure (SZ.v n == cap)

/// Get the current size (number of elements) in the ring buffer
fn size (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns n : SZ.t
  ensures pure (SZ.v n == Seq.length s)

/// Check if the ring buffer is empty
fn is_empty (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns b : bool
  ensures pure (b <==> Seq.length s == 0)

/// Check if the ring buffer is full
fn is_full (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns b : bool
  ensures pure (b <==> Seq.length s == cap)

/// Push an element to the back of the ring buffer
/// Behavior when full: Returns false and does not modify the buffer (reject mode)
/// This ensures we never lose data without explicit acknowledgment
fn push_back (#t:Type0) (rb:ringbuffer t) (x:t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns success : bool
  ensures exists* (s':Seq.seq t).
    is_ringbuffer rb s' cap **
    pure ((success ==> (Seq.length s < cap /\ s' == Seq.snoc s x)) /\
          (not success ==> (Seq.length s == cap /\ s' == s)))

/// Pop an element from the front of the ring buffer
/// Requires: the buffer must be non-empty (proven via Seq.length s > 0)
/// Returns: the front element (maintaining FIFO semantics)
fn pop_front (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t){Seq.length s > 0})
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns x : t
  ensures is_ringbuffer rb (Seq.tail s) cap **
          pure (x == Seq.head s)

/// Peek at the front element without removing it
/// Requires: the buffer must be non-empty
fn peek_front (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t){Seq.length s > 0})
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns x : t
  ensures is_ringbuffer rb s cap **
          pure (x == Seq.head s)

/// Free the ring buffer
/// Deallocates the underlying array storage
fn free (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
