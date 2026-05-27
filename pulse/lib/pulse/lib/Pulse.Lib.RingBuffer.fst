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
open Pulse.Lib.Vec
open FStar.SizeT
module Seq = FStar.Seq
module SZ = FStar.SizeT
module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (:=), (!) }
module ML = FStar.Math.Lemmas

/// Internal representation of a ring buffer
/// Uses a fixed-size array with head and tail indices
/// Define as part of a type block to match interface pattern
noeq
type ringbuffer_t (t:Type0) = {
  buffer : vec t;           // The underlying array storage
  head : box SZ.t;          // Index of the front element (where we pop from)
  tail : box SZ.t;          // Index where the next element will be pushed
  count : box SZ.t;         // Current number of elements
  cap : SZ.t;               // Maximum capacity (constant)
}

and ringbuffer (t:Type0) = ringbuffer_t t

/// Helper lemma for modular arithmetic
let lemma_mod_add_small (a b n:nat) : Lemma
  (requires n > 0 /\ a < n /\ b < n /\ a + b < n)
  (ensures (a + b) % n == a + b)
  = ML.small_mod (a + b) n

/// Helper lemma: modular addition distributes
let lemma_mod_add_assoc (a b n:nat) : Lemma
  (requires n > 0 /\ a < n)
  (ensures (a + b) % n == (a % n + b % n) % n)
  = ML.lemma_mod_plus_distr_l a b n;
    ML.lemma_mod_plus_distr_r (a % n) b n

/// Pure function to extract the logical contents from the ring buffer state
/// This models how we interpret the circular buffer's physical layout as a logical sequence
/// Given head, tail, count, capacity and array contents, extract the FIFO sequence
let rec contents_of_buffer_aux 
  (#t:Type0)
  (buf:Seq.seq t)
  (head:nat)
  (count:nat)
  (cap:nat{cap > 0 /\ head < cap /\ count <= cap /\ Seq.length buf == cap})
  : Tot (Seq.seq t) (decreases count)
  = if count = 0 then Seq.empty
    else 
      let elem = Seq.index buf head in
      let next_head = (head + 1) % cap in
      Seq.cons elem (contents_of_buffer_aux buf next_head (count - 1) cap)

let contents_of_buffer
  (#t:Type0)
  (buf:Seq.seq t)
  (head:nat)
  (count:nat)
  (cap:nat{cap > 0 /\ head < cap /\ count <= cap /\ Seq.length buf == cap})
  : Seq.seq t
  = contents_of_buffer_aux buf head count cap

/// Key lemma: length of extracted contents equals count
let rec lemma_contents_length
  (#t:Type0)
  (buf:Seq.seq t)
  (head:nat)
  (count:nat)
  (cap:nat{cap > 0 /\ head < cap /\ count <= cap /\ Seq.length buf == cap})
  : Lemma (ensures Seq.length (contents_of_buffer_aux buf head count cap) == count)
          (decreases count)
  = if count = 0 then ()
    else 
      let next_head = (head + 1) % cap in
      lemma_contents_length buf next_head (count - 1) cap

/// Abstract predicate: a ring buffer represents a logical sequence
/// Unfolds to the concrete representation with invariants
let is_ringbuffer (#t:Type0) ([@@@mkey]rb:ringbuffer t) (s:Seq.seq t) (cap:nat{cap > 0})
  : Tot slprop
  = exists* (buf:Seq.seq t) (h:SZ.t) (tl:SZ.t) (cnt:SZ.t).
      Vec.pts_to rb.buffer buf **
      B.pts_to rb.head h **
      B.pts_to rb.tail tl **
      B.pts_to rb.count cnt **
      pure (
        SZ.v rb.cap == cap /\
        Seq.length buf == cap /\
        SZ.v h < cap /\
        SZ.v tl < cap /\
        SZ.v cnt <= cap /\
        SZ.v cnt == Seq.length s /\
        // Buffer is full (allows freeing)
        is_full_vec rb.buffer /\
        // Key invariant: when empty, head == tail
        (SZ.v cnt == 0 ==> SZ.v h == SZ.v tl) /\
        // Key invariant: tail is where the next element goes
        (SZ.v cnt > 0 ==> SZ.v tl == (SZ.v h + SZ.v cnt) % cap) /\
        // The key correctness property: contents match the abstract sequence
        contents_of_buffer buf (SZ.v h) (SZ.v cnt) cap == s
      )

/// Create a new ring buffer
fn create (#t:Type0) (capacity:SZ.t{SZ.v capacity > 0}) (init:t)
  returns rb : ringbuffer t
  ensures is_ringbuffer rb Seq.empty (SZ.v capacity)
{
  // Allocate the backing array
  let buffer = alloc init capacity;
  
  // Create mutable state for head, tail, and count using Box
  let head = B.alloc 0sz;
  let tail = B.alloc 0sz;
  let count = B.alloc 0sz;
  
  // Package into the ring buffer structure
  let rb = { buffer; head; tail; count; cap = capacity };
  
  // Establish the invariant
  with buf. assert (Vec.pts_to buffer buf);
  rewrite (Vec.pts_to buffer buf) as (Vec.pts_to rb.buffer buf);
  
  with h. assert (B.pts_to head h);
  rewrite (B.pts_to head h) as (B.pts_to rb.head h);
  
  with tl. assert (B.pts_to tail tl);
  rewrite (B.pts_to tail tl) as (B.pts_to rb.tail tl);
  
  with cnt. assert (B.pts_to count cnt);
  rewrite (B.pts_to count cnt) as (B.pts_to rb.count cnt);
  
  // Prove that empty buffer satisfies the invariant
  assert pure (contents_of_buffer buf 0 0 (SZ.v capacity) == Seq.empty);
  
  fold (is_ringbuffer rb Seq.empty (SZ.v capacity));
  rb
}

/// Get the capacity
fn capacity (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns n : SZ.t
  ensures pure (SZ.v n == cap)
{
  unfold (is_ringbuffer rb s cap);
  with _buf _h _tl _cnt. _;
  fold (is_ringbuffer rb s cap);
  rb.cap
}

/// Get the current size
fn size (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns n : SZ.t
  ensures pure (SZ.v n == Seq.length s)
{
  unfold (is_ringbuffer rb s cap);
  with _buf _h _tl _cnt. _;
  let c = !rb.count;
  fold (is_ringbuffer rb s cap);
  c
}

/// Check if empty
fn is_empty (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns b : bool
  ensures pure (b <==> Seq.length s == 0)
{
  unfold (is_ringbuffer rb s cap);
  with _buf _h _tl _cnt. _;
  let c = !rb.count;
  let result = (c = 0sz);
  fold (is_ringbuffer rb s cap);
  result
}

/// Check if full
fn is_full (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  preserves is_ringbuffer rb s cap
  returns b : bool
  ensures pure (b <==> Seq.length s == cap)
{
  unfold (is_ringbuffer rb s cap);
  with _buf _h _tl _cnt. _;
  let c = !rb.count;
  let result = (c = rb.cap);
  fold (is_ringbuffer rb s cap);
  result
}

/// Lemma: pushing to the buffer updates contents correctly
let rec lemma_push_contents
  (#t:Type0)
  (buf:Seq.seq t)
  (head:nat)
  (tail:nat)
  (count:nat)
  (cap:nat{cap > 0 /\ head < cap /\ tail < cap /\ count < cap /\ Seq.length buf == cap})
  (x:t)
  : Lemma 
    (requires 
      count < cap /\ 
      (count == 0 ==> head == tail) /\
      (count > 0 ==> tail == (head + count) % cap))
    (ensures (
      let new_buf = Seq.upd buf tail x in
      let new_tail = (tail + 1) % cap in
      let new_count = count + 1 in
      let old_contents = contents_of_buffer buf head count cap in
      let new_contents = contents_of_buffer new_buf head new_count cap in
      new_contents `Seq.equal` Seq.snoc old_contents x
    ))
    (decreases count)
  = let new_buf = Seq.upd buf tail x in
    if count = 0 then ()  // Base case
    else (
      // Inductive case
      let next_head = (head + 1) % cap in
      lemma_push_contents buf next_head tail (count - 1) cap x
    )

/// Lemma: the tail invariant is maintained after push
let lemma_tail_invariant_maintained (h tl c cap:nat) : Lemma
  (requires 
    cap > 0 /\ h < cap /\ tl < cap /\ c < cap /\
    (c == 0 ==> h == tl) /\
    (c > 0 ==> tl == (h + c) % cap))
  (ensures (tl + 1) % cap == (h + (c + 1)) % cap)
  = if c = 0 then ()
    else lemma_mod_add_assoc h c cap

/// Push an element to the back
fn push_back (#t:Type0) (rb:ringbuffer t) (x:t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns success : bool
  ensures exists* (s':Seq.seq t).
    is_ringbuffer rb s' cap **
    pure ((success ==> (Seq.length s < cap /\ s' == Seq.snoc s x)) /\
          (not success ==> (Seq.length s == cap /\ s' == s)))
{
  unfold (is_ringbuffer rb s cap);
  with buf h tl cnt. _;
  
  let c = !rb.count;
  
  if (c = rb.cap) {
    // Buffer is full, reject the push
    fold (is_ringbuffer rb s cap);
    false
  } else {
    // Buffer has space, perform the push
    let t = !rb.tail;
    
    // Write the element at tail position
    rb.buffer.(t) <- x;
    with buf'. assert (pts_to rb.buffer buf');
    
    // Update tail with wrap-around
    let new_tail = (t +^ 1sz) %^ rb.cap;
    rb.tail := new_tail;
    
    // Increment count
    let new_count = c +^ 1sz;
    rb.count := new_count;
    
    // Prove the new contents are correct
    lemma_push_contents buf (SZ.v h) (SZ.v tl) (SZ.v cnt) cap x;
    
    // Prove the new invariant holds using a helper lemma
    lemma_tail_invariant_maintained (SZ.v h) (SZ.v tl) (SZ.v c) cap;
    
    assert pure (SZ.v new_count > 0);
    assert pure (SZ.v new_tail == (SZ.v h + SZ.v new_count) % cap);
    
    fold (is_ringbuffer rb (Seq.snoc s x) cap);
    true
  }
}

/// Lemma: popping from the buffer updates contents correctly
let lemma_pop_contents
  (#t:Type0)
  (buf:Seq.seq t)
  (head:nat)
  (count:nat{count > 0})
  (cap:nat{cap > 0 /\ head < cap /\ count <= cap /\ Seq.length buf == cap})
  : Lemma 
    (ensures (
      let elem = Seq.index buf head in
      let new_head = (head + 1) % cap in
      let new_count = count - 1 in
      let old_contents = contents_of_buffer buf head count cap in
      let new_contents = contents_of_buffer buf new_head new_count cap in
      Seq.head old_contents == elem /\
      Seq.tail old_contents `Seq.equal` new_contents
    ))
  = ()

/// Pop from the front
fn pop_front (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t){Seq.length s > 0})
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns x : t
  ensures is_ringbuffer rb (Seq.tail s) cap **
          pure (x == Seq.head s)
{
  unfold (is_ringbuffer rb s cap);
  with buf h tl cnt. _;
  
  let hd = !rb.head;
  
  // Read the element at head position
  let elem = rb.buffer.(hd);
  
  // Update head with wrap-around
  let new_head = (hd +^ 1sz) %^ rb.cap;
  rb.head := new_head;
  
  // Decrement count
  let c = !rb.count;
  let new_count = c -^ 1sz;
  rb.count := new_count;
  
  // Prove the new contents are correct
  lemma_pop_contents buf (SZ.v h) (SZ.v cnt) cap;
  
  fold (is_ringbuffer rb (Seq.tail s) cap);
  elem
}

/// Peek at the front element
fn peek_front (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t){Seq.length s > 0})
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
  returns x : t
  ensures is_ringbuffer rb s cap **
          pure (x == Seq.head s)
{
  unfold (is_ringbuffer rb s cap);
  with buf h tl cnt. _;
  
  let hd = !rb.head;
  
  // Read the element at head position
  let elem = rb.buffer.(hd);
  
  // The contents_of_buffer definition shows elem is the head
  // Since count > 0, contents is cons of elem and rest
  lemma_contents_length buf (SZ.v h) (SZ.v cnt) cap;
  
  fold (is_ringbuffer rb s cap);
  elem
}

/// Free the ring buffer
fn free (#t:Type0) (rb:ringbuffer t)
  (#s:erased (Seq.seq t))
  (#cap:erased nat{cap > 0})
  requires is_ringbuffer rb s cap
{
  unfold (is_ringbuffer rb s cap);
  with buf h tl cnt. _;
  
  // Free all the resources
  Vec.free rb.buffer;
  B.free rb.head;
  B.free rb.tail;
  B.free rb.count;
}
