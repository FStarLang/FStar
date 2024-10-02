(*
   Copyright 2008-2018 Microsoft Research

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
module LowStar.Ex2

/// Lab Session: Programming in Low*. This is intended as a warm-up to get
/// familiar with Low*. The module defines a few aliases that may come in handy.
module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.Integers
open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Modifies

(***** Working with references *)
/// The classic swap on references: provide suitable pre- and post-conditions.
/// Two useful operations: b *= (e), for writing into a pointer, and !*(e), for
/// dereferencing a pointer.
let swap (x: B.pointer uint_32) (y: B.pointer uint_32): Stack unit
  (requires fun h0 -> B.live h0 x /\ B.live h0 y /\ B.disjoint x y)
  (ensures fun h0 _ h1 ->
           modifies (loc_union (loc_buffer x) (loc_buffer y)) h0 h1 /\
           deref h1 x = deref h0 y /\
           deref h1 y = deref h0 x)
= let tmp = !* x in
  x *= !* y;
  y *= tmp

(***** Working with buffers *)

/// The next exercise is a copy from a source to a destination. Just like in the
/// earlier lecture, we will prove memory safety. We will also prove functional
/// correctness, i.e. that after copy i elements from src to dst, the sequences
/// that reflect the contents of the buffer are equal.

/// Our first useful definition is a type abbreviation for a buffer whose length
/// is known at type-checking time.
let lbuffer (len:uint_32) (a:Type) = b:B.buffer a{len <= B.len b}

/// A predicate, stating that b1 and b2 are equal, in memory h, over their first
/// i elements.
let prefix_equal (#l:uint_32) (#a:Type) (h:HS.mem) (b1 b2: lbuffer l a) (i:uint_32{i <= l}) =
  forall (j:nat). j < v i ==> B.get h b1 j == B.get h b2 j

/// For this version, you are expected to verify safety, but also functional
/// correctness. Start by writing the code, then proving that it is memory safe.
/// Here is the list of predicates you will need:
/// - B.live h b, to show that buffer b is live in memory h
/// - B.disjoint b1 b2, to show that two buffers do not overlap
/// - loc_buffer b, the injection of a buffer into the generic type of memory locations
/// - modifies l h0 h1, a predicate stating that going from memory h0 to memory
///   h1, only location l was modified.
/// Once you have proved memory safety, show how copy_correct extends the
/// prefix_equal predicate.
let rec copy_correct (#len:uint_32) (dst src:lbuffer len uint_32) (cur: uint_32): Stack unit
  (requires (fun h0 ->
                 B.live h0 src
              /\ B.live h0 dst
              /\ B.disjoint src dst
              /\ cur <= len
              /\ prefix_equal h0 src dst cur))
  (ensures fun h0 _ h1 ->
              B.live h1 src
           /\ B.live h1 dst
           /\ modifies (loc_buffer dst) h0 h1
           /\ prefix_equal h1 src dst len)
= if cur <> len
  then begin
    dst.(cur) <- src.(cur);
    copy_correct dst src (cur + 1ul)
 end
