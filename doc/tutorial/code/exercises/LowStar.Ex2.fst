// BEGIN: DisplayFrag
module LowStar.Ex2

/// Programming with references and buffers
// END: DisplayFrag

/// The module defines a few aliases that may come in handy.
module B = LowStar.Buffer
module HS = FStar.HyperStack

open FStar.Integers
open LowStar.BufferOps
open FStar.HyperStack.ST
open LowStar.Modifies


(***** Working with references *)
/// The classic swap on references: provide suitable pre- and post-conditions.
/// Two useful operations: b *= (e), for writing into a pointer, and !*(e), for
/// dereferencing a pointer. Moreover, in order to state a meaningful
/// post-condition, you will need:
/// - loc_buffer, which injects a buffer into the type of abstract memory
///   locations
/// - loc_union, which computes the union of two memory locations
/// - modifies l h0 h1, a predicate stating that going from memory h0 to memory
///   h1, only location l was modified.
/// - B.get h p i, which fetches the contents of pointer p in heap h at index i
let swap (x: B.pointer uint_32) (y: B.pointer uint_32): Stack unit
  (requires fun h0 -> B.live h0 x /\ B.live h0 y /\ B.disjoint x y)
  (ensures fun _ _ _ -> True)
=
  admit ()

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
  (requires fun h0 ->
     True)
  (ensures fun h0 _ h1 ->
     True)
=
  admit ()
