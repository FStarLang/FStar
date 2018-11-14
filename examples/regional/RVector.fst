module RVector

open FStar.All
open FStar.Integers
open LowStar.Modifies
open LowStar.Regional
open LowStar.RVector
open LowStar.Regional.Instances

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = LowStar.Vector
module RV = LowStar.RVector
module RVI = LowStar.Regional.Instances

module U32 = FStar.UInt32

// This small example is to introduce how to use the `regional` typeclass,
// which is quite useful when dealing with lots of pointers in Low*.

// Having a `regional` typeclass instance guarantees that every object of the
// instance type is allocated, manipulated, and freed within a designated
// region. Not surprisingly, we have an instance saying that every Low* buffer
// type is regional.
val breg: regional (B.buffer U32.t)
let breg = RVI.buffer_regional 0ul 16ul

// We already know that if the regions of two Low* buffers are disjoint then
// the locations are disjoint as well. Using a `regional` typeclass is not that
// useful for now.
val two_regional_buffers_disjoint:
  b1:B.buffer U32.t -> b2:B.buffer U32.t ->
  Lemma (requires (HH.disjoint (Rgl?.region_of breg b1) (Rgl?.region_of breg b2)))
        (ensures (B.loc_disjoint (B.loc_buffer b1) (B.loc_buffer b2)))
let two_regional_buffers_disjoint b1 b2 = ()

// Let's move on to a complicated data structure, a vector of buffers. Since a
// vector is just a wrapper of a buffer for capacity control, we can regard it
// as a two-dimensional pointer.
// We already have a typeclass instance for the vector of buffers, guaranteeing
// that all pointers, including all the element pointers and the vector itself,
// are in a certain region and all vector operations preserve this invariant.
val vreg: regional (RV.rvector breg)
let vreg = RVI.vector_regional breg

// Now the disjointness between two regional vectors guarantees more than two
// vector locations are disjoint; it says that any two buffer elements
// respectively from each vector are disjoint as well.
val two_regional_vectors_disjoint:
  v1:RV.rvector breg -> v2:RV.rvector breg ->
  Lemma (requires (HH.disjoint (Rgl?.region_of vreg v1) (Rgl?.region_of vreg v2)))
        (ensures (B.loc_disjoint (RV.loc_rvector v1) (RV.loc_rvector v2)))
let two_regional_vectors_disjoint v1 v2 = ()

private val bcpy: copyable _ breg
private let bcpy = Cpy (fun src dst -> B.blit src 0ul dst 0ul 16ul)

// We have two more examples that actively use the regional vector.
// The first example claims that if we insert an element to a vector, the
// insertion does not affect the other vector with a different region.
val insert_does_not_affect_the_other:
  v1:RV.rvector breg{not (V.is_full v1)} ->
  nv:B.buffer U32.t ->
  v2:RV.rvector breg ->
  HST.ST (RV.rvector breg)
    (requires (fun h0 ->
      Rgl?.r_inv breg h0 nv /\
      Rgl?.r_inv vreg h0 v1 /\ Rgl?.r_inv vreg h0 v2 /\
      HH.disjoint (Rgl?.region_of vreg v1) (Rgl?.region_of breg nv) /\
      HH.disjoint (Rgl?.region_of vreg v1) (Rgl?.region_of vreg v2)))
    (ensures (fun h0 iv1 h1 ->
      Rgl?.r_inv vreg h1 iv1 /\ Rgl?.r_inv vreg h1 v2 /\
      Rgl?.r_repr vreg h0 v2 == Rgl?.r_repr vreg h1 v2))
let insert_does_not_affect_the_other v1 nv v2 =
  // Here we can see that the proof is quite automated; it suffices to
  // explicitly say that two vector locations are disjoint.
  assert (B.loc_disjoint (RV.loc_rvector v1) (RV.loc_rvector v2));
  RV.insert_copy bcpy v1 nv

// The second example claims that freeing a vector does not affect the other
// vector as well.
val free_does_not_affect_the_other:
  v1:RV.rvector breg{not (V.is_full v1)} ->
  v2:RV.rvector breg ->
  HST.ST unit
    (requires (fun h0 ->
      Rgl?.r_inv vreg h0 v1 /\ Rgl?.r_inv vreg h0 v2 /\
      HH.disjoint (Rgl?.region_of vreg v1) (Rgl?.region_of vreg v2)))
    (ensures (fun h0 _ h1 ->
      Rgl?.r_inv vreg h1 v2 /\
      Rgl?.r_repr vreg h0 v2 == Rgl?.r_repr vreg h1 v2))
let free_does_not_affect_the_other v1 v2 =
  assert (B.loc_disjoint (RV.loc_rvector v1) (RV.loc_rvector v2));
  RV.free v1
