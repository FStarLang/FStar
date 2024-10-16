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

module LowStar.PrefixFreezableBuffer

open FStar.HyperStack.ST

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost

module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

(*
 * A library for prefix freezable buffers of elements of type u8
 *
 * Our monotonicity theory does not easily support preorders and predicates over
 *   multiple references. So instead of keeping the frozen-until counter in a
 *   separate (ghost) reference, the library maintains the frozen-until counter (a u32)
 *   in the first four bytes of the buffer itself
 *
 * Buffer contents up to the frozen-until counter are stable and clients can witness
 *   and recall them
 *
 *)

type u8 = UInt8.t
type u32 = U32.t

#set-options "--max_fuel 0 --max_ifuel 0"


/// This is the frozen until index in the sequence representation of a PrefixFreezableBuffer

val le_to_n (s:Seq.seq u8) : Tot nat

let frozen_until (s:Seq.seq u8{Seq.length s >= 4}) = le_to_n (Seq.slice s 0 4)


/// Preorder for PrefixFreezableBuffers

private unfold let pre (s1 s2:Seq.seq u8) =
  Seq.length s1 == Seq.length s2 /\  //lengths are same
  (let len = Seq.length s1 in
   len >= 4 ==>  //if length >= 4 then
   (let frozen_until1 = frozen_until s1 in
    let frozen_until2 = frozen_until s2 in
    (4 <= frozen_until1 /\ frozen_until1 <= len) ==>  //if frozen_until1 is in the range [4, len] then
    (frozen_until1 <= frozen_until2 /\ frozen_until2 <= len /\  //frozen until index increases monotonically, but remains <= len
     (forall (i:nat).{:pattern Seq.index s2 i}
        (4 <= i /\ i < frozen_until1) ==> Seq.index s2 i == Seq.index s1 i))))  //and the contents until frozen_until1 remain same


val prefix_freezable_preorder : srel u8

/// Clients can call the following lemma to reveal the preorder

val prefix_freezable_preorder_elim (s1 s2:Seq.seq u8)
  : Lemma (prefix_freezable_preorder s1 s2 <==> pre s1 s2)


/// Predicate for the frozen_until index being at least n
///
/// It is stable w.r.t. the prefix_freezable_preorder

let frozen_until_at_least (n:nat) : spred u8 =
  fun s -> Seq.length s >= 4 /\  //it follows from the inequalities below, but we need it for typing of frozen_until
  
  4 <= n /\ n <= frozen_until s /\ frozen_until s <= Seq.length s


/// Predicate for the frozen slice with indices in the [4, frozen_until) range
///
/// It is stable w.r.t. the prefix_freezable_preorder

let slice_is (i j:u32) (snap:G.erased (Seq.seq u8)) : spred u8 =
  fun s -> let len = Seq.length s in len >= 4 /\  //for typing of frozen_until
  (let frozen_until = frozen_until s in
   let i = U32.v i in
   let j = U32.v j in
   let snap = G.reveal snap in
   4 <= i /\ i <= j /\ j <= frozen_until /\ frozen_until <= len /\
   Seq.length snap == j - i /\
   Seq.equal (Seq.slice s i j) snap)


/// Buffer type for PrefixfreezableBuffers
///
/// And abbreviation for the length indexed version

type buffer =
  b:mbuffer u8 (prefix_freezable_preorder) (prefix_freezable_preorder)
    {length b >= 4 /\ b `witnessed` frozen_until_at_least 4}

unfold let lbuffer (len:u32) =
  b:buffer{length b == U32.v len + 4}


/// Allocation precondition for prefix freezable buffers adds an additional constraint
/// that the input length + 4 must fit in u32

unfold let malloc_pre (r:HS.rid) (len:u32) =
  UInt.size (U32.v len + 4) 32 /\ malloc_pre r len


/// The postcondition is also different in that there is no initializer
/// and an additional predicate for the initial value of the frozen_until_index

unfold let alloc_post_mem_common
  (h0:HS.mem) (b:buffer) (h1:HS.mem)
  = live h1 b /\
    unused_in b h0 /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    HS.get_tip h1 == HS.get_tip h0 /\
    modifies loc_none h0 h1 /\
    frozen_until (as_seq h1 b) == 4


/// Allocation functions

val gcmalloc (r:HS.rid) (len:u32)
  : ST (b:lbuffer len{frameOf b == r /\ recallable b})
       (requires fun _ -> malloc_pre r len)
       (ensures  alloc_post_mem_common)

val malloc (r:HS.rid) (len:u32)
  : ST
    (b:lbuffer len{frameOf b == r /\ freeable b})
    (requires fun _ -> malloc_pre r len)
    (ensures  alloc_post_mem_common)

unfold let alloca_pre (len:U32.t) =  //precondition for stack allocated prefix freezable buffers
  UInt.size (U32.v len + 4) 32 /\ alloca_pre len
  
val alloca (len:u32)
  : StackInline
    (lbuffer len)
    (requires fun _ -> alloca_pre len)
    (ensures  fun h0 b h1 ->
      alloc_post_mem_common h0 b h1 /\ frameOf b == HS.get_tip h0)


/// Update function
///
/// Input index must be geq than the current frozen until index

val upd (b:buffer) (i:u32) (v:u8)
  : Stack
    unit
    (requires fun h ->
      live h b /\ U32.v i < length b /\
      U32.v i >= frozen_until (as_seq h b))
    (ensures  fun h0 _ h1 ->
      (not (g_is_null b)) /\
      modifies (loc_buffer b) h0 h1 /\
      live h1 b /\
      frozen_until (as_seq h0 b) == frozen_until (as_seq h1 b) /\
      as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v)


/// API to freeze the buffer up-to the input index
///
/// Also provides a witnessed frozen_until_at_least predicate

val freeze (b:buffer) (i:u32)
  : Stack
    unit
    (requires fun h ->
      live h b /\
      U32.v i <= length b /\
      U32.v i >= frozen_until (as_seq h b))
    (ensures  fun h0 _ h1 ->
      (not (g_is_null b)) /\
      modifies (loc_buffer b) h0 h1 /\
      live h1 b /\
      frozen_until (as_seq h1 b) == U32.v i /\
      b `witnessed` frozen_until_at_least (U32.v i) /\
      (forall (k:nat).{:pattern (Seq.index (as_seq h1 b) k)}  //contents from [4, len) remain same
         (4 <= k /\ k < length b) ==>
         (Seq.index (as_seq h1 b) k == Seq.index (as_seq h0 b) k)))


/// API for querying the current frozen until index

val frozen_until_st (b:buffer)
  : Stack
    u32
    (requires fun h -> live h b)
    (ensures  fun h0 r h1 ->
      h0 == h1 /\
      U32.v r == frozen_until (as_seq h1 b))


/// Clients can witness contents of some [i, j) within the range [4, frozen_until)

val witness_slice (b:buffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : Stack
    unit
    (requires fun h -> slice_is i j snap (as_seq h b))
    (ensures  fun h0 _ h1 ->
      h0 == h1 /\
      b `witnessed` slice_is i j snap)


/// Clients can recall contents of some previously witnessed slice

val recall_slice (b:buffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : Stack
    unit
    (requires fun h ->
      (recallable b \/ live h b) /\
      b `witnessed` slice_is i j snap)
    (ensures  fun h0 _ h1 ->
      h0 == h1 /\
      slice_is i j snap (as_seq h1 b))


/// Clients can also witness the value of the frozen until index

val witness_frozen_until (b:buffer) (n:nat)
  : Stack
    unit 
    (requires fun h -> frozen_until_at_least n (as_seq h b))
    (ensures  fun h0 _ h1 ->
      h0 == h1 /\
      b `witnessed` frozen_until_at_least n)
  

/// And then recall the previously witnessed value of the frozen until index

val recall_frozen_until (b:buffer) (n:nat)
  : Stack
    unit
    (requires fun h ->
      (recallable b \/ live h b) /\
      b `witnessed` frozen_until_at_least n)
    (ensures  fun h0 _ h1 ->
      h0 == h1 /\
      frozen_until_at_least n (as_seq h1 b))


/// By-default, clients can recall that 4 <= frozen until index <= length b

val recall_frozen_until_default (b:buffer)
  : Stack
    unit
    (requires fun h -> recallable b \/ live h b)
    (ensures  fun h0 _ h1 ->
      h0 == h1 /\
      frozen_until_at_least 4 (as_seq h1 b))
