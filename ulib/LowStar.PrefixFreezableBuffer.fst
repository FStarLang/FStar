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

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST


(*
 * Implementation for LowStar.PrefixfreezableBuffer
 *)

#set-options "--max_fuel 0 --max_ifuel 0"

(****** Functions that will come from LowStar.Endianness ******)

/// Read a sequence of bytes as a nat in the little-endian order

assume val le_to_n (s:Seq.seq u8) : Tot nat
assume val le_to_n_zeros (s:Seq.seq u8)  //if everything in a sequence is 0, then le_to_n of first 4 bytes is 0
  : Lemma
    (requires
      Seq.length s >= 4 /\
      (forall (i:nat). i < Seq.length s ==> Seq.index s i == 0uy))
    (ensures le_to_n (Seq.slice s 0 4) == 0)


/// Storing a u32 in the first 4 bytes of the input buffer
///
/// Precondition requires the callers to prove that it is consistent with the preorder
///
/// The following load and store will be more general in LowStar.Endianness in terms of indices

assume
val store32_le
  (#rrel #rel:srel u8)
  (b:mbuffer u8 rrel rel)
  (i:u32)
  : Stack
    unit
    (requires fun h ->
      live h b /\
      4 <= length b /\
      (forall (s:Seq.seq u8).
         (Seq.length s == length b /\
	  (forall (i:nat). 4 <= i /\ i < length b ==> Seq.index s i == Seq.index (as_seq h b) i) /\
	  le_to_n (Seq.slice s 0 4) == U32.v i) ==>
	 (rel (as_seq h b) s)))
    (ensures  fun h0 _ h1 ->
      live h1 b /\
      modifies (loc_buffer b) h0 h1 /\
      le_to_n (Seq.slice (as_seq h1 b) 0 4) == U32.v i /\
      (forall (k:nat).{:pattern (Seq.index (as_seq h1 b) k)}
         (4 <= k /\ k < length b) ==> Seq.index (as_seq h1 b) k == Seq.index (as_seq h0 b) k))


/// Loading first 4 bytes of the buffer as a u32

assume
val load32_le
  (#rrel #rel:srel u8)
  (b:mbuffer u8 rrel rel)
  : Stack
    u32
    (requires fun h ->
      live h b /\
      4 <= length b)
    (ensures  fun h0 r h1 ->
      h0 == h1 /\
      U32.v r == le_to_n (Seq.slice (as_seq h1 b) 0 4))

(****** End LowStar.Endianness functions ******)


let frozen_until s = le_to_n (Seq.slice s 0 4)

let prefix_freezable_preorder = pre

let prefix_freezable_preorder_elim _ _ = ()

private let update_frozen_until_alloc
  (b:mbuffer u8 prefix_freezable_preorder prefix_freezable_preorder)
  : Stack
    unit
    (requires fun h ->
      live h b /\
      length b >= 4 /\
      frozen_until (as_seq h b) == 0)
    (ensures  fun h0 _ h1 ->
      live h1 b /\
      modifies (loc_buffer b) h0 h1 /\
      frozen_until (as_seq h1 b) == 4 /\
      witnessed b (frozen_until_at_least 4))
  = store32_le b 4ul;
    witness_p b (frozen_until_at_least 4)

let gcmalloc r len =
  let h0 = ST.get () in
  
  let b = mgcmalloc #_ #prefix_freezable_preorder r 0uy (U32.add len 4ul) in

  let h = ST.get () in le_to_n_zeros (as_seq h b);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let malloc r len =
  let h0 = ST.get () in
  
  let b = mmalloc #_ #prefix_freezable_preorder r 0uy (U32.add len 4ul) in

  let h = ST.get () in le_to_n_zeros (as_seq h b);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let alloca len =
  let h0 = ST.get () in
  
  let b = malloca #_ #prefix_freezable_preorder 0uy (U32.add len 4ul) in

  let h = ST.get () in le_to_n_zeros (as_seq h b);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let upd b i v =
  recall_p b (frozen_until_at_least 4);
  upd b i v

let freeze b i =
  recall_p b (frozen_until_at_least 4);
  store32_le b i;
  witness_p b (frozen_until_at_least (U32.v i))

let frozen_until_st b = load32_le b

let witness_slice b i j snap =
  witness_p b (slice_is i j snap)

let recall_slice b i j snap =
  recall_p b (slice_is i j snap)

let witness_frozen_until b n =
  witness_p b (frozen_until_at_least n)

let recall_frozen_until b n =
  recall_p b (frozen_until_at_least n)

let recall_frozen_until_default b =
  recall_p b (frozen_until_at_least 4)
