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

module E = FStar.Endianness
module LE = LowStar.Endianness


(*
 * Implementation for LowStar.PrefixfreezableBuffer
 *)

#set-options "--max_fuel 0 --max_ifuel 0"

let le_to_n s = E.le_to_n s

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
  = LE.store32_le_i b 0ul 4ul;
    witness_p b (frozen_until_at_least 4)

let gcmalloc r len =
  let h0 = ST.get () in
  
  let b = mgcmalloc #_ #prefix_freezable_preorder r 0uy (U32.add len 4ul) in

  let h = ST.get () in E.le_to_n_zeros (Seq.slice (as_seq h b) 0 4);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let malloc r len =
  let h0 = ST.get () in
  
  let b = mmalloc #_ #prefix_freezable_preorder r 0uy (U32.add len 4ul) in

  let h = ST.get () in E.le_to_n_zeros (Seq.slice (as_seq h b) 0 4);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let alloca len =
  let h0 = ST.get () in
  
  let b = malloca #_ #prefix_freezable_preorder 0uy (U32.add len 4ul) in

  let h = ST.get () in E.le_to_n_zeros (Seq.slice (as_seq h b) 0 4);

  assert (fresh_loc (loc_buffer b) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
  update_frozen_until_alloc b;
  b

let upd b i v =
  recall_p b (frozen_until_at_least 4);
  upd b i v

(*
 * This lemma handles the mismatch between the style of the spec
 *   in LE.store_pre and LE.store_post, and the preorder of PrefixFreezableBuffers
 * Basically the sequence library is missing a lemma that eliminates
 *   equality on two slices to some equality on the base sequences
 *)
let le_pre_post_index
  (s1 s2:Seq.seq u8)
  : Lemma
    (ensures
      (Seq.length s1 == Seq.length s2 /\
       Seq.length s1 >= 4 /\
       Seq.equal (Seq.slice s1 0 0) (Seq.slice s2 0 0) /\
       Seq.equal (Seq.slice s1 4 (Seq.length s1))
                 (Seq.slice s2 4 (Seq.length s2))) ==>

      (forall (i:nat).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
         (i >= 4 /\ i < Seq.length s1) ==>
         (Seq.index s1 i == Seq.index s2 i)))
  = assert (forall (s:Seq.seq u8).
              Seq.length s >= 4 ==>
	      (forall (i:nat).
	         (i >= 4 /\ i < Seq.length s) ==>
	         Seq.index s i == Seq.index (Seq.slice s 4 (Seq.length s)) (i - 4)))
               
let freeze b i =
  recall_p b (frozen_until_at_least 4);
  FStar.Classical.forall_intro_2 le_pre_post_index;
  LE.store32_le_i b 0ul i;
  witness_p b (frozen_until_at_least (U32.v i))

let frozen_until_st b = LE.load32_le_i b 0ul

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
