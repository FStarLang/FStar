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

module LowStar.FreezableBuffer

open FStar.HyperStack.ST

include LowStar.Monotonic.Buffer

module P = FStar.Preorder
module G = FStar.Ghost

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Seq = FStar.Seq

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*
 * A library for freezable buffers of u8
 * 
 * It maintains the current frozen-upto index (a u32) in the first 4 bytes of the buffer
 *
 * Clients can call `freeze` to freeze upto an input index
 *   after which the buffer cannot be mutated until that index
 *
 * We call this value `w` in the code below
 *)

type u8 = U8.t
type u32 = U32.t

#set-options "--max_fuel 0 --max_ifuel 0"

/// View a byte sequence as a little-endian natural number
/// Only for spec purposes, will see if we need to provide more lemmas for it

assume val le_to_n (s:Seq.seq u8) : Tot nat


/// Read the w index in the sequence

unfold let get_w (s:Seq.seq u8{Seq.length s >= 4}) = le_to_n (Seq.slice s 0 4)


/// Preorder for a freezable buffer
/// Essentially w increases monotonically and contents upto w remain same

let freezable_preorder : P.preorder (Seq.seq u8) =
  fun s1 s2 ->
  Seq.length s1 == Seq.length s2 /\  //sequence length remains same
  (let len = Seq.length s1 in
   (len >= 4 ==>  //if length >= 4 then
    (let w1 = get_w s1 in
     let w2 = get_w s2 in
     ((w1 >= 4 /\ w1 <= len) ==>  //if first 4 bytes of s1 viewed as a nat < length of the buffer then
      (w2 <= len /\ w1 <= w2 /\  //w2 increases monotonically, but remains <= len
       (forall (i:nat).{:pattern Seq.index s2 i} (i >= 4 /\ i < w1) ==> Seq.index s2 i == Seq.index s1 i)  //and the buffer until w1 remains same
       )))))


/// Predicate that w >= n is stable

let w_pred (n:nat) : spred u8 =
  fun s -> n >= 4 /\ Seq.length s >= 4 /\ get_w s >= n /\ get_w s <= Seq.length s


/// And so are the contents of a slice [i, j) within w

let frozen_slice_pred (i j:u32) (snap:G.erased (Seq.seq u8)) : spred u8 =
  fun s ->
  let len = Seq.length s in
   len >= 4 /\
   (let w = get_w s in
    let i = U32.v i in
    let j = U32.v j in
    let snap = G.reveal snap in
    (i >= 4 /\ i <= j /\ j <= w /\ w <= len /\ Seq.length snap == j - i /\ Seq.equal (Seq.slice s i j) snap))


/// Test for their stability

[@"uninterpreted_by_smt"]
abstract private let test_stable
  (n:nat)
  (i j:u32) (snap:G.erased (Seq.seq u8)) =
  assert (stable_on (w_pred n) freezable_preorder);
  assert (stable_on (frozen_slice_pred i j snap) freezable_preorder)


/// Length of a freezable buffer is always >= 4

private let fbuffer0 =
  fb:mbuffer u8 freezable_preorder freezable_preorder{length fb >= 4}

/// We also witness that the value of w >= 4

let fbuffer = fb:fbuffer0{witnessed fb (w_pred 4)}

unfold let lfbuffer (len:u32) = fb:fbuffer{length fb == U32.v len + 4}


/// A store32_le function that stores a u32 in a bytes buffer in le format
/// Is it native in Kremlin?

assume private val store32_le (fb:fbuffer0) (w:u32)
  : Stack unit (requires (fun h0      ->
                          live h0 fb /\
			  U32.v w <= length fb /\
			  U32.v w >= get_w (as_seq h0 fb)))
               (ensures  (fun h0 _ h1 ->
	                  live h1 fb /\
			  modifies (loc_buffer fb) h0 h1 /\
			  get_w (as_seq h1 fb) == U32.v w /\
			  (forall (i:nat).{:pattern (Seq.index (as_seq h1 fb) i)}
			     (i >= 4 /\ i < length fb) ==> Seq.index (as_seq h1 fb) i == Seq.index (as_seq h0 fb) i)))


/// Since store32_le is assumed, following test makes sure that it is still consistent with the preorder

[@"uninterpreted_by_smt"]
private let test_store32_le (fb:fbuffer0) (w:u32)
  : Stack unit (requires (fun h0      ->
                          live h0 fb /\
			  U32.v w <= length fb /\
			  U32.v w >= get_w (as_seq h0 fb)))
               (ensures  (fun h0 _ h1 -> True))
  = let h0 = HST.get () in    
    store32_le fb w;    
    let h1 = HST.get () in
    assert (freezable_preorder (as_seq h0 fb) (as_seq h1 fb))


/// Another test to make sure that we are not introducing any inconsistency

[@expect_failure]
private let test_store32_le1 (fb:fbuffer0) (w:u32)
  : Stack unit (requires (fun h0      ->
                          live h0 fb /\
			  U32.v w <= length fb /\
			  U32.v w >= get_w (as_seq h0 fb)))
               (ensures  (fun h0 _ h1 -> True))
  = store32_le fb w;    
    assert False


/// Precondition corresponding to malloc_pre

let fb_malloc_pre (r:HS.rid) (len:U32.t) =
  UInt.size (U32.v len + 4) 32 /\
  malloc_pre r len


/// Postcondition for creation of freezable buffers
/// w is set to 4 (in u32) and rest of the contents are under-specified

unfold let fb_alloc_post_mem_common (h0:HS.mem) (fb:fbuffer) (h1:HS.mem) =
  live h1 fb /\
  unused_in fb h0 /\
  Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
  HS.get_tip h1 == HS.get_tip h0 /\
  modifies loc_none h0 h1 /\
  get_w (as_seq h1 fb) == 4

private let update_w_post_alloc (fb:fbuffer0)
  : Stack unit (requires (fun h0 ->
                          live h0 fb /\
			  get_w (as_seq h0 fb) == 0))
               (ensures  (fun h0 _ h1 ->
	                  live h1 fb /\
			  modifies (loc_buffer fb) h0 h1 /\
			  get_w (as_seq h1 fb) == 4 /\
			  witnessed fb (w_pred 4)))
  = store32_le fb 4ul;
    witness_p fb (w_pred 4)


/// memory-managed freezable bufer

let fgcmalloc (r:HS.rid) (len:u32)
  : ST (fb:lfbuffer len{frameOf fb == r /\ recallable fb})
       (requires (fun _       -> fb_malloc_pre r len))
       (ensures  fb_alloc_post_mem_common)
  = let h0 = HST.get () in
  
    let fb = mgcmalloc #_ #freezable_preorder r 0uy (U32.add len 4ul) in

    let h = HST.get () in
    assume (le_to_n (Seq.slice (as_seq h fb) 0 4) == 0);  //since le_to_n is an assume val

    assert (fresh_loc (loc_buffer fb) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
    update_w_post_alloc fb;
    fb


/// hand-managed freezable buffer in an eternal region r

let fmalloc (r:HS.rid) (len:u32)
  : ST (fb:lfbuffer len{frameOf fb == r /\ freeable fb})
       (requires fun _ -> fb_malloc_pre r len)
       (ensures fb_alloc_post_mem_common)
  = let h0 = HST.get () in
  
    let fb = mmalloc #_ #freezable_preorder r 0uy (U32.add len 4ul) in

    let h = HST.get () in
    assume (le_to_n (Seq.slice (as_seq h fb) 0 4) == 0);  //since le_to_n is an assume val

    assert (fresh_loc (loc_buffer fb) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
    update_w_post_alloc fb;
    fb


/// Stack allocated freezable buffer

unfold let fb_alloca_pre (len:U32.t) =
  UInt.size (U32.v len + 4) 32 /\
  alloca_pre len
  
let falloca (len:u32)
  : StackInline (lfbuffer len)
                (requires (fun _        -> fb_alloca_pre len))
	        (ensures  (fun h0 fb h1 -> fb_alloc_post_mem_common h0 fb h1 /\ frameOf fb == HS.get_tip h0))
  = let h0 = HST.get () in
  
    let fb = malloca #_ #freezable_preorder 0uy (U32.add len 4ul) in

    let h = HST.get () in
    assume (le_to_n (Seq.slice (as_seq h fb) 0 4) == 0);  //since le_to_n is an assume val

    assert (fresh_loc (loc_buffer fb) h0 h);  //TODO: necessary for firing modifies_remove_new_locs lemma?
    update_w_post_alloc fb;
    fb


/// update function

let fupd (fb:fbuffer) (i:u32) (v:u8)
  : Stack unit (requires (fun h0 -> 
                          live h0 fb /\ U32.v i < length fb /\
                          U32.v i >= get_w (as_seq h0 fb)))
	       (ensures  (fun h0 _ h1 ->
		          (not (g_is_null fb)) /\
			  modifies (loc_buffer fb) h0 h1 /\
			  live h1 fb /\
			  get_w (as_seq h0 fb) == get_w (as_seq h1 fb) /\
			  as_seq h1 fb == Seq.upd (as_seq h0 fb) (U32.v i) v))
  = recall_p fb (w_pred 4);
    upd fb i v


/// Freeze the buffer upto i
/// Also provide the witnessed w_pred for this i

let freeze (fb:fbuffer) (i:u32)
  : Stack unit (requires (fun h0 ->
                          live h0 fb /\ U32.v i < length fb /\ U32.v i >= get_w (as_seq h0 fb)))
	       (ensures  (fun h0 _ h1 ->
		          (not (g_is_null fb)) /\
			  modifies (loc_buffer fb) h0 h1 /\
			  live h1 fb /\
			  get_w (as_seq h1 fb) == U32.v i /\
			  witnessed fb (w_pred (U32.v i)) /\
			  (forall (k:nat).{:pattern (Seq.index (as_seq h1 fb) k)}
			     (k >= 4 /\ k < length fb) ==> Seq.index (as_seq h1 fb) k == Seq.index (as_seq h0 fb) k)))
  = recall_p fb (w_pred 4);
    store32_le fb i;
    witness_p fb (w_pred (U32.v i))


/// Clients can witness contents of some [i, j) within the range [4, w)

let witness_slice (fb:fbuffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : Stack unit (requires (fun h0      -> frozen_slice_pred i j snap (as_seq h0 fb)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed fb (frozen_slice_pred i j snap)))
  = witness_p fb (frozen_slice_pred i j snap)


/// Clients can recall contents of some previously witnessed slice

let recall_slice (fb:fbuffer) (i j:u32) (snap:G.erased (Seq.seq u8))
  : Stack unit (requires (fun h0      -> (recallable fb \/ live h0 fb) /\ witnessed fb (frozen_slice_pred i j snap)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ frozen_slice_pred i j snap (as_seq h1 fb)))
  = recall_p fb (frozen_slice_pred i j snap)


/// Clients can also witness value of w

let witness_w (fb:fbuffer) (n:nat)
  : Stack unit (requires (fun h0      -> w_pred n (as_seq h0 fb)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ witnessed fb (w_pred n)))
  = witness_p fb (w_pred n)
  

/// And then recall previously witnessed value of w

let recall_w (fb:fbuffer) (n:nat)
  : Stack unit (requires (fun h0      -> (recallable fb \/ live h0 fb) /\ witnessed fb (w_pred n)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ w_pred n (as_seq h1 fb)))
  = recall_p fb (w_pred n)


/// By-default clients can recall that w >= 4 and w <= length b

let recall_w_default (fb:fbuffer)
  : Stack unit (requires (fun h0      -> (recallable fb \/ live h0 fb)))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ w_pred 4 (as_seq h1 fb)))
  = recall_p fb (w_pred 4)
