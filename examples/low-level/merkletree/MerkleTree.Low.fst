module MerkleTree.Low

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

assume type elem: eqtype u#0
assume type hash: eqtype u#0
assume val elem_init: elem
assume val hash_init: hash
let elem_buf = B.buffer elem
let hash_buf = B.buffer hash

assume val hash_from_elem: elem -> Tot hash
assume val hash_from_hashes: hash -> hash -> Tot hash

// This number says that the maximum number of values is (2^32 - 1)
let max_num_elts_lg = 32

/// Allocation by power of two

// TODO: optimize using bit manipulation
val is_pow2: nat -> Tot bool
let rec is_pow2 n =
  if n = 0 then false
  else if n = 1 then true
  else (n % 2 = 0 && is_pow2 (n / 2))

val pow2_is_pow2:
  n:nat ->
  Lemma (is_pow2 (pow2 n))
	[SMTPat (is_pow2 (pow2 n))]
let rec pow2_is_pow2 n =
  if n = 0 then ()
  else pow2_is_pow2 (n - 1)

val alloc_sz_lg: 
  nelts:nat{nelts > 0} -> 
  GTot (sz:nat{if sz = 0 
    then nelts <= pow2 sz
    else pow2 (sz - 1) < nelts && nelts <= pow2 sz})
let rec alloc_sz_lg nelts =
  if nelts = 1 then 0
  else if nelts % 2 = 0 then 1 + alloc_sz_lg (nelts / 2)
  else 1 + alloc_sz_lg ((nelts + 1) / 2)

val pow2_interval_unique:
  n:nat -> sz1:nat{sz1 > 0} -> sz2:nat{sz2 > 0} ->
  Lemma (requires (pow2 (sz1 - 1) < n && n <= pow2 sz1 &&
		  pow2 (sz2 - 1) < n && n <= pow2 sz2))
	(ensures (sz1 = sz2))
let pow2_interval_unique n sz1 sz2 =
  if sz1 > sz2 
  then Math.Lemmas.pow2_le_compat (sz1 - 1) sz2
  else if sz1 < sz2
  then Math.Lemmas.pow2_le_compat (sz2 - 1) sz1
  else ()

val alloc_sz_lg_inv:
  nelts:nat -> sz:nat{sz > 0} ->
  Lemma (requires (pow2 (sz - 1) < nelts && nelts <= pow2 sz))
	(ensures (alloc_sz_lg nelts = sz))
let alloc_sz_lg_inv nelts sz =
  pow2_interval_unique nelts sz (alloc_sz_lg nelts)

val alloc_sz_lg_pow2:
  nelts:nat ->
  Lemma (requires (is_pow2 nelts))
	(ensures (nelts = pow2 (alloc_sz_lg nelts)))
let rec alloc_sz_lg_pow2 nelts =
  if nelts = 1 then ()
  else if nelts % 2 = 0 then alloc_sz_lg_pow2 (nelts / 2)
  else ()

val alloc_sz_lg_pow2_inc:
  nelts:nat ->
  Lemma (requires (is_pow2 nelts))
	(ensures (alloc_sz_lg (nelts + 1) = 1 + alloc_sz_lg nelts))
#set-options "--z3rlimit 10"
let rec alloc_sz_lg_pow2_inc nelts =
  if nelts = 1 then ()
  else if nelts % 2 = 0 then alloc_sz_lg_pow2_inc (nelts / 2)
  else ()

val alloc_sz_lg_not_pow2_inc:
  nelts:nat{nelts > 0} ->
  Lemma (requires (~ (is_pow2 nelts)))
	(ensures (alloc_sz_lg nelts = 
       		 alloc_sz_lg (nelts + 1)))
let alloc_sz_lg_not_pow2_inc nelts =
  let sz1 = alloc_sz_lg nelts in
  let sz2 = alloc_sz_lg (nelts + 1) in
  if sz1 > sz2 
  then Math.Lemmas.pow2_le_compat (sz1 - 1) sz2
  else if sz1 < sz2
  then (Math.Lemmas.pow2_le_compat (sz2 - 1) sz1;
       assert (nelts = pow2 sz1))
  else ()

/// Low-level Merkle tree data structure

noeq type merkle_tree =
| MT: nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg} -> 
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      values:elem_buf{B.length values = pow2 (alloc_sz_lg nelts)} ->
      // The actual number of internal roots should be equal to 
      // the number of "set" bits of `nelts`.
      iroots:hash_buf{B.length iroots = max_num_elts_lg} ->
      merkle_tree

// let mtree_ptr = B.pointer merkle_tree

/// Initialization

val create_merkle_tree: unit -> HST.St merkle_tree
let create_merkle_tree _ =
  MT 1 (B.malloc Monotonic.HyperHeap.root elem_init 1ul)
     (B.malloc Monotonic.HyperHeap.root hash_init (UInt32.uint_to_t max_num_elts_lg))

// val init_merkle_tree: unit -> HST.St mtree_ptr
// let init_merkle_tree _ =
//   B.malloc Monotonic.HyperHeap.root (create_merkle_tree ()) 1ul

/// Insertion

val mt_is_full: merkle_tree -> Tot bool
let mt_is_full mt = MT?.nelts mt >= pow2 max_num_elts_lg - 1

val insert_nelts: 
  nelts:nat{nelts < pow2 max_num_elts_lg - 1} ->
  Tot (inelts:nat{inelts < pow2 max_num_elts_lg})
let insert_nelts nelts =
  nelts + 1

// TODO: so inefficient if recursive; maybe it's already defined somewhere?
val buffer_copy:
  #a:Type -> l1:nat{l1 > 0} -> b1:B.buffer a{B.length b1 = l1} ->
  b2:B.buffer a{B.length b2 >= l1} ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 b1 /\ B.live h0 b2 /\ B.disjoint b1 b2))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer b2) h0 h1 /\
	   B.as_seq h1 b1 == S.slice (B.as_seq h1 b2) 0 l1))
let rec buffer_copy #a l1 b1 b2 =
  admit () // Do we have iteration for buffers, or something like `memcpy`?

val insert_values:
  nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg - 1} -> 
  vs:elem_buf{B.length vs = pow2 (alloc_sz_lg nelts)} ->
  elem -> 
  HST.ST (ivs:elem_buf{B.length ivs = pow2 (alloc_sz_lg (insert_nelts nelts))})
	 (requires (fun h0 -> B.live h0 vs))
	 (ensures (fun h0 nvs h1 -> B.live h1 nvs)) // TODO: definitely need stronger postconditions
let insert_values nelts vs e =
  if is_pow2 nelts 
  then (// TODO: need a fine-grained control of indexing and allocation
       assume (2 * nelts <= pow2 (max_num_elts_lg) - 1);
       
       let hh0 = HST.get () in
       let nvs = B.malloc Monotonic.HyperHeap.root elem_init (UInt32.uint_to_t (2 * nelts)) in
       B.live_unused_in_disjoint hh0 vs nvs;
       alloc_sz_lg_pow2 nelts;
       buffer_copy nelts vs nvs;

       B.upd nvs (UInt32.uint_to_t nelts) e;

       // B.free vs; // TODO: `B.free` the previous values buffer

       alloc_sz_lg_pow2_inc nelts; nvs)
  else (assume (nelts < pow2 (alloc_sz_lg nelts));
       B.upd vs (UInt32.uint_to_t nelts) e;
       alloc_sz_lg_not_pow2_inc nelts;
       vs)

val insert_iroots:
  irs:hash_buf{B.length irs = max_num_elts_lg} ->
  elem -> Tot (nirs:hash_buf{B.length nirs = max_num_elts_lg})
let insert_iroots irs e =
  admit ()

val insert: 
  mt:merkle_tree -> e:elem -> 
  HST.ST merkle_tree
	 (requires (fun h0 -> 
	   B.live h0 (MT?.values mt) /\
	   B.live h0 (MT?.iroots mt) /\
	   ~ (mt_is_full mt)))
	 (ensures (fun h0 _ h1 -> true))
let insert mt e =
  MT (insert_nelts (MT?.nelts mt))
     (insert_values (MT?.nelts mt) (MT?.values mt) e)
     (insert_iroots (MT?.iroots mt) e)

/// Getting the Merkle root



