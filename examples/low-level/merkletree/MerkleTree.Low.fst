module MerkleTree.Low

open FStar.All
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

val get_values_alloc_size_lg: 
  nelts:nat{nelts > 0} -> 
  GTot (sz:nat{if sz = 0 
    then nelts <= pow2 sz
    else pow2 (sz - 1) < nelts && nelts <= pow2 sz})
let rec get_values_alloc_size_lg nelts =
  if nelts = 1 then 0
  else if nelts % 2 = 0 then 1 + get_values_alloc_size_lg (nelts / 2)
  else 1 + get_values_alloc_size_lg ((nelts + 1) / 2)

noeq type merkle_tree =
| MT: nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg} -> 
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      values:elem_buf{B.length values = pow2 (get_values_alloc_size_lg nelts)} ->
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

// TODO: optimize using bit manipulation
val is_pow2: nat -> Tot bool
let rec is_pow2 n =
  if n = 0 then false
  else if n = 1 then true
  else (n % 2 = 0 && is_pow2 (n / 2))

val get_values_alloc_size_lg_eq:
  nelts:nat{nelts > 0} ->
  Lemma (requires (~ (is_pow2 nelts)))
	(ensures (get_values_alloc_size_lg nelts = 
       		 get_values_alloc_size_lg (nelts + 1)))
let get_values_alloc_size_lg_eq nelts =
  admit ()

val insert_values:
  nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg - 1} -> 
  vs:elem_buf{B.length vs = pow2 (get_values_alloc_size_lg nelts)} ->
  elem -> 
  HST.ST (ivs:elem_buf{B.length ivs = pow2 (get_values_alloc_size_lg (insert_nelts nelts))})
	 (requires (fun h0 -> B.live h0 vs))
	 (ensures (fun h0 nvs h1 -> B.live h1 nvs))
#set-options "--z3rlimit 10"
let insert_values nelts vs e =
  if is_pow2 nelts then admit ()
  else (assume (nelts < pow2 (get_values_alloc_size_lg nelts));
       B.upd vs (UInt32.uint_to_t nelts) e;
       get_values_alloc_size_lg_eq nelts;
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



