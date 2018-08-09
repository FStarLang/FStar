module MerkleTree.Low

// TODO1: Use `EverCrypt.Hash` directly
// open EverCrypt.Hash

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq
open FStar.Integers
open FStar.Ghost

open MerkleTree.High
open LowStar.Vector
open LowStar.BufVector

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module MHS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap

module B = LowStar.Buffer
module V = LowStar.Vector
module BV = LowStar.BufVector
module S = FStar.Seq

module High = MerkleTree.High

module U32 = FStar.UInt32
module U8 = FStar.UInt8

type hash = B.buffer uint8_t
type hash_vec = BV.buf_vector uint8_t

// TODO1: When `EverCrypt.Hash` is connected if we define it.
assume val hash_from_hashes: 
  src1:hash -> src2:hash -> dst:hash -> 
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_liveness hash_size h0 src1 /\
	   BV.buffer_inv_liveness hash_size h0 src2 /\
	   BV.buffer_inv_liveness hash_size h0 dst))
	 (ensures (fun h0 _ h1 ->
	   // memory safety
	   modifies (B.loc_buffer dst) h0 h1 /\
	   // correctness
	   High.hash_from_hashes (B.as_seq h1 src1) (B.as_seq h1 src2) = 
	   B.as_seq h1 dst)) 

/// Utilities

val modifies_union_weakened_left:
  s1:loc -> s2:loc ->
  h1:HS.mem -> h2:HS.mem ->
  Lemma (requires (modifies s1 h1 h2))
	(ensures (modifies (loc_union s1 s2) h1 h2))
let modifies_union_weakened_left s1 s2 h1 h2 =
  loc_includes_union_l s1 s2 s1

val modifies_union_weakened_right:
  s1:loc -> s2:loc ->
  h1:HS.mem -> h2:HS.mem ->
  Lemma (requires (modifies s2 h1 h2))
	(ensures (modifies (loc_union s1 s2) h1 h2))
let modifies_union_weakened_right s1 s2 h1 h2 =
  loc_includes_union_l s1 s2 s2

/// Low-level Merkle tree data structure

noeq type merkle_tree =
| MT: values:hash_vec ->
      iroots:hash_vec{V.size_of iroots = 32ul} ->
      merkle_tree

let mt_ptr = B.pointer merkle_tree

val mt_lift: 
  h:HS.mem -> mt:merkle_tree{
    BV.bv_inv_liveness hash_size h (MT?.values mt) /\
    BV.bv_inv_liveness hash_size h (MT?.iroots mt)} ->
  GTot High.merkle_tree
let mt_lift h mt =
  High.MT U32.n
	  (BV.as_seq h hash_size (MT?.values mt))
	  (BV.as_seq h hash_size (MT?.iroots mt))

val mt_ptr_lift:
  h:HS.mem -> mt:mt_ptr{
    BV.bv_inv_liveness hash_size h (MT?.values (B.get h mt 0)) /\
    BV.bv_inv_liveness hash_size h (MT?.iroots (B.get h mt 0))} ->
  GTot High.merkle_tree
let mt_ptr_lift h mt =
  mt_lift h (B.get h mt 0)

val merkle_tree_safe: HS.mem -> mt_ptr -> GTot Type0
let merkle_tree_safe h mt =
  let mtv = B.get h mt 0 in
  let values = MT?.values mtv in
  let iroots = MT?.iroots mtv in
  B.live h mt /\ B.freeable mt /\
  HH.extends (V.frameOf values) (B.frameOf mt) /\
  HH.extends (V.frameOf iroots) (B.frameOf mt) /\
  HH.disjoint (V.frameOf values) (V.frameOf iroots) /\
  BV.bv_inv hash_size h values /\
  BV.bv_inv hash_size h iroots

val merkle_tree_rloc: mt_ptr -> GTot loc
let merkle_tree_rloc mt =
  B.loc_all_regions_from false (B.frameOf mt)

/// Initialization

val create_merkle_tree: unit -> 
  HST.ST mt_ptr
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> merkle_tree_safe h1 mt))
	 //mt_ptr_lift h1 mt == High.create_merkle_tree 32))
#set-options "--z3rlimit 10"
let create_merkle_tree _ =
  let mt_region = BV.new_region_ root in
  let mt_values_region = BV.new_region_ mt_region in 
  let values = BV.create_reserve hash_size 1ul mt_values_region in
  let mt_iroots_region = BV.new_region_ mt_region in 
  let iroots = BV.create_rid 0uy hash_size 32ul mt_iroots_region in
  B.malloc mt_region (MT values iroots) 1ul

/// Insertion

val insert_value:
  vs:hash_vec{not (V.is_full vs)} ->
  nv:hash ->
  HST.ST (ivs:hash_vec)
	 (requires (fun h0 -> 
	   BV.buffer_inv_liveness hash_size h0 nv /\ 
	   BV.bv_inv hash_size h0 vs /\
	   HH.disjoint (V.frameOf vs) (B.frameOf nv)))
	 (ensures (fun h0 ivs h1 -> 
	   BV.buffer_inv_liveness hash_size h1 nv /\ 
	   V.frameOf vs = V.frameOf ivs /\
	   modifies (BV.buf_vector_rloc ivs) h0 h1 /\
	   BV.bv_inv hash_size h1 ivs))
let insert_value vs nv =
  BV.insert_copy 0uy hash_size vs nv

val insert_iroots:
  irs:hash_vec{V.size_of irs = 32ul} ->
  cpos:uint32_t{cpos < 32ul} ->
  irps:uint32_t{U32.v irps < pow2 (U32.v (32ul - cpos)) - 1} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   BV.buffer_inv_liveness hash_size h0 acc /\
	   HH.disjoint (V.frameOf irs) (B.frameOf acc) /\
	   BV.bv_inv hash_size h0 irs))
	 (ensures (fun h0 _ h1 -> 
	   modifies (loc_union (B.loc_buffer acc) 
			       (BV.buf_vector_rloc irs)) h0 h1 /\
	   BV.bv_inv hash_size h1 irs))
let rec insert_iroots irs cpos irps acc =
  if irps % 2ul = 0ul
  then BV.assign_copy hash_size irs cpos acc
  else (hash_from_hashes (V.index irs cpos) acc acc;
       insert_iroots irs (cpos + 1ul) (irps / 2ul) acc)

val insert:
  mt:mt_ptr -> nv:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_liveness hash_size h0 nv /\
	   HH.disjoint (B.frameOf mt) (B.frameOf nv) /\
	   merkle_tree_safe h0 mt /\
	   not (V.is_full (MT?.values (B.get h0 mt 0)))))
	 (ensures (fun h0 _ h1 -> merkle_tree_safe h1 mt))
let insert mt nv =
  let mtv = B.index mt 0ul in
  let values = MT?.values mtv in
  let nvalues = V.size_of values in
  let ivalues = insert_value values nv in
  let iroots = MT?.iroots mtv in
  insert_iroots iroots 0ul nvalues nv;
  assert (loc_disjoint 
	   (BV.buf_vector_rloc ivalues)
	   (loc_union (B.loc_buffer nv) (buf_vector_rloc iroots)));

  B.upd mt 0ul (MT ivalues iroots);
  assert (loc_disjoint (BV.buf_vector_rloc ivalues)
		       (B.loc_buffer mt));
  assert (loc_disjoint (BV.buf_vector_rloc iroots)
		       (B.loc_buffer mt))

/// Getting the Merkle root

val compress_or_init:
  actd:bool -> acc:hash -> nh:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   BV.buffer_inv_liveness hash_size h0 acc /\
	   BV.buffer_inv_liveness hash_size h0 nh /\
	   HH.disjoint (B.frameOf nh) (B.frameOf acc)))
	 (ensures (fun h0 _ h1 ->
	   modifies (B.loc_buffer acc) h0 h1))
let compress_or_init actd acc nh =
  if actd
  then hash_from_hashes nh acc acc
  else B.blit nh 0ul acc 0ul hash_size

val merkle_root_of_iroots:
  irs:hash_vec{V.size_of irs = 32ul} ->
  cpos:uint32_t{cpos < 32ul} ->
  irps:uint32_t{U32.v irps < pow2 (U32.v (32ul - cpos))} ->
  acc:hash -> actd:bool ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_liveness hash_size h0 acc /\
	   BV.bv_inv hash_size h0 irs /\
	   HH.disjoint (V.frameOf irs) (B.frameOf acc)))
	 (ensures (fun h0 _ h1 ->
	   modifies (B.loc_buffer acc) h0 h1))
let rec merkle_root_of_iroots irs cpos irps acc actd =
  if cpos = 31ul 
  then compress_or_init actd acc (V.index irs cpos)
  else (if irps % 2ul = 0ul
       then merkle_root_of_iroots irs (cpos + 1ul) (irps / 2ul) acc actd
       else (compress_or_init actd acc (V.index irs cpos);
  	    merkle_root_of_iroots irs (cpos + 1ul) (irps / 2ul) acc true))

val get_root:
  mt:mt_ptr -> rt:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.buffer_inv_liveness hash_size h0 rt /\
	   B.live h0 mt /\ B.freeable mt /\
	   merkle_tree_safe h0 mt /\
	   HH.disjoint (B.frameOf mt) (B.frameOf rt)))
	 (ensures (fun h0 _ h1 ->
	   modifies (B.loc_buffer rt) h0 h1))
let get_root mt rt =
  let mtv = B.index mt 0ul in
  let values = MT?.values mtv in
  let nvalues = V.size_of values in
  let iroots = MT?.iroots mtv in
  merkle_root_of_iroots iroots 0ul nvalues rt false

/// Freeing the Merkle tree

val free_merkle_tree: 
  mt:mt_ptr ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ B.freeable mt /\
	   merkle_tree_safe h0 mt))
	 (ensures (fun h0 _ h1 -> modifies (merkle_tree_rloc mt) h0 h1))
let free_merkle_tree mt =
  let mtv = B.index mt 0ul in
  BV.free hash_size (MT?.values mtv);
  assert (loc_disjoint 
	   (BV.buf_vector_rloc (MT?.values mtv))
	   (BV.buf_vector_rloc (MT?.iroots mtv)));
  BV.free hash_size (MT?.iroots mtv);
  B.free mt

