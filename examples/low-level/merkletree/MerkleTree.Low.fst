module MerkleTree.Low

// open MerkleTree.High
// open EverCrypt.Hash

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq
open FStar.Integers

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

// module High = MerkleTree.High

let root = Monotonic.HyperHeap.root

type uint32_t = UInt32.t
type uint8_t = UInt8.t

let hash_size = 32
type hash = b:B.buffer uint8_t{B.length b = hash_size}
let hash_buf = B.buffer hash

// assume val hash_from_hashes: 
//   src1:hash -> src2:hash -> dst:hash -> 
//   HST.St unit
// 	 (requires (fun h0 -> 
// 	   B.live h0 src1 /\ B.live h0 src2 /\ B.live h0 dst))
// 	 (ensures (fun h0 _ h1 ->
// 	   modifies (loc_addr_of_buffer

/// Utilities

val uint32_pow2: sz:uint32_t{sz < 32ul} -> Tot uint32_t
let rec uint32_pow2 sz =
  UInt32.shift_left 1ul sz

val uint32_is_pow2: uint32_t -> Tot bool
let rec uint32_is_pow2 n =
  n <> 0ul && UInt32.logor n (n -% 1ul) = 0ul

val uint32_pow2_floor: n:uint32_t{n > 0ul} -> 
  Tot (p:uint32_t{p < 32ul && uint32_pow2 p <= n})
let uint32_pow2_floor n = admit ()

/// Hash pointers

// val copy_hash: src:hash -> dst:hash -> HST.St unit
// let copy_hash src dst =
//   B.upd dst 0ul (B.index src 0ul)
//     B.upd (B.index nvs nelts) 0ul (B.index e 0ul);



/// Low-level Merkle tree data structure

noeq type merkle_tree =
| MT: nelts:uint32_t{nelts > 0ul} -> 
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      values:hash_buf ->
      // The actual number of internal roots should be equal to 
      // the number of "set" bits of `nelts`.
      iroots:hash_buf ->
      merkle_tree

let mtree_ptr = B.pointer merkle_tree

/// Initialization



val create_hashes: 
  idx:uint32_t -> len:uint32_t -> 
  hs:B.buffer hash{UInt32.v idx < B.length hs} ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 hs))
	 (ensures (fun h0 _ h1 -> modifies (loc_buffer hs) h0 h1))
let rec create_hashes idx len hs =
  if len = 0ul then ()
  else (B.upd hs idx (B.malloc root (UInt8.uint_to_t 0) hash_size);
       assume (UInt32.v (idx + 1ul) < B.length hs);
       create_hashes (idx + 1ul) (len - 1ul) hs)

val create_merkle_tree: unit -> 
  HST.ST mtree_ptr
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> true))
let create_merkle_tree _ = 
  let values = B.malloc root B.null 1ul in
  create_hashes 0ul 1ul values;
  let iroots = B.malloc root B.null 32ul in
  create_hashes 0ul 32ul iroots;
  B.malloc root (MT 1ul values iroots) 1ul

/// Insertion

val insert_values:
  nelts:uint32_t{nelts > 0ul} -> 
  vs:hash_buf ->
  e:hash -> 
  HST.ST (ivs:hash_buf)
	 (requires (fun h0 -> B.live h0 vs /\ B.freeable vs))
	 (ensures (fun h0 nvs h1 -> B.live h1 nvs /\ B.freeable nvs))
#set-options "--z3rlimit 10"
let insert_values nelts vs e =
  if uint32_is_pow2 (nelts +% 1ul)
  then (let nvs = B.malloc root B.null (2ul * (nelts + 1ul)) in
       // `blit` requires two buffers to be disjoint
       LowStar.BufferOps.blit vs 0ul nvs 0ul nelts;
       create_hashes (nelts + 1ul) (nelts + 1ul) nvs;
       B.upd (B.index nvs nelts) 0ul (B.index e 0ul);

       B.free vs;
       let hh2 = HST.get () in assume (B.live hh2 nvs);
       nvs)
  else (assume (UInt32.v nelts < B.length vs);
       B.upd vs nelts e; vs)

val num_iroots_of: nelts:uint32_t -> Tot uint32_t
let rec num_iroots_of nelts =
  admit ()
  // if nelts = 0ul then 0ul
  // else 1ul +% num_iroots_of (nelts -% uint32_pow2 (uint32_pow2_floor nelts))

val insert_iroots:
  nelts:uint32_t{nelts > 0ul} ->
  irs:hash_buf ->
  nv:hash ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 _ h1 -> true))
#set-options "--z3rlimit 20"
let rec insert_iroots nelts irs nv =
  if nelts = 1ul
  then (assume (B.length irs > 0);
       hash_from_hashes (B.index irs 0ul) nv (B.index irs 0ul))
  else if uint32_is_pow2 nelts
  then B.upd (B.index irs 1ul) 0ul (B.index nv 0ul)
  else (insert_iroots (nelts -% uint32_pow2 (uint32_pow2_floor nelts))
  		      (B.sub irs 1ul (num_iroots_of nelts - 1))
  		      nv;
       if nelts +% 1ul = uint32_pow2 (uint32_pow2_floor nelts +% 1ul)
       then hash_from_hashes (B.index irs 0ul) (B.index irs 1ul) 
       			     (B.index irs 0ul)
       else ())

val insert: 
  mt:mtree_ptr -> e:hash -> 
  HST.ST merkle_tree
	 (requires (fun h0 -> true))
	 (ensures (fun h0 nmt h1 -> true))
let insert mt e =
  let nnelts = insert_nelts (MT?.nelts mt) in
  let niroots = insert_iroots (MT?.nelts mt) (MT?.iroots mt) e; MT?.iroots mt in
  let nvalues = insert_values (MT?.nelts mt) (MT?.values mt) e in
  admit () // MT nnelts nvalues niroots

/// Getting the Merkle root

val merkle_root_of_iroots:
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_buf{B.length irs = max_nelts_sz} -> 
  HST.ST hash
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 hs h1 -> 
	   h1 == h0 /\
	   High.merkle_root_of_iroots (B.as_seq h0 irs) = hs))
let merkle_root_of_iroots nirs irs =
  admit ()

