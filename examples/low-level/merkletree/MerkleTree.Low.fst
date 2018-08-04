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

// TODO2: Connect high-level and low-level impls.
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
type uint32_t = U32.t
type uint8_t = U8.t

val uint32_hash_size: uint32_t
let uint32_hash_size = 32ul

type hash = BV.lbuf uint8_t uint32_hash_size
let hash_vec = BV.buf_vector uint8_t uint32_hash_size

// TODO1: When `EverCrypt.Hash` is connected if we define it.
assume val hash_from_hashes: 
  src1:hash -> src2:hash -> dst:hash -> 
  HST.ST unit
	 (requires (fun h0 ->
	   B.live h0 src1 /\ not (B.g_is_null src1) /\
	   B.live h0 src2 /\ not (B.g_is_null src2) /\
	   B.live h0 dst /\ not (B.g_is_null dst)))
	 (ensures (fun h0 _ h1 ->
	   // memory safety
	   modifies (loc_buffer dst) h0 h1 /\
	   // correctness
	   High.hash_from_hashes 
	     (B.as_seq h1 src1) 
	     (B.as_seq h1 src2) = B.as_seq h1 dst)) 

/// Sequence mapping

val seq_map:
  #a:Type -> #b:Type -> f:(a -> GTot b) -> s:S.seq a -> 
  GTot (fs:S.seq b{
    S.length fs = S.length s /\
    (forall (i:nat{i < S.length fs}). S.index fs i == f (S.index s i))})
    (decreases (S.length s))
let rec seq_map #a #b f s =
  if S.length s = 0 then S.empty
  else S.cons (f (S.head s)) (seq_map f (S.tail s))

val seq_map_create:
  #a:Type -> #b:Type -> f:(a -> GTot b) -> 
  len:nat -> ia:a ->
  Lemma (seq_map f (S.create len ia) ==
	S.create len (f ia))
	[SMTPat (seq_map f (S.create len ia))]
let rec seq_map_create #a #b f len ia =
  S.lemma_eq_intro (seq_map f (S.create len ia)) (S.create len (f ia))

val seq_map_append:
  #a:Type -> #b:Type -> f:(a -> GTot b) -> 
  s1:S.seq a -> s2:S.seq a ->
  Lemma (seq_map f (S.append s1 s2) ==
	S.append (seq_map f s1) (seq_map f s2))
	[SMTPat (seq_map f (S.append s1 s2))]
let rec seq_map_append #a #b f s1 s2 =
  S.lemma_eq_elim (seq_map f (S.append s1 s2)) 
		  (S.append (seq_map f s1) (seq_map f s2))

val seq_map_slice:
  #a:Type -> #b:Type -> f:(a -> GTot b) -> 
  s:S.seq a -> i:nat -> j:nat{i <= j && j <= length s} ->
  Lemma (seq_map f (S.slice s i j) == S.slice (seq_map f s) i j)
	[SMTPat (seq_map f (S.slice s i j)); 
	SMTPat (S.slice (seq_map f s) i j)]
let seq_map_slice #a #b f s i j =
  S.lemma_eq_elim (seq_map f (S.slice s i j))
		  (S.slice (seq_map f s) i j)

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

/// Power of 2

val uint32_pow2: 
  sz:uint32_t{sz < 32ul} -> Tot (p:uint32_t{U32.v p = pow2 (U32.v sz)})
let uint32_pow2 sz =
  Math.Lemmas.pow2_lt_compat U32.n (U32.v sz);
  UInt32.shift_left 1ul sz

val uint32_is_pow2_ok:
  n:uint32_t{n > 0ul} ->
  Lemma (requires (UInt32.logor n (n - 1ul) = 0ul))
	(ensures (is_pow2 (U32.v n)))



val uint32_is_pow2: 
  n:uint32_t ->
  Tot (b:bool{b = is_pow2 (U32.v n)})
      (decreases (U32.v n))
let uint32_is_pow2 n =
  let b = n <> 0ul && UInt32.logor n (n - 1ul) = 0ul in
  assume (b = is_pow2 (U32.v n));
  b

val uint32_pow2_floor':
  sz:erased nat{reveal sz > 0 && reveal sz <= 32} ->
  n:uint32_t{n > 0ul && U32.v n < pow2 (reveal sz)} ->
  Tot (p:uint32_t{
    U32.v p < reveal sz && pow2 (U32.v p) <= U32.v n && 
    U32.v n < pow2 (U32.v p + 1)})
      (decreases (U32.v n))
let rec uint32_pow2_floor' sz n =
  if n = 1ul then 0ul
  else (1ul + uint32_pow2_floor' (hide (reveal sz - 1))
       	      			 (UInt32.shift_right n 1ul))

val uint32_pow2_floor:
  n:uint32_t{n > 0ul} ->
  Tot (p:uint32_t{ 
    p < 32ul && pow2 (U32.v p) <= U32.v n && 
    U32.v n < pow2 (U32.v p + 1)})
      (decreases (U32.v n))
let uint32_pow2_floor n =
  uint32_pow2_floor' (hide 32) n

val uint32_num_of_ones:
  sz:erased nat{reveal sz <= U32.n} -> 
  n:uint32_t{U32.v n < pow2 (reveal sz)} ->
  Tot (nirs:uint32_t{U32.v nirs <= reveal sz /\ High.num_of_ones (U32.v n) = U32.v nirs})
      (decreases (U32.v n))
let rec uint32_num_of_ones sz n =
  if n = 0ul then 0ul
  else (let nones = n % 2ul + uint32_num_of_ones (hide (reveal sz - 1)) (n / 2ul) in
       assume (High.num_of_ones (U32.v n) = U32.v nones);
       nones)

/// Low-level Merkle tree data structure

noeq type merkle_tree =
| MT: values:hash_vec ->
      iroots:hash_vec{V.size_of iroots = 32ul} ->
      merkle_tree

let mt_ptr = B.pointer merkle_tree

val merkle_tree_wf: HS.mem -> merkle_tree -> GTot Type0
let merkle_tree_wf h mt =
  // memory safety
  BV.bv_inv h (MT?.values mt) /\
  BV.bv_inv h (MT?.iroots mt) /\
  V.frameOf (MT?.values mt) <> V.frameOf (MT?.iroots mt)

/// Initialization

val create_merkle_tree: unit -> 
  HST.ST mt_ptr
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 ->
	   merkle_tree_wf h1 (B.get h1 mt 0)))
let create_merkle_tree _ =
  let values = BV.create 1ul in
  let iroots = BV.create 32ul in
  // fresh_regions_neq (V.frameOf values) (V.frameOf iroots) hh0 hh1 hh2;
  B.malloc root (MT values iroots) 1ul

/// Insertion

// NOTE: it copies the value of `vs` buffer.
val insert_value:
  vs:hash_vec{not (V.is_full vs)} ->
  nv:hash ->
  HST.ST (ivs:hash_vec)
	 (requires (fun h0 ->
	   BV.bv_inv h0 vs /\
	   B.live h0 nv /\ not (B.g_is_null nv)))
	 (ensures (fun h0 ivs h1 -> 
	   BV.bv_inv h1 ivs))
let insert_value vs nv =
  BV.insert_copy 0uy vs nv

val insert_iroots:
  irs:hash_vec ->
  nvalues:uint32_t{U32.v nvalues < pow2 (U32.v (V.size_of irs)) - 1} ->
  nv:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   BV.bv_inv h0 irs /\
	   B.live h0 nv /\ not (B.g_is_null nv)))
	 (ensures (fun h0 _ h1 ->
	   BV.bv_inv h1 irs))
let rec insert_iroots irs nvalues nv =
  admit ()
  // let hh0 = HST.get () in
  // if nvalues = 0ul
  // then copy_hash nv (B.index irs 0ul)
  // else (hash_buf_allocated_gsub hh0 irs 1ul (B.len irs - 1ul);
  //      hash_buf_disjoint_ext_gsub hh0 irs 1ul (B.len irs - 1ul) nv;
  //      hash_buf_disjoint_ext_gsub hh0 irs 1ul (B.len irs - 1ul) irs;
       
  //      insert_iroots (hide (reveal nirs - 1))
  // 		     (nvalues - uint32_pow2 (uint32_pow2_floor nvalues))
  // 		     (B.offset irs 1ul) nv;

  //      let hh1 = HST.get () in
  //      let tirs = B.offset irs 1ul in
  //      B.modifies_buffer_elim (B.get hh1 irs 0) (loc_hashes hh1 tirs) hh0 hh1;
  //      modifies_union_weakened_right (loc_buffer (B.get hh0 irs 0))
  //      				     (loc_hashes hh0 tirs)
  //      				     hh0 hh1);
  //      Math.Lemmas.pow2_le_compat U32.n (reveal nirs);

  //      if uint32_is_pow2 (nvalues + 1ul)
  //      then hash_from_hashes (B.index irs 0ul) (B.index irs 1ul)
  //      	    		     (B.index irs 0ul)
  //      else ()

val insert_maximum_helper:
  sz:nat -> n:uint32_t{U32.v n = pow2 sz - 1 && U32.v n < UInt.max_int U32.n} ->
  Lemma (2 * U32.v n + 1 <= UInt.max_int U32.n)
#set-options "--z3rlimit 10"
let insert_maximum_helper sz n =
  pow2_lt_compat_inv sz U32.n

val insert:
  mt:mt_ptr -> nv:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ B.freeable mt /\
	   (let mtv = B.get h0 mt 0 in
	   merkle_tree_wf h0 mtv /\
	   not (V.is_full (MT?.values mtv))) /\
	   B.live h0 nv /\ not (B.g_is_null nv)))
	 (ensures (fun h0 _ h1 ->
	   merkle_tree_wf h1 (B.get h1 mt 0)))
let insert mt nv =
  let mtv = B.index mt 0ul in
  let values = MT?.values mtv in
  let nvalues = V.size_of values in
  let iroots = MT?.iroots mtv in
  insert_iroots iroots nvalues nv;
  admit ();
  let ivalues = insert_value values nv in
  B.upd mt 0ul (MT ivalues iroots)

/// Getting the Merkle root

val merkle_root_of_iroots:
  irs:hash_vec ->
  iidx:uint32_t{iidx < V.size_of irs} ->
  acc:hash ->
  HST.ST unit
	 (requires (fun h0 ->
	   BV.bv_inv h0 irs /\
	   B.live h0 acc /\ not (B.g_is_null acc)))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer acc) h0 h1))
let rec merkle_root_of_iroots irs iidx acc =
  if iidx = 0ul 
  then (admit (); hash_from_hashes (V.index irs 0ul) acc acc)
  else (admit (); hash_from_hashes (V.index irs iidx) acc acc;
       merkle_root_of_iroots irs (iidx - 1ul) acc)

val get_root:
  mt:mt_ptr -> rt:hash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ B.freeable mt /\
	   merkle_tree_wf h0 (B.get h0 mt 0) /\
	   B.live h0 rt /\ not (B.g_is_null rt)))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer rt) h0 h1))
let get_root mt rt =
  let mtv = B.index mt 0ul in
  let values = MT?.values mtv in
  let nvalues = V.size_of values in
  if nvalues = 0ul then ()
  else (let iroots = MT?.iroots mtv in
       let nirs = uint32_num_of_ones (hide 32) nvalues in
       merkle_root_of_iroots iroots (nirs - 1ul) rt)

/// Freeing the Merkle tree

val free_merkle_tree: 
  mt:mt_ptr ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ B.freeable mt /\
	   merkle_tree_wf h0 (B.get h0 mt 0)))
	 (ensures (fun h0 _ h1 -> true))
	 // Should have sth. like: modifies (loc_mt mt) h0 h1
let free_merkle_tree mt =
  let mtv = B.index mt 0ul in
  admit ();
  BV.free (MT?.values mtv);
  BV.free (MT?.iroots mtv);
  B.free mt

