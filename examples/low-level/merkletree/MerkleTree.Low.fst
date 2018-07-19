module MerkleTree.Low

open MerkleTree.High

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

module High = MerkleTree.High

let root = Monotonic.HyperHeap.root
let elem_buf = B.buffer elem
let hash_buf = B.buffer hash

// This number says that the maximum number of values is (2^32 - 1)
unfold let max_nelts_sz = 32

/// Mapping sequences (why is it not in the library?)

val seq_map: 
  #a:Type -> #b:Type -> f:(a -> b) -> s:S.seq a -> 
  Tot (fs:S.seq b{
    S.length fs = S.length s /\
    (forall (i:nat{i < S.length fs}). S.index fs i == f (S.index s i))})
    (decreases (S.length s))
let rec seq_map #a #b f s =
  if S.length s = 0 then S.empty
  else S.cons (f (S.head s)) (seq_map f (S.tail s))

// val seq_map_create:
//   #a:Type -> #b:Type -> f: (a -> b) -> 
//   len:nat -> ia:a ->
//   Lemma (seq_map f (S.create len ia) == S.create len (f ia))
// let seq_map_create #a #b f len ia =
//   S.lemma_eq_elim (seq_map f (S.create len ia)) (S.create len (f ia))

/// Allocation by power of two

val alloc_sz_lg:
  nelts:nat{nelts > 0} -> 
  GTot (sz:nat{sz > 0 && pow2 (sz - 1) <= nelts && nelts < pow2 sz})
let rec alloc_sz_lg nelts = pow2_floor nelts + 1

unfold val alloc_sz: nelts:nat{nelts > 0} -> GTot nat
unfold let alloc_sz nelts =
  pow2 (alloc_sz_lg nelts) - 1

val alloc_sz_lg_pow2_inc:
  nelts:nat{nelts > 0} ->
  Lemma (requires (is_pow2 (nelts + 1)))
	(ensures (alloc_sz_lg (nelts + 1) = 1 + alloc_sz_lg nelts))
let rec alloc_sz_lg_pow2_inc nelts =
  if nelts = 1 then ()
  else alloc_sz_lg_pow2_inc (nelts / 2)

val alloc_sz_lg_not_pow2_inc:
  nelts:nat{nelts > 0} ->
  Lemma (requires (~ (is_pow2 (nelts + 1))))
	(ensures (alloc_sz_lg nelts = alloc_sz_lg (nelts + 1)))
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
| MT: nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz} -> 
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      values:elem_buf{B.length values = alloc_sz nelts} ->
      // The actual number of internal roots should be equal to 
      // the number of "set" bits of `nelts`.
      iroots:hash_buf{B.length iroots = max_nelts_sz} ->
      merkle_tree

let mtree_ptr = B.pointer merkle_tree

val num_iroots_of_bound: 
  #nelts_sz:nat -> nelts:nat{nelts < pow2 nelts_sz} -> 
  GTot (nirs:nat{nirs = num_iroots_of nelts && nirs <= nelts_sz})
let rec num_iroots_of_bound #nelts_sz nelts =
  if nelts = 0 then 0
  else 1 + num_iroots_of_bound #(nelts_sz - 1) (nelts - pow2 (pow2_floor nelts))

val merkle_tree_lift: HS.mem -> merkle_tree -> GTot (High.merkle_tree)
let merkle_tree_lift h mt =
  High.MT (MT?.nelts mt) 
	  (S.slice (B.as_seq h (MT?.values mt)) 0 (MT?.nelts mt))
	  (S.slice (B.as_seq h (MT?.iroots mt)) 
	    0 (num_iroots_of_bound #max_nelts_sz (MT?.nelts mt)))

/// Low-level well-formedness

unfold val merkle_tree_wf: HS.mem -> merkle_tree -> GTot Type0
unfold let merkle_tree_wf h mt =
  B.live h (MT?.values mt) /\ B.freeable (MT?.values mt) /\ 
  B.live h (MT?.iroots mt) /\
  B.disjoint (MT?.values mt) (MT?.iroots mt) /\
  High.merkle_tree_wf (merkle_tree_lift h mt)

/// Initialization

val create_merkle_tree: unit -> 
  HST.ST merkle_tree
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> merkle_tree_wf h1 mt))
let create_merkle_tree _ = 
  let values = B.malloc root elem_init 1ul in
  let hh0 = HST.get () in
  let iroots = B.malloc root (hash_from_elem elem_init) (UInt32.uint_to_t max_nelts_sz) in
  let hh1 = HST.get () in
  B.live_unused_in_disjoint hh0 values iroots;
  S.lemma_eq_intro (iroots_of 1 (S.slice (B.as_seq hh1 values) 0 1))
  		   (S.slice (B.as_seq hh1 iroots) 0 1);
  MT 1 values iroots

// val init_merkle_tree: unit -> HST.St mtree_ptr
// let init_merkle_tree _ =
//   B.malloc root (create_merkle_tree ()) 1ul

/// Insertion

val mt_is_full: merkle_tree -> Tot bool
let mt_is_full mt = MT?.nelts mt >= pow2 max_nelts_sz - 1

val insert_nelts: 
  nelts:nat{nelts < pow2 max_nelts_sz - 1} ->
  Tot (inelts:nat{
      inelts = High.insert_nelts nelts && 
      inelts < pow2 max_nelts_sz})
let insert_nelts nelts =
  nelts + 1

val insert_values:
  nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz - 1} -> 
  vs:elem_buf{B.length vs = alloc_sz nelts} ->
  e:elem -> 
  HST.ST (ivs:elem_buf{B.length ivs = alloc_sz (insert_nelts nelts)})
	 (requires (fun h0 -> B.live h0 vs /\ B.freeable vs))
	 (ensures (fun h0 nvs h1 -> 
	   B.live h1 nvs /\ B.freeable nvs /\
	   S.slice (B.as_seq h1 nvs) 0 (insert_nelts nelts) ==
	   High.insert_values (S.slice (B.as_seq h0 vs) 0 nelts) e))
#set-options "--z3rlimit 20"
let insert_values nelts vs e =
  if is_pow2 (nelts + 1)
  then (let hh0 = HST.get () in
       // Need to prove `2 * nelts + 1` does not exceed the maximum before `B.malloc`
       pow2_lt_le (nelts + 1) max_nelts_sz; 
       let nvs = B.malloc root elem_init (UInt32.uint_to_t (2 * nelts + 1)) in

       // `blit` requires two buffers to be disjoint
       B.live_unused_in_disjoint hh0 vs nvs;
       loc_disjoint_buffer vs nvs;
       LowStar.BufferOps.blit vs 0ul nvs 0ul (UInt32.uint_to_t nelts);

       B.upd nvs (UInt32.uint_to_t nelts) e;
       let hh1 = HST.get () in
       S.lemma_eq_elim (S.slice (B.as_seq hh1 nvs) 0 (insert_nelts nelts))
       		       (High.insert_values (S.slice (B.as_seq hh0 vs) 0 nelts) e);

       // TODO: should be able to prove that `nvs` is not affected after `B.free`
       // there might be a relation among `B.disjoint`, `B.free`, and `B.live`
       // B.free vs;
       // let hh2 = HST.get () in assume (B.live hh2 nvs);

       alloc_sz_lg_pow2_inc nelts;
       nvs)
  else (let hh0 = HST.get () in
       B.upd vs (UInt32.uint_to_t nelts) e; 
       let hh1 = HST.get () in
       S.lemma_eq_elim (S.slice (B.as_seq hh1 vs) 0 (insert_nelts nelts))
       		       (High.insert_values (S.slice (B.as_seq hh0 vs) 0 nelts) e);

       alloc_sz_lg_not_pow2_inc nelts;
       vs)

val insert_iroots:
  nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz - 1} ->
  irs:hash_buf{B.length irs = max_nelts_sz} ->
  nv:elem ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 _ h1 -> 
	   modifies (loc_buffer irs) h0 h1 /\
	   S.slice (B.as_seq h1 irs) 0 (num_iroots_of_bound #max_nelts_sz (insert_nelts nelts)) ==
	   High.insert_iroots 
	     nelts (S.slice (B.as_seq h0 irs) 0 (num_iroots_of_bound #max_nelts_sz nelts)) 
	     (hash_from_elem nv)))
let rec insert_iroots nirs irs nv =
  admit ()

val insert: 
  mt:merkle_tree -> e:elem -> 
  HST.ST merkle_tree
	 (requires (fun h0 -> merkle_tree_wf h0 mt /\ ~ (mt_is_full mt)))
	 (ensures (fun h0 nmt h1 ->
	   merkle_tree_wf h1 nmt /\
	   High.insert (merkle_tree_lift h0 mt) e == merkle_tree_lift h1 nmt))
let insert mt e =
  let nnelts = insert_nelts (MT?.nelts mt) in
  let niroots = insert_iroots (MT?.nelts mt) (MT?.iroots mt) e; MT?.iroots mt in
  let nvalues = insert_values (MT?.nelts mt) (MT?.values mt) e in
  admit () // MT nnelts nvalues niroots

/// Getting the Merkle root

val merkle_root_of_iroots':
  acc:hash ->
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_buf{B.length irs = max_nelts_sz} -> 
  HST.ST hash
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 hs h1 -> 
	   h1 == h0 /\
	   High.merkle_root_of_iroots' acc (B.as_seq h0 irs) = hs))
let rec merkle_root_of_iroots' acc nirs irs =
  // if nirs = 0 then acc
  // else merkle_root_of_iroots'
  //      (hash_from_hashes (B.index irs (UInt32.uint_to_t (nirs - 1))) acc)
  //      (nirs - 1) irs
  admit () // TODO: need to prove `High.merkle_root_of_iroots'`

val merkle_root_of_iroots:
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_buf{B.length irs = max_nelts_sz} -> 
  HST.ST hash
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 hs h1 -> 
	   h1 == h0 /\
	   High.merkle_root_of_iroots (B.as_seq h0 irs) = hs))
let merkle_root_of_iroots nirs irs =
  merkle_root_of_iroots' hash_init nirs irs

