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

let root = Monotonic.HyperHeap.root

assume type elem: eqtype u#0
assume type hash: eqtype u#0
assume val elem_init: elem
assume val hash_init: hash
let elem_buf = B.buffer elem
let hash_buf = B.buffer hash
let elem_seq = S.seq elem
let hash_seq = S.seq hash

assume val hash_from_elem: elem -> Tot hash

assume val hash_from_hashes: hash -> hash -> Tot hash
assume val hash_init_idem: 
  h:hash -> Lemma (hash_from_hashes h hash_init = h)

// This number says that the maximum number of values is (2^32 - 1)
let max_nelts_sz = 32

/// Mapping sequences (why is it not in the library?)

val seq_map: 
  #a:Type -> #b:Type -> f:(a -> b) -> s:S.seq a -> 
  Tot (fs:S.seq b{S.length fs = S.length s}) (decreases (S.length s))
let rec seq_map #a #b f s =
  if S.length s = 0 then S.empty
  else S.cons (f (S.head s)) (seq_map f (S.tail s))

// val seq_map_create:
//   #a:Type -> #b:Type -> f: (a -> b) -> 
//   len:nat -> ia:a ->
//   Lemma (seq_map f (S.create len ia) == S.create len (f ia))
// let rec seq_map_create #a #b f len ia =
//   admit ()

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
  GTot (sz:nat{sz > 0 && pow2 (sz - 1) <= nelts && nelts < pow2 sz})
let rec alloc_sz_lg nelts =
  if nelts = 1 then 1
  else 1 + alloc_sz_lg (nelts / 2)

unfold val alloc_sz: nelts:nat{nelts > 0} -> GTot nat
unfold let alloc_sz nelts =
  pow2 (alloc_sz_lg nelts) - 1

val pow2_interval_unique:
  n:nat -> sz1:nat{sz1 > 0} -> sz2:nat{sz2 > 0} ->
  Lemma (requires (pow2 (sz1 - 1) <= n && n < pow2 sz1 &&
		  pow2 (sz2 - 1) <= n && n < pow2 sz2))
	(ensures (sz1 = sz2))
let pow2_interval_unique n sz1 sz2 =
  if sz1 > sz2 
  then Math.Lemmas.pow2_le_compat (sz1 - 1) sz2
  else if sz1 < sz2
  then Math.Lemmas.pow2_le_compat (sz2 - 1) sz1
  else ()

val alloc_sz_lg_inv:
  nelts:nat -> sz:nat{sz > 0} ->
  Lemma (requires (pow2 (sz - 1) <= nelts && nelts < pow2 sz))
	(ensures (alloc_sz_lg nelts = sz))
let alloc_sz_lg_inv nelts sz =
  pow2_interval_unique nelts sz (alloc_sz_lg nelts)

val alloc_sz_lg_pow2:
  nelts:nat ->
  Lemma (requires (is_pow2 nelts))
	(ensures (nelts = pow2 (alloc_sz_lg nelts - 1)))
let rec alloc_sz_lg_pow2 nelts =
  if nelts = 1 then ()
  else if nelts % 2 = 0 then alloc_sz_lg_pow2 (nelts / 2)
  else ()

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

/// Invariants between internal roots and values

val merkle_root_of_pow2:
  #nelts:nat{is_pow2 nelts} -> vs:hash_seq{S.length vs = nelts} -> 
  GTot hash
let rec merkle_root_of_pow2 #nelts vs =
  if nelts = 1 then S.index vs 0
  else 
    let lrt = merkle_root_of_pow2 #(nelts / 2) (S.slice vs 0 (nelts / 2)) in
    let rrt = merkle_root_of_pow2 #(nelts / 2) (S.slice vs (nelts / 2) nelts) in
    hash_from_hashes lrt rrt

val pow2_floor: 
  n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
let rec pow2_floor n =
  if n = 1 then 0 else 1 + pow2_floor (n / 2)

val num_iroots_of: 
  nelts_sz:nat -> nelts:nat{nelts < pow2 nelts_sz} -> 
  GTot (nirs:nat{nirs <= nelts_sz})
let rec num_iroots_of nelts_max_lg nelts =
  if nelts = 0 then 0
  else 1 + num_iroots_of (nelts_max_lg - 1) (nelts - pow2 (pow2_floor nelts))

val iroots_of_hashes:
  nelts_sz:nat -> nelts:nat{nelts < pow2 nelts_sz} -> 
  hs:hash_seq{S.length hs = nelts} ->
  GTot (iroots:hash_seq{S.length iroots = num_iroots_of nelts_sz nelts})
let rec iroots_of_hashes nelts_sz nelts hs =
  if nelts = 0 then hs
  else S.cons (merkle_root_of_pow2 #(pow2 (pow2_floor nelts))
				   (S.slice hs 0 (pow2 (pow2_floor nelts))))
	      (iroots_of_hashes (nelts_sz - 1) (nelts - (pow2 (pow2_floor nelts)))
				(S.slice hs (pow2 (pow2_floor nelts)) nelts))

unfold val iroots_of: 
  nelts_sz:nat -> nelts:nat{nelts < pow2 nelts_sz} -> 
  es:elem_seq{S.length es = nelts} -> GTot hash_seq
unfold let iroots_of nelts_sz nelts vs =
  iroots_of_hashes nelts_sz nelts (seq_map hash_from_elem vs)

unfold val merkle_tree_elems_wf:
  nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz} -> 
  values:elem_seq{S.length values = nelts} ->
  iroots:hash_seq{S.length iroots = num_iroots_of max_nelts_sz nelts} ->
  GTot bool
unfold let merkle_tree_elems_wf nelts values iroots =
  iroots_of max_nelts_sz nelts values = iroots

unfold val merkle_tree_wf: HS.mem -> merkle_tree -> GTot Type0
unfold let merkle_tree_wf h mt =
  B.live h (MT?.values mt) /\ B.live h (MT?.iroots mt) /\
  merkle_tree_elems_wf 
    (MT?.nelts mt) 
    (S.slice (B.as_seq h (MT?.values mt)) 0 (MT?.nelts mt))
    (S.slice (B.as_seq h (MT?.iroots mt)) 0 (num_iroots_of max_nelts_sz (MT?.nelts mt)))

/// Initialization

val create_merkle_tree: unit -> 
  HST.ST merkle_tree
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> 
	   B.freeable (MT?.values mt) /\ 
	   B.disjoint (MT?.values mt) (MT?.iroots mt) /\
	   merkle_tree_wf h1 mt))
let create_merkle_tree _ =
  let values = B.malloc root elem_init 1ul in
  let iroots = B.malloc root (hash_from_elem elem_init) (UInt32.uint_to_t max_nelts_sz) in
  // let hh = HST.get () in
  // assume (B.disjoint values iroots);
  // assume (iroots_of max_nelts_sz 1 (S.slice (B.as_seq hh values) 0 1) = S.slice (B.as_seq hh iroots) 0 1);
  admit (); MT 1 values iroots

// val init_merkle_tree: unit -> HST.St mtree_ptr
// let init_merkle_tree _ =
//   B.malloc root (create_merkle_tree ()) 1ul

/// Insertion

val mt_is_full: merkle_tree -> Tot bool
let mt_is_full mt = MT?.nelts mt >= pow2 max_nelts_sz - 1

unfold val insert_nelts: 
  nelts:nat{nelts < pow2 max_nelts_sz - 1} ->
  Tot (inelts:nat{inelts < pow2 max_nelts_sz})
unfold let insert_nelts nelts =
  nelts + 1

val pow2_lt_le:
  n:nat -> p:nat{p > 0} ->
  Lemma (requires (is_pow2 n && n < pow2 p))
	(ensures (n <= pow2 (p - 1)))
let rec pow2_lt_le n p =
  if n = 1 then ()
  else pow2_lt_le (n / 2) (p - 1)

val insert_values:
  nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz - 1} -> 
  vs:elem_buf{B.length vs = alloc_sz nelts} ->
  e:elem -> 
  HST.ST (ivs:elem_buf{B.length ivs = alloc_sz (insert_nelts nelts)})
	 (requires (fun h0 -> B.live h0 vs /\ B.freeable vs))
	 (ensures (fun h0 nvs h1 -> 
	   B.live h1 nvs /\ B.freeable nvs /\
	   S.slice (B.as_seq h1 nvs) 0 nelts == S.slice (B.as_seq h0 vs) 0 nelts /\
	   S.index (B.as_seq h1 nvs) nelts == e))
#set-options "--z3rlimit 10"
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

       // TODO: should be able to prove that `nvs` is not affected after `B.free`
       // there might be a relation among `B.disjoint`, `B.free`, and `B.live`
       // B.free vs;
       // let hh2 = HST.get () in assume (B.live hh2 nvs);

       alloc_sz_lg_pow2_inc nelts;
       nvs)
  else (B.upd vs (UInt32.uint_to_t nelts) e; 
       alloc_sz_lg_not_pow2_inc nelts;
       vs)

// TODO: How to declare `values` as a ghost variable?
#set-options "--z3rlimit 20"
val insert_iroots:
  nelts:nat{nelts > 0 && nelts < pow2 max_nelts_sz - 1} ->
  values:elem_buf{B.length values = alloc_sz nelts} ->
  irs:hash_buf{B.length irs = max_nelts_sz} ->
  nv:elem ->
  HST.ST unit
	 (requires (fun h0 ->
	   B.live h0 values /\ B.live h0 irs /\ B.disjoint values irs /\
	   merkle_tree_elems_wf 
	     nelts (S.slice (B.as_seq h0 values) 0 nelts)
	     (S.slice (B.as_seq h0 irs) 0 (num_iroots_of max_nelts_sz nelts))))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer irs) h0 h1 /\
	   merkle_tree_elems_wf
	     (insert_nelts nelts)
	     (S.append (S.slice (B.as_seq h0 values) 0 nelts) (S.create 1 nv))
	     (S.slice (B.as_seq h1 irs) 0 (num_iroots_of max_nelts_sz (insert_nelts nelts)))))
let rec insert_iroots nelts values irs nv =
  admit ()

val insert: 
  mt:merkle_tree -> e:elem -> 
  HST.ST merkle_tree
	 (requires (fun h0 -> 
	   MT?.nelts mt < pow2 max_nelts_sz - 1 /\
	   B.disjoint (MT?.values mt) (MT?.iroots mt) /\
	   B.live h0 (MT?.values mt) /\ B.freeable (MT?.values mt) /\
	   B.live h0 (MT?.iroots mt) /\ B.freeable (MT?.iroots mt) /\
	   ~ (mt_is_full mt) /\
	   merkle_tree_wf h0 mt))
	 (ensures (fun h0 nmt h1 -> true))
let insert mt e =
  let nnelts = insert_nelts (MT?.nelts mt) in
  let niroots = (insert_iroots (MT?.nelts mt) (MT?.values mt) (MT?.iroots mt) e; MT?.iroots mt) in
  let nvalues = insert_values (MT?.nelts mt) (MT?.values mt) e in
  assert (nnelts > 0 && nnelts < pow2 max_nelts_sz);
  assert (B.length nvalues = alloc_sz nnelts);
  assert (B.length niroots = max_nelts_sz);
  admit () // MT nnelts nvalues niroots

/// Getting the Merkle root

val padding_to_pow2:
  nelts:nat{nelts > 0} -> GTot (sz:nat{
    if nelts = 1 then sz = 0
    else sz > 0 && pow2 (sz - 1) < nelts && nelts <= pow2 sz})
let rec padding_to_pow2 nelts =
  if nelts = 1 then 0
  else if nelts % 2 = 0 then 1 + padding_to_pow2 (nelts / 2)
  else 1 + padding_to_pow2 ((nelts + 1) / 2)

val pad_hashes_pow2:
  vs:hash_seq{S.length vs > 0} -> 
  GTot (pvs:hash_seq{
    S.length pvs = pow2 (padding_to_pow2 (S.length vs)) && 
    S.slice pvs 0 (S.length vs) = vs})
let pad_hashes_pow2 vs =
  let pad = S.create (pow2 (padding_to_pow2 (S.length vs)) - S.length vs) hash_init in
  S.append_slices vs pad;
  S.append vs pad

val merkle_root_of_hashes: vs:hash_seq{S.length vs > 0} -> GTot hash
let merkle_root_of_hashes vs =
  merkle_root_of_pow2 #(pow2 (padding_to_pow2 (S.length vs))) 
		      (pad_hashes_pow2 vs)

val merkle_root_of_iroots_seq':
  acc:hash ->
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_seq{S.length irs = max_nelts_sz} -> 
  GTot hash (decreases nirs)
let rec merkle_root_of_iroots_seq' acc nirs irs =
  if nirs = 0 then acc
  else merkle_root_of_iroots_seq'
       (hash_from_hashes (S.index irs (nirs - 1)) acc)
       (nirs - 1) irs

val merkle_root_of_iroots':
  acc:hash ->
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_buf{B.length irs = max_nelts_sz} -> 
  HST.ST hash
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 hs h1 -> 
	   h1 == h0 /\
	   merkle_root_of_iroots_seq' acc nirs (B.as_seq h0 irs) = hs))
let rec merkle_root_of_iroots' acc nirs irs =
  if nirs = 0 then acc
  else merkle_root_of_iroots'
       (hash_from_hashes (B.index irs (UInt32.uint_to_t (nirs - 1))) acc)
       (nirs - 1) irs

val merkle_root_of_iroots_seq:
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_seq{S.length irs = max_nelts_sz} -> 
  GTot hash (decreases nirs)
let rec merkle_root_of_iroots_seq nirs irs =
  merkle_root_of_iroots_seq' hash_init nirs irs

val merkle_root_of_iroots:
  nirs:nat{nirs <= max_nelts_sz} ->
  irs:hash_buf{B.length irs = max_nelts_sz} -> 
  HST.ST hash
	 (requires (fun h0 -> B.live h0 irs))
	 (ensures (fun h0 hs h1 -> 
	   h1 == h0 /\
	   merkle_root_of_iroots_seq nirs (B.as_seq h0 irs) = hs))
let merkle_root_of_iroots nirs irs =
  merkle_root_of_iroots' hash_init nirs irs

val merkle_root_of_iroots_ok:
  h:HS.mem -> mt:merkle_tree ->
  Lemma (requires (merkle_tree_wf h mt))
	(ensures (merkle_root_of_iroots_seq (num_iroots_of max_nelts_sz (MT?.nelts mt)) (B.as_seq h (MT?.iroots mt)) =
		 merkle_root_of_hashes (seq_map hash_from_elem (B.as_seq h (MT?.values mt)))))

