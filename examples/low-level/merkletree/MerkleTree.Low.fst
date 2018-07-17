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
| MT: nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg} -> 
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      values:elem_buf{B.length values = alloc_sz nelts} ->
      // The actual number of internal roots should be equal to 
      // the number of "set" bits of `nelts`.
      iroots:hash_buf{B.length iroots = max_num_elts_lg} ->
      merkle_tree

let mtree_ptr = B.pointer merkle_tree

/// Initialization

val create_merkle_tree: unit -> 
  HST.ST merkle_tree
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 -> 
	   B.live h1 (MT?.values mt) /\ B.freeable (MT?.values mt) /\
	   B.live h1 (MT?.iroots mt)))
let create_merkle_tree _ =
  MT 1 (B.malloc root elem_init 1ul)
     (B.malloc root hash_init (UInt32.uint_to_t max_num_elts_lg))

// val init_merkle_tree: unit -> HST.St mtree_ptr
// let init_merkle_tree _ =
//   B.malloc root (create_merkle_tree ()) 1ul

/// Insertion

val mt_is_full: merkle_tree -> Tot bool
let mt_is_full mt = MT?.nelts mt >= pow2 max_num_elts_lg - 1

unfold val insert_nelts: 
  nelts:nat{nelts < pow2 max_num_elts_lg - 1} ->
  Tot (inelts:nat{inelts < pow2 max_num_elts_lg})
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
  nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg - 1} -> 
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
       pow2_lt_le (nelts + 1) max_num_elts_lg; 
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

val merkle_root_of_pow2:
  #nelts:nat{is_pow2 nelts} -> vs:hash_seq{S.length vs = nelts} -> 
  GTot hash
let rec merkle_root_of_pow2 #nelts vs =
  if nelts = 1 then S.index vs 0
  else 
    let lrt = merkle_root_of_pow2 #(nelts / 2) (S.slice vs 0 (nelts / 2)) in
    let rrt = merkle_root_of_pow2 #(nelts / 2) (S.slice vs (nelts / 2) nelts) in
    hash_from_hashes lrt rrt

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

val pow2_floor: 
  n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
let rec pow2_floor n =
  if n = 1 then 0 else 1 + pow2_floor (n / 2)

val num_iroots_of: nelts:nat -> GTot nat
let rec num_iroots_of nelts =
  if nelts = 0 then 0
  else 1 + num_iroots_of (nelts - pow2 (pow2_floor nelts))

val num_iroots_of_limit:
  nelts_max_lg:nat -> nelts:nat{nelts < pow2 nelts_max_lg} ->
  Lemma (num_iroots_of nelts <= nelts_max_lg)
let rec num_iroots_of_limit nelts_max_lg nelts =
  if nelts = 0 then ()
  else num_iroots_of_limit 
       (nelts_max_lg - 1) 
       (nelts - pow2 (pow2_floor nelts))

// val num_iroots_of_inv:
//   nelts:nat{nelts > 0} ->
//   Lemma (num_iroots_of nelts = 

// val merkle_root_of_iroots: 
//   nelts:nat{nelts > 0} -> 
//   iroots:hash_seq{S.length iroots = num_iroots_of nelts} ->
//   GTot hash
// let rec merkle_root_of_iroots nelts iroots =
//   if nelts = 1 then S.index iroots 0
//   else if nelts % 2 = 0 then 

val iroots_of_hashes:
  nelts:nat -> hs:hash_seq{S.length hs = nelts} ->
  GTot (iroots:hash_seq{S.length iroots = num_iroots_of nelts})
let rec iroots_of_hashes nelts hs =
  if nelts = 0 then hs
  else S.cons (merkle_root_of_pow2 #(pow2 (pow2_floor nelts))
				   (S.slice hs 0 (pow2 (pow2_floor nelts))))
	      (iroots_of_hashes (nelts - (pow2 (pow2_floor nelts)))
			 (S.slice hs (pow2 (pow2_floor nelts)) nelts))

val seq_map: 
  #a:Type -> #b:Type -> (f: a -> b) -> s:S.seq a -> 
  Tot (fs:S.seq b{S.length fs = S.length s}) (decreases (S.length s))
let rec seq_map #a #b f s =
  if S.length s = 0 then S.empty
  else S.cons (f (S.head s)) (seq_map f (S.tail s))

unfold val iroots_of: 
  nelts:nat -> es:elem_seq{S.length es = nelts} -> GTot hash_seq
unfold let iroots_of nelts vs =
  iroots_of_hashes nelts (seq_map hash_from_elem vs)

// How to declare `values` as a ghost variable?
#set-options "--z3rlimit 20"
val insert_iroots:
  nelts:nat{nelts > 0 && nelts < pow2 max_num_elts_lg - 1} ->
  values:elem_buf{B.length values = alloc_sz nelts} ->
  irs:hash_buf{B.length irs = max_num_elts_lg} ->
  nv:elem ->
  HST.ST unit
	 (requires (fun h0 ->
	   B.live h0 values /\ B.live h0 irs /\ B.disjoint values irs /\
	   (num_iroots_of_limit max_num_elts_lg nelts;
	     iroots_of nelts (S.slice (B.as_seq h0 values) 0 nelts) =
	     S.slice (B.as_seq h0 irs) 0 (num_iroots_of nelts))))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer irs) h0 h1 /\
	   (num_iroots_of_limit max_num_elts_lg (nelts + 1);
	     iroots_of (nelts + 1) (S.append (S.slice (B.as_seq h0 values) 0 nelts) (S.create 1 nv)) =
	     S.slice (B.as_seq h1 irs) 0 (num_iroots_of (nelts + 1)))))
let rec insert_iroots nelts values irs nv =
  admit ()

val insert: 
  mt:merkle_tree -> e:elem -> 
  HST.ST merkle_tree
	 (requires (fun h0 -> 
	   MT?.nelts mt < pow2 max_num_elts_lg - 1 /\
	   B.disjoint (MT?.values mt) (MT?.iroots mt) /\
	   B.live h0 (MT?.values mt) /\ B.freeable (MT?.values mt) /\
	   B.live h0 (MT?.iroots mt) /\ B.freeable (MT?.iroots mt) /\
	   ~ (mt_is_full mt) /\
	   (num_iroots_of_limit max_num_elts_lg (MT?.nelts mt);
	     iroots_of (MT?.nelts mt) (S.slice (B.as_seq h0 (MT?.values mt)) 0 (MT?.nelts mt)) =
	     S.slice (B.as_seq h0 (MT?.iroots mt)) 0 (num_iroots_of (MT?.nelts mt)))))
	 (ensures (fun h0 _ h1 -> true))
let insert mt e =
  let nnelts = insert_nelts (MT?.nelts mt) in
  let niroots = (insert_iroots (MT?.nelts mt) (MT?.values mt) (MT?.iroots mt) e; MT?.iroots mt) in
  let nvalues = insert_values (MT?.nelts mt) (MT?.values mt) e in
  assert (nnelts > 0 && nnelts < pow2 max_num_elts_lg);
  assert (B.length nvalues = alloc_sz nnelts);
  assert (B.length niroots = max_num_elts_lg);
  admit () // MT nnelts nvalues niroots

/// Getting the Merkle root

