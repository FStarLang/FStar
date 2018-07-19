module MerkleTree.High

open FStar.All
open FStar.Mul
open FStar.Seq

// open EverCrypt.Hash
// open MerkleTree.Spec

module List = FStar.List.Tot
module S = FStar.Seq

assume type elem: eqtype u#0
assume type hash: eqtype u#0
assume val elem_init: elem
assume val hash_init: hash
let elem_seq = S.seq elem
let hash_seq = S.seq hash

assume val hash_from_elem: elem -> Tot hash
assume val hash_from_hashes: hash -> hash -> Tot hash
assume val hash_init_idem: 
  h:hash -> Lemma (hash_from_hashes h hash_init = h)

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

/// Power of two (TODO: use a bit vector; division is expensive)

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

val pow2_lt_le:
  n:nat -> p:nat{p > 0} ->
  Lemma (requires (is_pow2 n && n < pow2 p))
	(ensures (n <= pow2 (p - 1)))
let rec pow2_lt_le n p =
  if n = 1 then ()
  else pow2_lt_le (n / 2) (p - 1)

val pow2_floor: 
  n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
let rec pow2_floor n =
  if n = 1 then 0 else 1 + pow2_floor (n / 2)

val pow2_floor_pow2:
  p:nat -> 
  Lemma (pow2_floor (pow2 p) = p)
	[SMTPat (pow2_floor (pow2 p))]
let rec pow2_floor_pow2 p =
  if p = 0 then ()
  else pow2_floor_pow2 (p - 1)

val pow2_floor_is_pow2:
  n:nat ->
  Lemma (requires (is_pow2 n))
	(ensures (n = pow2 (pow2_floor n)))
let rec pow2_floor_is_pow2 n =
  if n = 1 then ()
  else pow2_floor_is_pow2 (n / 2)

val pow2_interval_unique:
  n:nat -> p1:nat -> p2:nat ->
  Lemma (requires (pow2 p1 <= n && n < pow2 (p1 + 1) &&
		  pow2 p2 <= n && n < pow2 (p2 + 1)))
	(ensures (p1 = p2))
let pow2_interval_unique n p1 p2 =
  if p1 > p2 
  then Math.Lemmas.pow2_le_compat (p1 - 1) p2
  else if p1 < p2
  then Math.Lemmas.pow2_le_compat (p2 - 1) p1
  else ()

val pow2_floor_inv:
  p:nat -> n:nat{pow2 p <= n && n < pow2 (p + 1)} ->
  Lemma (pow2_floor n = p)
let rec pow2_floor_inv p n =
  pow2_interval_unique n (pow2_floor n) p

val pow2_floor_pow2_pow2:
  p:nat -> q:nat{p > q} ->
  Lemma (pow2_floor (pow2 p + pow2 q) = p)
let rec pow2_floor_pow2_pow2 p q =
  Math.Lemmas.pow2_lt_compat p q;
  pow2_floor_inv p (pow2 p + pow2 q)

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

val num_iroots_of: nelts:nat -> GTot nat
let rec num_iroots_of nelts =
  if nelts = 0 then 0
  else 1 + num_iroots_of (nelts - pow2 (pow2_floor nelts))

val iroots_of_hashes:
  nelts:nat -> hs:hash_seq{S.length hs = nelts} ->
  GTot (iroots:hash_seq{S.length iroots = num_iroots_of nelts})
let rec iroots_of_hashes nelts hs =
  if nelts = 0 then hs
  else
    let n_floor = pow2 (pow2_floor nelts) in
    let hs0, hs1 = S.split hs n_floor in
    S.cons (merkle_root_of_pow2 #n_floor hs0) 
	   (iroots_of_hashes (nelts - n_floor) hs1)

unfold val iroots_of: 
  nelts:nat -> es:elem_seq{S.length es = nelts} -> GTot hash_seq
unfold let iroots_of nelts vs =
  iroots_of_hashes nelts (seq_map hash_from_elem vs)

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: nelts:nat{nelts > 0} -> 
      values:elem_seq{S.length values = nelts} ->
      iroots:hash_seq{iroots = iroots_of nelts values} ->
      merkle_tree

/// Creating a merkle tree instance

val create_merkle_tree: unit -> merkle_tree
let create_merkle_tree _ = 
  S.lemma_eq_elim (iroots_of 1 (S.create 1 elem_init))
  		  (S.create 1 (hash_from_elem elem_init));
  MT 1 (S.create 1 elem_init) (S.create 1 (hash_from_elem elem_init))

/// Insertion

unfold val insert_nelts: nat -> GTot nat
unfold let insert_nelts nelts = nelts + 1

val insert_values: elem_seq -> elem -> GTot elem_seq
let insert_values vs nv = S.snoc vs nv

// val merge_iroots_seq:
//   sz1:nat -> nelts1:nat{nelts1 = pow2 sz1 && nelts1 < pow2 max_nelts_sz - 1} ->
//   irs1:hash_seq{S.length irs1 = num_iroots_of max_nelts_sz nelts1} ->
//   sz2:nat{sz1 >= sz2} -> nelts2:nat{nelts2 = pow2 sz2 && nelts1 + nelts2 < pow2 max_nelts_sz - 1} ->
//   irs2:hash_seq{S.length irs2 = num_iroots_of max_nelts_sz nelts2} ->
//   GTot (mirs:hash_seq{S.length mirs = num_iroots_of max_nelts_sz (nelts1 + nelts2)})
// let merge_iroots_seq sz1 nelts1 irs1 sz2 nelts2 irs2 =
//   if sz1 = sz2 
//   then S.create 1 (hash_from_hashes (S.index irs1 0) (S.index irs2 0))
//   else (pow2_floor_pow2_pow2 sz1 sz2;
//        assert (num_iroots_of max_nelts_sz nelts1 = 1);
//        assert (num_iroots_of max_nelts_sz nelts2 = 1);
//        assert (num_iroots_of max_nelts_sz (nelts1 + nelts2) =
//        	      1 + num_iroots_of (max_nelts_sz - 1) (nelts1 + nelts2 - pow2 (pow2_floor (nelts1 + nelts2))));
//        assert (num_iroots_of max_nelts_sz (nelts1 + nelts2) = 2);
//        S.append irs1 irs2)

val insert_iroots:
  nelts:nat{nelts > 0} ->
  irs:hash_seq{S.length irs = num_iroots_of nelts} ->
  nh:hash ->
  GTot (iirs:hash_seq{S.length iirs = num_iroots_of (insert_nelts nelts)})
let rec insert_iroots nelts irs nh =
  admit ()

val insert: mt:merkle_tree -> e:elem -> GTot merkle_tree
let insert mt e =
  let nnelts = insert_nelts (MT?.nelts mt) in
  let niroots = insert_iroots (MT?.nelts mt) (MT?.iroots mt) (hash_from_elem e) in
  let nvalues = insert_values (MT?.values mt) e in
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

val merkle_root_of_iroots':
  acc:hash -> irs:hash_seq -> GTot hash (decreases (S.length irs))
let rec merkle_root_of_iroots' acc irs =
  if S.length irs = 0 then acc
  else merkle_root_of_iroots'
       (hash_from_hashes (S.index irs (S.length irs - 1)) acc)
       (S.tail irs)

val merkle_root_of_iroots: irs:hash_seq -> GTot hash
let rec merkle_root_of_iroots irs =
  merkle_root_of_iroots' hash_init irs

val merkle_root_of_iroots_ok:
  mt:merkle_tree ->
  Lemma (merkle_root_of_iroots (MT?.iroots mt) =
	merkle_root_of_hashes (seq_map hash_from_elem (MT?.values mt)))
let merkle_root_of_iroots_ok mt =
  admit ()

