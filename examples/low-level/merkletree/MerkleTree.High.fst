module MerkleTree.High

open FStar.All
open FStar.Ghost
open FStar.Mul
open FStar.Seq
open FStar.Integers

module List = FStar.List.Tot
module S = FStar.Seq

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

val hash_size: uint32_t
let hash_size = 32ul

let hash = b:S.seq uint8_t{S.length b = U32.v hash_size}
let hash_seq = S.seq hash

val hash_default: hash
let hash_default = S.create (U32.v hash_size) 0uy

assume val hash_from_hashes: hash -> hash -> Tot hash

/// About FStar.Seq.Base.seq

val lemma_split_append:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  Lemma (S.split (S.append s1 s2) (S.length s1) == (s1, s2))
let lemma_split_append #a s1 s2 =
  S.lemma_eq_elim (fst (S.split (S.append s1 s2) (S.length s1))) s1;
  S.lemma_eq_elim (snd (S.split (S.append s1 s2) (S.length s1))) s2

val snoc_slice:
  #a:Type -> s:S.seq a -> v:a ->
  Lemma (S.equal (S.slice (S.snoc s v) 0 (S.length s)) s)
	[SMTPat (S.slice (S.snoc s v) 0 (S.length s))]
let snoc_slice #a s v = ()

val cons_slice:
  #a:Type -> v:a -> s:S.seq a -> 
  Lemma (S.equal (S.slice (S.cons v s) 1 (S.length s + 1)) s)
	[SMTPat (S.slice (S.cons v s) 1 (S.length s + 1))]
let cons_slice #a v s = ()

/// Power of two / Division by two

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

val remainder_by_two_add_one_1:
  n:nat ->
  Lemma (requires (n % 2 = 0))
	(ensures ((n + 1) % 2 <> 0))
let remainder_by_two_add_one_1 n = ()

val remainder_by_two_add_one_2:
  n:nat ->
  Lemma (requires (n % 2 <> 0))
	(ensures ((n + 1) % 2 = 0))
let remainder_by_two_add_one_2 n = ()

val remainder_by_two_sub_one_1:
  n:nat{n > 0} ->
  Lemma (requires (n % 2 = 0))
	(ensures ((n - 1) % 2 <> 0))
let remainder_by_two_sub_one_1 n = ()

val remainder_by_two_sub_one_2:
  n:nat ->
  Lemma (requires (n % 2 <> 0))
	(ensures ((n - 1) % 2 = 0))
let remainder_by_two_sub_one_2 n = ()

val div_by_two_same_odd:
  n:nat ->
  Lemma (requires (n % 2 <> 0))
	(ensures (n / 2 = (n - 1) / 2))
let div_by_two_same_odd n = ()

/// The Merkle root of a full binary tree

type hash_seq_pow2 = hs:hash_seq{is_pow2 (S.length hs)}

val merkle_root_of_pow2:
  hs:hash_seq_pow2 -> GTot hash (decreases (S.length hs))
let rec merkle_root_of_pow2 hs =
  if S.length hs = 1 then S.index hs 0
  else
    let lhs, rhs = S.split hs (S.length hs / 2) in
    let lrt = merkle_root_of_pow2 lhs in
    let rrt = merkle_root_of_pow2 rhs in
    hash_from_hashes lrt rrt

val merkle_root_of_pow2_inv:
  hs1:hash_seq_pow2{S.length hs1 > 0} -> 
  hs2:hash_seq_pow2{S.length hs2 = S.length hs1} ->
  Lemma (merkle_root_of_pow2 (S.append hs1 hs2) =
	hash_from_hashes (merkle_root_of_pow2 hs1)
			 (merkle_root_of_pow2 hs2))
	[SMTPat (merkle_root_of_pow2 (S.append hs1 hs2))]
let merkle_root_of_pow2_inv hs1 hs2 =
  assert (S.length (S.append hs1 hs2) / 2 = S.length hs1);
  lemma_split_append hs1 hs2

/// Invariants between internal roots and values

val num_iroots_of:
  nvalues:nat -> GTot (nirs:nat)
let rec num_iroots_of nvalues =
  if nvalues = 0 then 0
  else if nvalues % 2 = 0 then num_iroots_of (nvalues / 2)
  else 1 + num_iroots_of (nvalues / 2)

val iroots_compactify:
  sz:nat -> irps:nat{irps < pow2 sz} ->
  irs:hash_seq{S.length irs = sz}  ->
  GTot (cirs:hash_seq{S.length cirs = num_iroots_of irps})
       (decreases sz)
let rec iroots_compactify sz irps irs =
  if sz = 0 then S.empty
  else if irps % 2 = 0 
  then iroots_compactify (sz - 1) (irps / 2) (S.tail irs)
  else S.cons (S.head irs) (iroots_compactify (sz - 1) (irps / 2) (S.tail irs))

val iroots_compactify_0:
  sz:nat -> irs:hash_seq{S.length irs = sz} ->
  Lemma (iroots_compactify sz 0 irs = S.empty)
let rec iroots_compactify_0 sz irs =
  if sz = 0 then ()
  else iroots_compactify_0 (sz - 1) (S.tail irs)

val compress_hashes_half:
  hs:hash_seq{S.length hs % 2 = 0} -> 
  GTot (chs:hash_seq{S.length chs = S.length hs / 2})
       (decreases (S.length hs))
let rec compress_hashes_half hs =
  if S.length hs = 0 then S.empty
  else S.snoc (compress_hashes_half (S.slice hs 0 (S.length hs - 2)))
	      (hash_from_hashes (S.index hs (S.length hs - 2))
				(S.index hs (S.length hs - 1)))

val iroots_of_hashes:
  hs:hash_seq ->
  GTot (iroots:hash_seq{S.length iroots = num_iroots_of (S.length hs)})
       (decreases (S.length hs))
let rec iroots_of_hashes hs =
  if S.length hs = 0 then S.empty 
  else if S.length hs % 2 = 0
  then iroots_of_hashes (compress_hashes_half hs)
  else S.cons (S.index hs (S.length hs - 1))
	      (iroots_of_hashes (compress_hashes_half (S.slice hs 0 (S.length hs - 1))))

val iroots_of_hashes_head:
  hs:hash_seq ->
  Lemma (requires (S.length hs % 2 <> 0))
	(ensures (S.head (iroots_of_hashes hs) =
		 S.index hs (S.length hs - 1)))
let iroots_of_hashes_head hs = ()

val iroots_of_hashes_tail:
  hs:hash_seq ->
  Lemma (requires (S.length hs % 2 <> 0))
	(ensures (S.equal (S.tail (iroots_of_hashes hs))
			  (iroots_of_hashes
			    (compress_hashes_half 
			      (S.slice hs 0 (S.length hs - 1))))))
let iroots_of_hashes_tail hs = ()

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: values:hash_seq ->
      iroots:hash_seq ->
      merkle_tree

val merkle_tree_ok: mt:merkle_tree -> GTot bool
let merkle_tree_ok mt =
  MT?.iroots mt = iroots_of_hashes (MT?.values mt)

type good_merkle_tree = mt:merkle_tree{merkle_tree_ok mt}

/// Creating a merkle tree instance

val create_merkle_tree: unit -> Tot good_merkle_tree
let create_merkle_tree _ = 
  MT S.empty S.empty

/// Insertion

val insert_values: 
  hs:hash_seq -> nv:hash -> 
  Tot (ihs:hash_seq{S.length ihs = S.length hs + 1})
let insert_values vs nv = S.snoc vs nv

val insert_iroots:
  irps:nat ->
  irs:hash_seq{S.length irs = num_iroots_of irps} ->
  acc:hash ->
  Tot (iirs:hash_seq{S.length iirs = num_iroots_of (irps + 1)})
      (decreases irps)
let rec insert_iroots irps irs acc =
  if irps % 2 = 0
  then S.cons acc irs
  else (let nacc = hash_from_hashes (S.index irs 0) acc in
       insert_iroots (irps / 2) (S.tail irs) nacc)

val insert_ok_case_odd_lhs:
  values:hash_seq ->
  iroots:hash_seq{iroots = iroots_of_hashes values} ->
  e:hash ->
  Lemma (requires (S.length values % 2 <> 0))
	(ensures (insert_iroots (S.length values) iroots e =
		 insert_iroots (S.length values / 2) 
			       (S.tail iroots)
			       (hash_from_hashes (S.head iroots) e)))
let insert_ok_case_odd_lhs values iroots e = ()

val compress_hashes_half_snoc:
  values:hash_seq -> e:hash ->
  Lemma (requires (S.length values % 2 <> 0))
	(ensures (compress_hashes_half (S.snoc values e) =
		 S.snoc (compress_hashes_half (S.slice values 0 (S.length values - 1)))
			(hash_from_hashes (S.index values (S.length values - 1)) e)))
let compress_hashes_half_snoc values e =
  assert (S.length (S.snoc values e) <> 0);
  assert (S.equal (S.slice (S.snoc values e) 0 (S.length (S.snoc values e) - 2))
		  (S.slice values 0 (S.length values - 1)));
  assert (S.index (S.snoc values e) (S.length (S.snoc values e) - 2) =
	 S.index values (S.length values - 1));
  assert (S.index (S.snoc values e) (S.length (S.snoc values e) - 1) = e)

val insert_ok_case_odd_rhs:
  values:hash_seq -> e:hash ->
  Lemma (requires (S.length values % 2 <> 0))
	(ensures (iroots_of_hashes (insert_values values e) =
		 iroots_of_hashes
		   (S.snoc (compress_hashes_half 
			     (S.slice values 0 (S.length values - 1)))
			   (hash_from_hashes
			     (S.index values (S.length values - 1)) e))))
#set-options "--z3rlimit 20"
let insert_ok_case_odd_rhs values e =
  compress_hashes_half_snoc values e

val insert_ok:
  values:hash_seq ->
  iroots:hash_seq{iroots = iroots_of_hashes values} ->
  e:hash ->
  Lemma (requires True)
	(ensures 
	  (S.equal (insert_iroots (S.length values) iroots e)
		   (iroots_of_hashes (S.snoc values e))))
	(decreases (S.length iroots))
#set-options "--z3rlimit 40"
let rec insert_ok values iroots e =
  if S.length values = 0 then ()
  else if S.length values % 2 = 0 then ()
  else (iroots_of_hashes_head values;
       iroots_of_hashes_tail values;
       insert_ok_case_odd_lhs values iroots e;
       insert_ok_case_odd_rhs values e;
       compress_hashes_half_snoc values e;
       remainder_by_two_sub_one_2 (S.length values);
       div_by_two_same_odd (S.length values);
       insert_ok 
	 (compress_hashes_half (S.slice values 0 (S.length values - 1)))
	 (S.tail iroots)
	 (hash_from_hashes (S.head iroots) e))

val insert: mt:good_merkle_tree -> e:hash -> Tot good_merkle_tree
let insert mt e =
  let values = MT?.values mt in
  let iroots = MT?.iroots mt in
  insert_ok values iroots e;
  MT (insert_values values e)
     (insert_iroots (S.length values) iroots e)

/// Getting the Merkle root

val compress_or_init:
  actd:bool -> acc:hash -> nh:hash -> Tot hash
let compress_or_init actd acc nh =
  if actd
  then hash_from_hashes nh acc
  else nh

val merkle_root_of_iroots:
  nvalues:nat{nvalues > 0} ->
  irs:hash_seq{S.length irs = num_iroots_of nvalues} ->
  acc:hash -> actd:bool ->
  Tot hash (decreases nvalues)
let rec merkle_root_of_iroots nvalues irs acc actd =
  if nvalues = 1 
  then compress_or_init actd acc (S.index irs 0)
  else (if nvalues % 2 = 0
       then merkle_root_of_iroots (nvalues / 2) irs acc actd
       else (let nacc = compress_or_init actd acc (S.index irs 0) in
	    merkle_root_of_iroots (nvalues / 2) (S.tail irs) nacc true))

val get_root:
  mt:good_merkle_tree{S.length (MT?.values mt) > 0} -> rt:hash -> 
  Tot hash
let get_root mt rt =
  merkle_root_of_iroots
    (S.length (MT?.values mt))
    (MT?.iroots mt) rt false

