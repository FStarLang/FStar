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

assume val hash_from_hashes: hash -> hash -> Tot hash

/// About FStar.Seq.Base.seq

// val lemma_split_append:
//   #a:Type -> s1:S.seq a -> s2:S.seq a ->
//   Lemma (S.split (S.append s1 s2) (S.length s1) == (s1, s2))
// let lemma_split_append #a s1 s2 =
//   S.lemma_eq_elim (fst (S.split (S.append s1 s2) (S.length s1))) s1;
//   S.lemma_eq_elim (snd (S.split (S.append s1 s2) (S.length s1))) s2

// val seq_create_one_cons:
//   #a:eqtype -> ia:a -> 
//   Lemma (S.create 1 ia = S.cons ia S.empty)
// 	[SMTPat (S.create 1 ia); SMTPat (S.cons ia S.empty)]
// let seq_create_one_cons #a ia =
//   S.lemma_eq_elim (S.create 1 ia) (S.cons ia S.empty)

/// Power of two

// val is_pow2: nat -> Tot bool
// let rec is_pow2 n =
//   if n = 0 then false
//   else if n = 1 then true
//   else (n % 2 = 0 && is_pow2 (n / 2))

// val pow2_is_pow2:
//   n:nat ->
//   Lemma (is_pow2 (pow2 n))
// 	[SMTPat (is_pow2 (pow2 n))]
// let rec pow2_is_pow2 n =
//   if n = 0 then ()
//   else pow2_is_pow2 (n - 1)

// val pow2_lt_le:
//   n:nat -> p:nat{p > 0} ->
//   Lemma (requires (is_pow2 n && n < pow2 p))
// 	(ensures (n <= pow2 (p - 1)))
// let rec pow2_lt_le n p =
//   if n = 1 then ()
//   else pow2_lt_le (n / 2) (p - 1)

// val pow2_floor: 
//   n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
// let rec pow2_floor n =
//   if n = 1 then 0 else 1 + pow2_floor (n / 2)

// val pow2_ceil:
//   n:nat{n > 0} -> 
//   GTot (p:nat{
//     if n = 1 then p = 0
//     else (p > 0 && pow2 (p - 1) < n && n <= pow2 p)})
// let rec pow2_ceil n =
//   if n = 1 then 0
//   else if n % 2 = 0 then 1 + pow2_ceil (n / 2)
//   else 1 + pow2_ceil ((n + 1) / 2)

// val pow2_floor_pow2:
//   p:nat -> 
//   Lemma (pow2_floor (pow2 p) = p)
// 	[SMTPat (pow2_floor (pow2 p))]
// let rec pow2_floor_pow2 p =
//   if p = 0 then ()
//   else pow2_floor_pow2 (p - 1)

// val pow2_ceil_pow2:
//   p:nat -> 
//   Lemma (pow2_ceil (pow2 p) = p)
// 	[SMTPat (pow2_ceil (pow2 p))]
// let rec pow2_ceil_pow2 p =
//   if p = 0 then ()
//   else (assert (pow2 p / 2 = pow2 (p - 1));
//        pow2_ceil_pow2 (p - 1))

// val pow2_floor_is_pow2:
//   n:nat ->
//   Lemma (requires (is_pow2 n))
// 	(ensures (n = pow2 (pow2_floor n)))
// 	[SMTPat (is_pow2 n)]
// let rec pow2_floor_is_pow2 n =
//   if n = 1 then ()
//   else pow2_floor_is_pow2 (n / 2)

// val pow2_ceil_is_pow2:
//   n:nat ->
//   Lemma (requires (is_pow2 n))
// 	(ensures (n = pow2 (pow2_ceil n)))
// 	[SMTPat (is_pow2 n)]
// let rec pow2_ceil_is_pow2 n =
//   if n = 1 then ()
//   else pow2_ceil_is_pow2 (n / 2)

// val pow2_interval_unique:
//   n:nat -> p1:nat -> p2:nat ->
//   Lemma (requires (pow2 p1 <= n && n < pow2 (p1 + 1) &&
// 		  pow2 p2 <= n && n < pow2 (p2 + 1)))
// 	(ensures (p1 = p2))
// let pow2_interval_unique n p1 p2 =
//   if p1 > p2 
//   then Math.Lemmas.pow2_le_compat (p1 - 1) p2
//   else if p1 < p2
//   then Math.Lemmas.pow2_le_compat (p2 - 1) p1
//   else ()

// val pow2_floor_inv:
//   p:nat -> n:nat{pow2 p <= n && n < pow2 (p + 1)} ->
//   Lemma (pow2_floor n = p)
// let pow2_floor_inv p n =
//   pow2_interval_unique n (pow2_floor n) p

// val pow2_floor_pow2_less:
//   p:nat -> n:nat{n < pow2 p} ->
//   Lemma (pow2_floor (pow2 p + n) = p)
// let pow2_floor_pow2_less p n =
//   pow2_floor_inv p (pow2 p + n)

// val pow2_floor_pow2_pow2:
//   p:nat -> q:nat{p > q} ->
//   Lemma (pow2_floor (pow2 p + pow2 q) = p)
// let pow2_floor_pow2_pow2 p q =
//   Math.Lemmas.pow2_lt_compat p q;
//   pow2_floor_pow2_less p (pow2 q)

// val pow2_lt_compat_inv:
//   p:nat -> q:nat ->
//   Lemma (requires (pow2 p < pow2 q))
// 	(ensures (p < q))
// let rec pow2_lt_compat_inv p q =
//   if q <= p then Math.Lemmas.pow2_le_compat p q
//   else ()

// val pow2_le_compat_inv:
//   p:nat -> q:nat ->
//   Lemma (requires (pow2 p <= pow2 q))
// 	(ensures (p <= q))
// let rec pow2_le_compat_inv p q =
//   if q < p then Math.Lemmas.pow2_lt_compat p q
//   else ()

// val not_pow2_floor_ceil:
//   n:nat{n > 0 && not (is_pow2 n)} ->
//   Lemma (pow2_floor n + 1 = pow2_ceil n)
// let not_pow2_floor_ceil n =
//   let fl = pow2_floor n in
//   let cl = pow2_ceil n in
//   pow2_le_compat_inv fl cl;
//   pow2_lt_compat_inv (cl - 1) (fl + 1)

/// Invariants between internal roots and values

// type hash_seq_pow2 = hs:hash_seq{is_pow2 (S.length hs)}

// val merkle_root_of_pow2:
//   hs:hash_seq_pow2 -> GTot hash (decreases (S.length hs))
// let rec merkle_root_of_pow2 hs =
//   if S.length hs = 1 then S.index hs 0
//   else
//     let lhs, rhs = S.split hs (S.length hs / 2) in
//     let lrt = merkle_root_of_pow2 lhs in
//     let rrt = merkle_root_of_pow2 rhs in
//     hash_from_hashes lrt rrt

// val merkle_root_of_pow2_inv:
//   hs1:hash_seq_pow2{S.length hs1 > 0} -> 
//   hs2:hash_seq_pow2{S.length hs2 = S.length hs1} ->
//   Lemma (merkle_root_of_pow2 (S.append hs1 hs2) =
// 	hash_from_hashes (merkle_root_of_pow2 hs1)
// 			 (merkle_root_of_pow2 hs2))
// 	[SMTPat (merkle_root_of_pow2 (S.append hs1 hs2))]
// let merkle_root_of_pow2_inv hs1 hs2 =
//   assert (S.length (S.append hs1 hs2) / 2 = S.length hs1);
//   lemma_split_append hs1 hs2

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: sz:nat{sz > 0} ->
      values:hash_seq{S.length values < pow2 sz} ->
      iroots:hash_seq{S.length iroots = sz} ->
      merkle_tree

/// Creating a merkle tree instance

val hash_default: hash
let hash_default = S.create (U32.v hash_size) 0uy

val create_merkle_tree: sz:nat{sz > 0} -> Tot merkle_tree
let create_merkle_tree sz =
  MT sz S.empty (S.create sz hash_default)

/// Insertion

val insert_values: 
  sz:nat -> hs:hash_seq{S.length hs < pow2 sz - 1} -> hash -> 
  Tot (ihs:hash_seq{S.length ihs < pow2 sz})
let insert_values sz vs nv = S.snoc vs nv

val insert_iroots:
  irs:hash_seq ->
  cpos:nat{cpos < S.length irs} ->
  irps:nat{irps < pow2 (S.length irs - cpos) - 1} ->
  acc:hash ->
  Tot (iirs:hash_seq{S.length iirs = S.length irs})
      (decreases (S.length irs - cpos))
let rec insert_iroots irs cpos irps acc =
  if irps % 2 = 0
  then S.upd irs cpos acc
  else (let nacc = hash_from_hashes (S.index irs cpos) acc in
       insert_iroots irs (cpos + 1) (irps / 2) nacc)

val insert: 
  mt:merkle_tree{S.length (MT?.values mt) < pow2 (MT?.sz mt) - 1} ->
  e:hash -> Tot merkle_tree
let insert mt e =
  let sz = MT?.sz mt in
  let values = MT?.values mt in
  let iroots = MT?.iroots mt in
  MT sz (insert_values sz values e)
     (insert_iroots iroots 0 (S.length values) e)

/// Getting the Merkle root

val compress_or_init:
  actd:bool -> acc:hash -> nh:hash -> Tot hash
let compress_or_init actd acc nh =
  if actd
  then hash_from_hashes nh acc
  else nh

val merkle_root_of_iroots: 
  irs:hash_seq ->
  cpos:nat{cpos < S.length irs} ->
  irps:nat{irps < pow2 (S.length irs - cpos)} ->
  acc:hash -> actd:bool ->
  Tot hash (decreases (S.length irs - cpos))
let rec merkle_root_of_iroots irs cpos irps acc actd =
  if cpos = S.length irs - 1
  then compress_or_init actd acc (S.index irs cpos)
  else (if irps % 2 = 0
       then merkle_root_of_iroots irs (cpos + 1) (irps / 2) acc actd
       else (let nacc = compress_or_init actd acc (S.index irs cpos) in
	    merkle_root_of_iroots irs (cpos + 1) (irps / 2) nacc true))

val get_root:
  mt:merkle_tree -> rt:hash -> Tot hash
let get_root mt rt =
  merkle_root_of_iroots (MT?.iroots mt) 0 (S.length (MT?.values mt)) rt false

