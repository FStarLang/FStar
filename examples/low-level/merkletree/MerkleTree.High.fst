module MerkleTree.High

open FStar.All
open FStar.Mul
open FStar.Seq
// open FStar.BitVector

// open EverCrypt.Hash
// open MerkleTree.Spec

module List = FStar.List.Tot
module S = FStar.Seq
module BV = FStar.BitVector

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

/// About FStar.Seq.Base.seq (the library is not that rich enough..)

val seq_map:
  #a:Type -> #b:Type -> f:(a -> b) -> s:S.seq a -> 
  Tot (fs:S.seq b{
    S.length fs = S.length s /\
    (forall (i:nat{i < S.length fs}). S.index fs i == f (S.index s i))})
    (decreases (S.length s))
let rec seq_map #a #b f s =
  if S.length s = 0 then S.empty
  else S.cons (f (S.head s)) (seq_map f (S.tail s))

val seq_map_create:
  #a:Type -> #b:Type -> f:(a -> b) -> 
  len:nat -> ia:a ->
  Lemma (seq_map f (S.create len ia) ==
	S.create len (f ia))
	[SMTPat (seq_map f (S.create len ia))]
let rec seq_map_create #a #b f len ia =
  S.lemma_eq_intro (seq_map f (S.create len ia)) (S.create len (f ia))

val seq_map_append:
  #a:Type -> #b:Type -> f:(a -> b) -> 
  s1:S.seq a -> s2:S.seq a ->
  Lemma (seq_map f (S.append s1 s2) ==
	S.append (seq_map f s1) (seq_map f s2))
	[SMTPat (seq_map f (S.append s1 s2))]
let rec seq_map_append #a #b f s1 s2 =
  S.lemma_eq_elim (seq_map f (S.append s1 s2)) 
		  (S.append (seq_map f s1) (seq_map f s2))

val seq_map_slice:
  #a:Type -> #b:Type -> f:(a -> b) -> 
  s:S.seq a -> i:nat -> j:nat{i <= j && j <= length s} ->
  Lemma (seq_map f (S.slice s i j) == S.slice (seq_map f s) i j)
	[SMTPat (seq_map f (S.slice s i j)); 
	SMTPat (S.slice (seq_map f s) i j)]
let seq_map_slice #a #b f s i j =
  S.lemma_eq_elim (seq_map f (S.slice s i j))
		  (S.slice (seq_map f s) i j)

val lemma_split_append:
  #a:Type -> s1:S.seq a -> s2:S.seq a ->
  Lemma (S.split (S.append s1 s2) (S.length s1) == (s1, s2))
let lemma_split_append #a s1 s2 =
  S.lemma_eq_elim (fst (S.split (S.append s1 s2) (S.length s1))) s1;
  S.lemma_eq_elim (snd (S.split (S.append s1 s2) (S.length s1))) s2

val seq_create_one_cons:
  #a:eqtype -> ia:a -> 
  Lemma (S.create 1 ia = S.cons ia S.empty)
	[SMTPat (S.create 1 ia); SMTPat (S.cons ia S.empty)]
let seq_create_one_cons #a ia =
  S.lemma_eq_elim (S.create 1 ia) (S.cons ia S.empty)

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

val pow2_ceil:
  n:nat{n > 0} -> 
  GTot (p:nat{
    if n = 1 then p = 0
    else (p > 0 && pow2 (p - 1) < n && n <= pow2 p)})
let rec pow2_ceil n =
  if n = 1 then 0
  else if n % 2 = 0 then 1 + pow2_ceil (n / 2)
  else 1 + pow2_ceil ((n + 1) / 2)

val pow2_floor_pow2:
  p:nat -> 
  Lemma (pow2_floor (pow2 p) = p)
	[SMTPat (pow2_floor (pow2 p))]
let rec pow2_floor_pow2 p =
  if p = 0 then ()
  else pow2_floor_pow2 (p - 1)

val pow2_ceil_pow2:
  p:nat -> 
  Lemma (pow2_ceil (pow2 p) = p)
	[SMTPat (pow2_ceil (pow2 p))]
let rec pow2_ceil_pow2 p =
  if p = 0 then ()
  else (assert (pow2 p / 2 = pow2 (p - 1));
       pow2_ceil_pow2 (p - 1))

val pow2_floor_is_pow2:
  n:nat ->
  Lemma (requires (is_pow2 n))
	(ensures (n = pow2 (pow2_floor n)))
	[SMTPat (is_pow2 n)]
let rec pow2_floor_is_pow2 n =
  if n = 1 then ()
  else pow2_floor_is_pow2 (n / 2)

val pow2_ceil_is_pow2:
  n:nat ->
  Lemma (requires (is_pow2 n))
	(ensures (n = pow2 (pow2_ceil n)))
	[SMTPat (is_pow2 n)]
let rec pow2_ceil_is_pow2 n =
  if n = 1 then ()
  else pow2_ceil_is_pow2 (n / 2)

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
let pow2_floor_inv p n =
  pow2_interval_unique n (pow2_floor n) p

val pow2_floor_pow2_less:
  p:nat -> n:nat{n < pow2 p} ->
  Lemma (pow2_floor (pow2 p + n) = p)
let pow2_floor_pow2_less p n =
  pow2_floor_inv p (pow2 p + n)

val pow2_floor_pow2_pow2:
  p:nat -> q:nat{p > q} ->
  Lemma (pow2_floor (pow2 p + pow2 q) = p)
let pow2_floor_pow2_pow2 p q =
  Math.Lemmas.pow2_lt_compat p q;
  pow2_floor_pow2_less p (pow2 q)

val not_pow2_floor_ceil:
  n:nat{n > 0 && not (is_pow2 n)} ->
  Lemma (pow2_floor n + 1 = pow2_ceil n)
let not_pow2_floor_ceil n =
  admit ()

/// Invariants between internal roots and values

type hash_seq_pow2 = hs:hash_seq{is_pow2 (S.length hs)}
type elem_seq_pow2 = vs:elem_seq{is_pow2 (S.length vs)}

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

val num_iroots_of: nelts:nat -> GTot nat
let rec num_iroots_of nelts =
  if nelts = 0 then 0
  else 1 + num_iroots_of (nelts - pow2 (pow2_floor nelts))

val iroots_of_hashes:
  hs:hash_seq -> 
  GTot (iroots:hash_seq{S.length iroots = num_iroots_of (S.length hs)})
       (decreases (S.length hs))
let rec iroots_of_hashes hs =
  if S.length hs = 0 then hs
  else
    let n_floor = pow2 (pow2_floor (S.length hs)) in
    let hs0, hs1 = S.split hs n_floor in
    S.cons (merkle_root_of_pow2 hs0) (iroots_of_hashes hs1)

val iroots_of_hashes_pow2_same:
  hs1:hash_seq_pow2 ->
  hs2:hash_seq{S.length hs2 = S.length hs1} ->
  Lemma (iroots_of_hashes (S.append hs1 hs2) =
	S.create 1 (hash_from_hashes 
	  (S.index (iroots_of_hashes hs1) 0)
	  (S.index (iroots_of_hashes hs2) 0)))
let iroots_of_hashes_pow2_same hs1 hs2 =
  S.lemma_eq_elim (S.cons (merkle_root_of_pow2 (S.append hs1 hs2)) S.empty)
  		  (S.create 1 (merkle_root_of_pow2 (S.append hs1 hs2)));
  assert (S.index (iroots_of_hashes hs1) 0 = merkle_root_of_pow2 hs1);
  assert (S.index (iroots_of_hashes hs2) 0 = merkle_root_of_pow2 hs2)

val iroots_of_hashes_pow2_diff:
  hs1:hash_seq_pow2 ->
  hs2:hash_seq{S.length hs1 > S.length hs2} ->
  Lemma (iroots_of_hashes (S.append hs1 hs2) =
	S.append (iroots_of_hashes hs1) (iroots_of_hashes hs2))
let iroots_of_hashes_pow2_diff hs1 hs2 =
  pow2_floor_pow2_less (pow2_floor (S.length hs1)) (S.length hs2);
  lemma_split_append hs1 hs2;
  S.lemma_eq_elim
    (S.cons (merkle_root_of_pow2 hs1) (iroots_of_hashes hs2))
    (S.append (S.cons (merkle_root_of_pow2 hs1) S.empty)
	      (iroots_of_hashes hs2))

val iroots_of: elem_seq -> GTot hash_seq
let iroots_of vs = 
  iroots_of_hashes (seq_map hash_from_elem vs)

val iroots_of_pow2_same:
  vs1:elem_seq_pow2 ->
  vs2:elem_seq{S.length vs2 = S.length vs1} ->
  Lemma (iroots_of (S.append vs1 vs2) =
	S.create 1 (hash_from_hashes 
	  (S.index (iroots_of vs1) 0)
	  (S.index (iroots_of vs2) 0)))
let iroots_of_pow2_same vs1 vs2 =
  seq_map_append hash_from_elem vs1 vs2;
  iroots_of_hashes_pow2_same
    (seq_map hash_from_elem vs1)
    (seq_map hash_from_elem vs2)

val iroots_of_pow2_diff:
  vs1:elem_seq_pow2 ->
  vs2:elem_seq{S.length vs1 > S.length vs2} ->
  Lemma (iroots_of (S.append vs1 vs2) =
	S.append (iroots_of vs1) (iroots_of vs2))
let iroots_of_pow2_diff vs1 vs2 =
  seq_map_append hash_from_elem vs1 vs2;
  iroots_of_hashes_pow2_diff
    (seq_map hash_from_elem vs1)
    (seq_map hash_from_elem vs2)

/// High-level Merkle tree data structure

noeq type merkle_tree =
| MT: values:elem_seq{S.length values > 0} ->
      iroots:hash_seq{iroots = iroots_of values} ->
      merkle_tree

/// Creating a merkle tree instance

val create_merkle_tree: unit -> merkle_tree
let create_merkle_tree _ = 
  MT (S.create 1 elem_init) (S.create 1 (hash_from_elem elem_init))

/// Insertion

val insert_values: elem_seq -> elem -> GTot elem_seq
let insert_values vs nv = S.snoc vs nv

val merge_iroots:
  vs1:elem_seq_pow2 -> 
  irs1:hash_seq{iroots_of vs1 = irs1} ->
  vs2:elem_seq{S.length vs1 >= S.length vs2} ->
  irs2:hash_seq{iroots_of vs2 = irs2} ->
  GTot (mirs:hash_seq{iroots_of (S.append vs1 vs2) = mirs})
let merge_iroots vs1 irs1 vs2 irs2 =
  if S.length vs1 = S.length vs2
  then (iroots_of_pow2_same vs1 vs2; 
       S.create 1 (hash_from_hashes (S.index irs1 0) (S.index irs2 0)))
  else (iroots_of_pow2_diff vs1 vs2; 
       S.append irs1 irs2)

val iroots_of_head:
  vs:elem_seq{S.length vs > 0} ->
  Lemma (iroots_of (S.slice vs 0 (pow2 (pow2_floor (S.length vs)))) =
	S.create 1 (S.head (iroots_of vs)))
let iroots_of_head vs =
  let hs = seq_map hash_from_elem vs in
  let n_floor = pow2 (pow2_floor (S.length vs)) in
  assert (S.head (iroots_of vs) = merkle_root_of_pow2 (S.slice hs 0 n_floor))

val iroots_of_tail:
  vs:elem_seq{S.length vs > 0} ->
  Lemma (iroots_of (S.slice vs (pow2 (pow2_floor (S.length vs))) (S.length vs)) =
	S.tail (iroots_of vs))
let iroots_of_tail vs =
  let hs = seq_map hash_from_elem vs in
  let n_floor = pow2 (pow2_floor (S.length vs)) in
  S.lemma_tl (merkle_root_of_pow2 (S.slice hs 0 n_floor))
	     (iroots_of_hashes (S.slice hs n_floor (S.length hs)))

val insert_iroots:
  vs:elem_seq{S.length vs > 0} ->
  irs:hash_seq{iroots_of vs = irs} ->
  nv:elem ->
  GTot (iirs:hash_seq{iroots_of (insert_values vs nv) = iirs})
       (decreases (S.length irs))
#set-options "--z3rlimit 10"
let rec insert_iroots vs irs nv =
  if S.length vs = 0
  then (S.create 1 (hash_from_elem nv))
  else if is_pow2 (S.length vs)
  then merge_iroots vs irs (S.create 1 nv) (S.create 1 (hash_from_elem nv))
  else
    (let vs0, vs1 = S.split vs (pow2 (pow2_floor (S.length vs))) in
    lemma_split vs (pow2 (pow2_floor (S.length vs)));
    iroots_of_head vs;
    iroots_of_tail vs;
    append_assoc vs0 vs1 (S.create 1 nv);
    merge_iroots vs0 (S.create 1 (S.head irs)) (insert_values vs1 nv) 
		 (insert_iroots vs1 (S.tail irs) nv))

val insert: 
  mt:merkle_tree -> e:elem -> 
  GTot (imt:merkle_tree{
    MT?.values imt = insert_values (MT?.values mt) e &&
    MT?.iroots imt = insert_iroots (MT?.values mt) (MT?.iroots mt) e})
let insert mt e =
  let nvalues = insert_values (MT?.values mt) e in
  let niroots = insert_iroots (MT?.values mt) (MT?.iroots mt) e in
  MT nvalues niroots

/// Getting the Merkle root

val pad_hashes_pow2:
  vs:hash_seq{S.length vs > 0} -> 
  GTot (pvs:hash_seq{
    S.length pvs = pow2 (pow2_ceil (S.length vs)) && 
    S.slice pvs 0 (S.length vs) = vs})
let pad_hashes_pow2 vs =
  let pad = S.create (pow2 (pow2_ceil (S.length vs)) - S.length vs) hash_init in
  S.append_slices vs pad;
  S.append vs pad

val pad_hashes_pow2_pow2:
  vs:hash_seq{is_pow2 (S.length vs)} ->
  Lemma (pad_hashes_pow2 vs = vs)
let pad_hashes_pow2_pow2 vs = ()

val merkle_root_of_hashes: vs:hash_seq{S.length vs > 0} -> GTot hash
let merkle_root_of_hashes vs =
  merkle_root_of_pow2 (pad_hashes_pow2 vs)

val merkle_root_of_iroots: 
  irs:hash_seq{S.length irs > 0} -> 
  GTot hash (decreases (S.length irs))
let rec merkle_root_of_iroots irs =
  if S.length irs = 1 then S.index irs 0
  else hash_from_hashes (S.head irs) (merkle_root_of_iroots (S.tail irs))

val merkle_root_of_iroots_ok_hashes:
  vs:hash_seq{S.length vs > 0} ->
  irs:hash_seq{iroots_of_hashes vs = irs} ->
  Lemma (merkle_root_of_iroots irs = merkle_root_of_hashes vs)
#set-options "--z3rlimit 20"
let rec merkle_root_of_iroots_ok_hashes vs irs =
  if is_pow2 (S.length vs)
  then (assert (irs = S.cons (merkle_root_of_pow2 vs) S.empty);
       hash_init_idem (merkle_root_of_pow2 vs))
  else (assert (S.length irs > 1);
       assert (merkle_root_of_iroots irs =
	      hash_from_hashes (S.head irs) (merkle_root_of_iroots (S.tail irs)));
       let pvs = pad_hashes_pow2 vs in
       assert (merkle_root_of_hashes vs = merkle_root_of_pow2 pvs);
       assert (S.length pvs > 1);
       // assert (merkle_root_of_pow2 pvs =
       // 	      hash_from_hashes 
       // 	      	(merkle_root_of_pow2 (S.slice pvs 0 (S.length pvs / 2)))
       // 	      	(merkle_root_of_pow2 (S.slice pvs (S.length pvs / 2) (S.length pvs))));

       // not_pow2_floor_ceil (S.length vs);
       // Math.Lemmas.pow2_double_mult (pow2_floor (S.length vs));
       // assert (2 * pow2 (pow2_floor (S.length vs)) = pow2 (pow2_ceil (S.length vs)));
       // assert (pow2 (pow2_floor (S.length vs)) = pow2 (pow2_ceil (S.length vs)) / 2);
       // assert (S.head irs = merkle_root_of_pow2 (S.slice vs 0 (pow2 (pow2_floor (S.length vs)))));
       // !!! assume (S.head irs = merkle_root_of_pow2 (S.slice pvs 0 (S.length pvs / 2)));

       // assert (merkle_root_of_iroots (S.tail irs) =
       // 	      merkle_root_of_hashes (S.slice vs (pow2 (pow2_floor (length vs))) (length vs)));
       // TODO HERE: should prove that any length of padding will not change the merkle root value.
       // !!! assume (merkle_root_of_iroots (S.tail irs) =
       // 	      merkle_root_of_pow2 (S.slice pvs (S.length pvs / 2) (S.length pvs)));
       admit ())

val merkle_root_of_iroots_ok:
  mt:merkle_tree ->
  Lemma (merkle_root_of_iroots (MT?.iroots mt) =
	merkle_root_of_hashes (seq_map hash_from_elem (MT?.values mt)))
let merkle_root_of_iroots_ok mt =
  merkle_root_of_iroots_ok_hashes
    (seq_map hash_from_elem (MT?.values mt))
    (MT?.iroots mt)

