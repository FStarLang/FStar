module MerkleTree.Low

// TODO2: Use `EverCrypt.Hash` directly
// open EverCrypt.Hash

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq
open FStar.Integers
open FStar.Ghost

open MerkleTree.High
// TODO3: Use the vector library for hash values
// open LowStar.Vector

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
// module V = LowStar.Vector
module S = FStar.Seq

module High = MerkleTree.High

let root = Monotonic.HyperHeap.root

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

type hash = b:B.buffer uint8_t
type vhash = h:hash{B.length h = hash_size}
let hash_buf = B.buffer hash

// TODO2: When `EverCrypt.Hash` is connected if we define it.
assume val hash_from_hashes: 
  src1:vhash -> src2:vhash -> dst:vhash -> 
  HST.ST unit
	 (requires (fun h0 ->
	   B.live h0 src1 /\ B.live h0 src2 /\ B.live h0 dst))
	 (ensures (fun h0 _ h1 ->
	   // memory safety
	   modifies (loc_buffer dst) h0 h1 /\
	   // correctness
	   High.hash_from_hashes 
	     (B.as_seq h1 src1) 
	     (B.as_seq h1 src2) = B.as_seq h1 dst)) 

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
#set-options "--z3rlimit 40"
let rec uint32_num_of_ones sz n =
  if n = 0ul then 0ul
  else (let nones = n % 2ul + uint32_num_of_ones (hide (reveal sz - 1)) (n / 2ul) in
       assume (High.num_of_ones (U32.v n) = U32.v nones);
       nones)

/// About hash buffer

val buffer_forall:
  #a:Type -> h:HS.mem -> b:B.buffer a -> 
  prop:(a -> GTot Type0) -> GTot Type0
let buffer_forall #a h b prop =
  forall (i:nat{i < B.length b}). prop (B.get h b i)

val buffer_forall_gsub:
  #a:Type -> h:HS.mem -> b:B.buffer a ->
  prop:(a -> GTot Type0) ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (U32.v i + U32.v len <= B.length b /\
		  buffer_forall h b prop))
	(ensures (buffer_forall h (B.gsub b i len) prop))
let buffer_forall_gsub #a h b prop i len =
  assert (forall (j:nat{j < B.length (B.gsub b i len)}).
	 B.get h (B.gsub b i len) j == B.get h b (U32.v i + j))

val buffer_forall_gsub_gsub:
  #a:Type -> h:HS.mem -> b:B.buffer a ->
  prop:(a -> GTot Type0) ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (B.length b = U32.v len /\ i <= len /\
		  buffer_forall h (B.gsub b 0ul i) prop /\
		  buffer_forall h (B.gsub b i (len - i)) prop))
	(ensures (buffer_forall h b prop))
let buffer_forall_gsub_gsub #a h b prop i len =
  assert (forall (j:nat{j < U32.v i}). B.get h b j == B.get h (B.gsub b 0ul i) j);
  assert (forall (j:nat{j >= U32.v i && j < B.length b}).
	 B.get h b j == B.get h (B.gsub b i (len - i)) (j - U32.v i))

val hash_buf_allocated: 
  h:HS.mem -> hs:hash_buf -> GTot Type0
let hash_buf_allocated h hs =
  buffer_forall h hs
  (fun hb -> 
    B.live h hb /\ 
    B.length hb = hash_size /\ 
    B.freeable hb)

val hash_buf_allocated_gsub:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (U32.v i + U32.v len <= B.length hs /\
		  hash_buf_allocated h hs))
	(ensures (hash_buf_allocated h (B.gsub hs i len)))
let hash_buf_allocated_gsub h hs i len =
  buffer_forall_gsub h hs 
  (fun hb -> B.live h hb /\ B.length hb = hash_size /\ B.freeable hb)
  i len

val hash_buf_allocated_gsub_gsub:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (B.length hs = U32.v len /\ i <= len /\
		  hash_buf_allocated h (B.gsub hs 0ul i) /\
		  hash_buf_allocated h (B.gsub hs i (len - i))))
	(ensures (hash_buf_allocated h hs))
	[SMTPat (hash_buf_allocated h (B.gsub hs 0ul i));
	SMTPat (hash_buf_allocated h (B.gsub hs i (len - i)))]
let hash_buf_allocated_gsub_gsub h hs i len =
  buffer_forall_gsub_gsub h hs 
  (fun hb -> B.live h hb /\ B.length hb = hash_size /\ B.freeable hb)
  i len

val hash_buf_allocated_gsub_hd_tl:
  h:HS.mem -> hs:hash_buf ->
  len:uint32_t{len > 0ul} ->
  Lemma (requires (B.length hs = U32.v len /\
		  B.live h (B.get h hs 0) /\ B.length (B.get h hs 0) = hash_size /\
		  B.freeable (B.get h hs 0) /\
		  hash_buf_allocated h (B.gsub hs 1ul (len - 1ul))))
	(ensures (hash_buf_allocated h hs))
	[SMTPat (hash_buf_allocated h (B.gsub hs 1ul (len - 1ul)))]
let hash_buf_allocated_gsub_hd_tl h hs len =
  buffer_forall_gsub_gsub h hs 
  (fun hb -> B.live h hb /\ B.length hb = hash_size /\ B.freeable hb)
  1ul len

val loc_hashes: 
  h:HS.mem -> hs:hash_buf -> 
  GTot loc (decreases (B.length hs))
let rec loc_hashes h hs =
  if B.length hs = 0 then loc_none
  else loc_union (loc_buffer (B.get h hs 0)) 
		 (loc_hashes h (B.gsub hs 1ul (B.len hs - 1ul)))

val loc_hashes_as_seq_eq:
  hs:hash_buf -> h1:HS.mem -> h2:HS.mem ->
  Lemma (requires (B.as_seq h1 hs == B.as_seq h2 hs))
  	(ensures (loc_hashes h1 hs == loc_hashes h2 hs))
	(decreases (B.length hs))
	[SMTPat (B.as_seq h1 hs); SMTPat (B.as_seq h2 hs)]
let rec loc_hashes_as_seq_eq hs h1 h2 =
  if B.length hs = 0 then ()
  else loc_hashes_as_seq_eq (B.gsub hs 1ul (B.len hs - 1ul)) h1 h2

val loc_includes_union_left:
  s1: loc -> s2: loc ->
  Lemma (loc_includes (loc_union s1 s2) s1)
let loc_includes_union_left s1 s2 =
  loc_includes_union_l s1 s2 s1

val loc_includes_union_right:
  s1: loc -> s2: loc ->
  Lemma (loc_includes (loc_union s1 s2) s2)
let loc_includes_union_right s1 s2 =
  loc_includes_union_l s1 s2 s2

val loc_includes_union_lift_left:
  s: loc -> s1: loc -> s2: loc ->
  Lemma (requires (loc_includes s1 s2))
	(ensures (loc_includes (loc_union s s1) (loc_union s s2)))
let loc_includes_union_lift_left s s1 s2 =
  loc_includes_union_left s s1;
  loc_includes_union_right s s1;
  loc_includes_union_r (loc_union s s1) s s2

val loc_includes_union_lift_right:
  s: loc -> s1: loc -> s2: loc ->
  Lemma (requires (loc_includes s1 s2))
	(ensures (loc_includes (loc_union s1 s) (loc_union s2 s)))
let loc_includes_union_lift_right s s1 s2 =
  loc_includes_union_left s1 s;
  loc_includes_union_right s1 s;
  loc_includes_union_r (loc_union s1 s) s s2

val loc_hashes_gsub_includes':
  h:HS.mem -> hs:hash_buf -> len:uint32_t ->
  Lemma (requires (U32.v len <= B.length hs))
	(ensures (loc_includes (loc_hashes h hs) 
			       (loc_hashes h (B.gsub hs 0ul len))))
	(decreases (B.length hs))
let rec loc_hashes_gsub_includes' h hs len =
  if len = 0ul then ()
  else (loc_hashes_gsub_includes' h (B.gsub hs 1ul (B.len hs - 1ul)) (len - 1ul);
       loc_includes_union_lift_left (loc_buffer (B.get h hs 0))
				    (loc_hashes h (B.gsub hs 1ul (B.len hs - 1ul)))
				    (loc_hashes h (B.gsub (B.gsub hs 0ul len) 1ul (len - 1ul))))

val loc_hashes_gsub_includes:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (U32.v i + U32.v len <= B.length hs))
	(ensures (loc_includes (loc_hashes h hs) 
			       (loc_hashes h (B.gsub hs i len))))
	(decreases (B.length hs))
let rec loc_hashes_gsub_includes h hs i len =
  if len = 0ul then ()
  else if i = 0ul then loc_hashes_gsub_includes' h hs len
  else (loc_hashes_gsub_includes h (B.gsub hs 1ul (B.len hs - 1ul)) (i - 1ul) len;
       loc_includes_union_right (loc_buffer (B.get h hs 0))
				(loc_hashes h (B.gsub hs 1ul (B.len hs - 1ul))))

val hash_buf_disjoint_ext:
  h:HS.mem -> hs:hash_buf -> 
  #a:Type -> e:B.buffer a -> GTot Type0
let hash_buf_disjoint_ext h hs #a e =
  loc_disjoint (loc_hashes h hs) (loc_buffer e)

val hash_buf_disjoint_ext_gsub:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  #a:Type -> e:B.buffer a ->
  Lemma (requires (U32.v i + U32.v len <= B.length hs /\
		  hash_buf_disjoint_ext h hs e))
	(ensures (hash_buf_disjoint_ext h (B.gsub hs i len) e))
let hash_buf_disjoint_ext_gsub h hs i len #a e =
  loc_hashes_gsub_includes h hs i len

val loc_hashes_gsub_gsub:
  h:HS.mem -> hs:hash_buf -> i:uint32_t ->
  Lemma (requires (U32.v i <= B.length hs))
	(ensures (loc_hashes h hs ==
		 loc_union (loc_hashes h (B.gsub hs 0ul i))
			   (loc_hashes h (B.gsub hs i (B.len hs - i)))))
	(decreases (U32.v i))
#set-options "--z3rlimit 20"
let rec loc_hashes_gsub_gsub h hs i =
  if i = 0ul then ()
  else (loc_hashes_gsub_gsub h (B.gsub hs 1ul (B.len hs - 1ul)) (i - 1ul);
       loc_union_assoc
	 (loc_buffer (B.get h hs 0))
	 (loc_hashes h (B.gsub (B.gsub hs 1ul (B.len hs - 1ul)) 0ul (i - 1ul)))
	 (loc_hashes h (B.gsub (B.gsub hs 1ul (B.len hs - 1ul)) (i - 1ul) (B.len hs - i))))

val hash_buf_disjoint_ext_gsub_gsub:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  #a:Type -> e:B.buffer a ->
  Lemma (requires (B.length hs = U32.v len /\ i <= len /\
		  hash_buf_disjoint_ext h (B.gsub hs 0ul i) e /\
		  hash_buf_disjoint_ext h (B.gsub hs i (len - i)) e))
	(ensures (hash_buf_disjoint_ext h hs e))
	[SMTPat (hash_buf_disjoint_ext h (B.gsub hs 0ul i) e);
	SMTPat (hash_buf_disjoint_ext h (B.gsub hs i (len - i)) e)]
let hash_buf_disjoint_ext_gsub_gsub h hs i len #a e =
  loc_disjoint_union_r 
    (loc_buffer e) 
    (loc_hashes h (B.gsub hs 0ul i))
    (loc_hashes h (B.gsub hs i (len - i)));
  loc_hashes_gsub_gsub h hs i

val hash_buf_disjoint:
  h:HS.mem -> hs:hash_buf -> GTot Type0 (decreases (B.length hs))
let rec hash_buf_disjoint h hs =
// forall (i:nat{i < B.length hs}) (j:nat{j < B.length hs}).
//   i <> j ==> (B.disjoint (B.get h hs i) (B.get h hs j))
  if B.length hs = 0 then True
  else (let ths = B.gsub hs 1ul (B.len hs - 1ul) in
       loc_disjoint (loc_buffer (B.get h hs 0)) (loc_hashes h ths) /\
       hash_buf_disjoint h ths)

/// Low-level Merkle tree data structure

noeq type merkle_tree =
| MT: nelts:uint32_t ->
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      nvalues:uint32_t{nvalues >= nelts} ->
      nvsz:erased nat{U32.v nvalues = pow2 (reveal nvsz) - 1} ->
      values:hash_buf{B.length values = U32.v nvalues} ->
      // The actual number of internal root values should be equal to 
      // the number of "set" bits of `nelts`. The maximum number is
      // U32.n (=32), so we pre-allocate the buffer.
      iroots:hash_buf{B.length iroots = U32.n} ->
      merkle_tree

let mt_ptr = B.pointer merkle_tree

// val hashes_as_seq: HS.mem -> hash_buf -> GTot High.hash_seq
val hashes_as_seq: 
  h:HS.mem -> hb:hash_buf{hash_buf_allocated h hb} ->
  GTot (hs:High.hash_seq{S.length hs = B.length hb})
       (decreases (B.length hb))
let rec hashes_as_seq h hb =
  if B.length hb = 0 then S.empty
  else (hash_buf_allocated_gsub h hb 1ul (B.len hb - 1ul);
       S.cons (B.as_seq h (B.get h hb 0))
	      (hashes_as_seq h (B.gsub hb 1ul (B.len hb - 1ul))))

// val hashes_as_seq_gsub:
//   h:HS.mem -> hb:hash_buf{hash_buf_allocated h hb} ->
//   i:uint32_t ->
//   len:uint32_t{U32.v i + U32.v len <= B.length hb} ->
//   Lemma (ensures (hashes_as_seq h (B.gsub hb i len) =
// 		 S.slice (hashes_as_seq h hb) (U32.v i) (U32.v i + U32.v len)))
// 	(decreases (U32.v len))
// 	[SMTPat (hashes_as_seq h hb); SMTPat (B.gsub hb i len)]
// let rec hashes_as_seq_gsub h hb i len =
//   // if len = 0ul then ()
//   // else hashes_as_seq_gsub h hb (i + 1ul) (len - 1ul)
//   admit ()

// val hashes_as_seq_gsub_gsub:
//   h:HS.mem -> hb:hash_buf{hash_buf_allocated h hb} ->
//   len:uint32_t{U32.v len = B.length hb} ->
//   i:uint32_t{i < len} ->
//   Lemma (ensures (hashes_as_seq h hb =
// 		 S.append (hashes_as_seq h (B.gsub hb 0ul i))
// 			  (hashes_as_seq h (B.gsub hb i (len - i)))))
// 	[SMTPat (hashes_as_seq h (B.gsub hb 0ul i));
// 	SMTPat (hashes_as_seq h (B.gsub hb i (len - i)))]
// let hashes_as_seq_gsub_gsub h hb len i =
//   admit ()

val merkle_tree_wf: HS.mem -> merkle_tree -> GTot Type0
let merkle_tree_wf h mt =
  let nelts = MT?.nelts mt in
  let nirs = uint32_num_of_ones (hide 32) nelts in
  let values = B.gsub (MT?.values mt) 0ul nelts in
  let iroots = B.gsub (MT?.iroots mt) 0ul nirs in
  hash_buf_allocated h values /\
  hash_buf_allocated h iroots /\
  iroots_of_hashes (hashes_as_seq h values) = hashes_as_seq h iroots

val lift_mt: 
  h:HS.mem -> mt:merkle_tree{merkle_tree_wf h mt} -> 
  GTot High.merkle_tree
let lift_mt h mt =
  let nelts = MT?.nelts mt in
  let nirs = uint32_num_of_ones (hide 32) nelts in
  let values = hashes_as_seq h (B.gsub (MT?.values mt) 0ul nelts) in
  let iroots = hashes_as_seq h (B.gsub (MT?.iroots mt) 0ul nirs) in
  High.MT values iroots

/// Initialization

// Allocate a buffer storing "pointers" to hashes.
// The initial value for each pointer is null.
val create_hashes:
  len:uint32_t{len > 0ul} ->
  HST.ST hash_buf
	 (requires (fun h0 -> true))
	 (ensures (fun h0 hs h1 ->
	   B.unused_in hs h0 /\ B.live h1 hs /\
	   B.length hs = U32.v len /\
	   modifies loc_none h0 h1 /\
	   B.freeable hs))
let create_hashes len = 
  B.malloc root B.null len

val init_hashes: 
  len:uint32_t -> hs:hash_buf{B.length hs = U32.v len} ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 hs))
	 (ensures (fun h0 _ h1 ->
	   hash_buf_allocated h1 hs /\
	   B.live h1 hs /\ 
	   modifies (loc_buffer hs) h0 h1))
let rec init_hashes len hs =
  if len = 0ul then ()
  else (B.upd hs 0ul (B.malloc root (UInt8.uint_to_t 0) 32ul);
       init_hashes (len - 1ul) (B.sub hs 1ul (len - 1ul));
       let hh = HST.get () in
       assert (hash_buf_allocated hh (B.gsub hs 0ul 1ul)))

val init_hashes_partial:
  idx:uint32_t -> len:uint32_t -> 
  hs:hash_buf{U32.v idx + U32.v len <= B.length hs} ->
  HST.ST unit
	 (requires (fun h0 -> B.live h0 hs))
	 (ensures (fun h0 _ h1 ->
	   hash_buf_allocated h1 (B.gsub hs idx len) /\
	   B.live h1 hs /\ 
	   modifies (loc_buffer (B.gsub hs idx len)) h0 h1))
let rec init_hashes_partial idx len hs =
  init_hashes len (B.sub hs idx len)

val create_merkle_tree: unit -> 
  HST.ST mt_ptr
	 (requires (fun _ -> true))
	 (ensures (fun h0 mt h1 ->
	   merkle_tree_wf h1 (B.get h1 mt 0)))
let create_merkle_tree _ = 
  let values = B.null in
  let iroots = create_hashes 32ul in
  init_hashes 32ul iroots;
  B.malloc root (MT 0ul 0ul (hide 0) values iroots) 1ul

/// Insertion

// NOTE: it DIRECTLY stores the `vs` pointer value (not copying the hash value).
val insert_values:
  mt:erased mt_ptr ->
  nelts:uint32_t{U32.v nelts < UInt.max_int U32.n} ->
  nvs:uint32_t{nvs >= nelts} ->
  nvsz:erased nat{U32.v nvs = pow2 (reveal nvsz) - 1} ->  
  vs:hash_buf{B.length vs = U32.v nvs} ->
  e:vhash ->
  HST.ST (ivs:hash_buf{B.length ivs = (if nelts = nvs then 2 * U32.v nelts + 1 else U32.v nvs)})
	 (requires (fun h0 ->
	   // hash_buf_allocated h0 (B.gsub vs 0ul nelts) /\
	   B.live h0 e /\ B.freeable e /\ 
	   B.live h0 vs /\ B.freeable vs /\
	   B.live h0 (reveal mt) /\ B.disjoint (reveal mt) vs))
	 (ensures (fun h0 ivs h1 ->
	   // memory safety
	   // hash_buf_allocated h1 (B.gsub ivs 0ul (nelts + 1ul)) /\
	   B.live h1 ivs /\ B.freeable ivs /\
	   modifies (loc_union (loc_buffer ivs) (loc_addr_of_buffer vs)) h0 h1 /\
	   B.disjoint (reveal mt) ivs))
	   // correctness
	   // High.insert_values 
	   //   (hashes_as_seq h0 (B.gsub vs 0ul nelts))
	   //   (B.as_seq h0 e) =
	   // hashes_as_seq h1 (B.gsub ivs 0ul (nelts + 1ul))))
#set-options "--z3rlimit 20"
let insert_values mt nelts nvs nvsz vs e =
  if nelts = nvs
  then (let hh0 = HST.get () in
       pow2_lt_compat_inv (reveal nvsz) U32.n;
       assert (2 * U32.v nelts + 1 <= UInt.max_int U32.n);
       let ivs = create_hashes (2ul * nelts + 1ul) in
       LowStar.BufferOps.blit vs 0ul ivs 0ul nelts;
       B.upd ivs nelts e;
       // init_hashes_partial nelts (nelts + 1ul) ivs;
       B.free vs;
       ivs)
  else (B.upd vs nelts e;
       // let hh0 = HST.get () in
       // hash_buf_allocated_gsub_gsub hh0 (B.gsub vs 0ul (nelts + 1ul)) nelts (nelts + 1ul);
       vs)

val copy_hash: 
  src:vhash -> dst:vhash -> 
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 src /\ B.live h0 dst /\ B.disjoint src dst))
	 (ensures (fun h0 _ h1 ->
	   B.live h1 src /\ B.live h1 dst /\
	   modifies (loc_buffer dst) h0 h1 /\
	   B.as_seq h1 dst = B.as_seq h0 src))
let copy_hash src dst =
  blit src 0ul dst 0ul 32ul

val insert_iroots:
  nirs:erased nat{reveal nirs <= U32.n} ->
  nelts:uint32_t{U32.v nelts < pow2 (reveal nirs) - 1} ->
  irs:hash_buf{B.length irs = reveal nirs} ->
  nv:vhash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 irs /\ hash_buf_allocated h0 irs /\ B.live h0 nv /\ 
	   B.disjoint irs nv /\ hash_buf_disjoint_ext h0 irs nv /\
	   hash_buf_disjoint_ext h0 irs irs /\
	   hash_buf_disjoint h0 irs))
	 (ensures (fun h0 _ h1 -> 
	   modifies (loc_hashes h0 irs) h0 h1 /\ // only affects internal root hash values
	   hash_buf_allocated h1 irs)) // internal roots are still alive!
#set-options "--z3rlimit 60"
let rec insert_iroots nirs nelts irs nv =
  let hh0 = HST.get () in
  if nelts = 0ul
  then copy_hash nv (B.index irs 0ul)
  else (hash_buf_allocated_gsub hh0 irs 1ul (B.len irs - 1ul);
       hash_buf_disjoint_ext_gsub hh0 irs 1ul (B.len irs - 1ul) nv;
       hash_buf_disjoint_ext_gsub hh0 irs 1ul (B.len irs - 1ul) irs;
       
       insert_iroots (hide (reveal nirs - 1))
		     (nelts - uint32_pow2 (uint32_pow2_floor nelts))
		     (B.offset irs 1ul) nv;

       let hh1 = HST.get () in
       let tirs = B.offset irs 1ul in
       B.modifies_buffer_elim (B.get hh1 irs 0) (loc_hashes hh1 tirs) hh0 hh1;
       modifies_union_weakened_right (loc_buffer (B.get hh0 irs 0))
       				     (loc_hashes hh0 tirs)
       				     hh0 hh1);
       Math.Lemmas.pow2_le_compat U32.n (reveal nirs);

       if uint32_is_pow2 (nelts + 1ul)
       then hash_from_hashes (B.index irs 0ul) (B.index irs 1ul)
       	    		     (B.index irs 0ul)
       else ()

val insert_maximum_helper:
  sz:nat -> n:uint32_t{U32.v n = pow2 sz - 1 && U32.v n < UInt.max_int U32.n} ->
  Lemma (2 * U32.v n + 1 <= UInt.max_int U32.n)
let insert_maximum_helper sz n =
  pow2_lt_compat_inv sz U32.n

val insert:
  mt:mt_ptr -> e:vhash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   let mtv = B.get h0 mt 0 in
	   let nelts = MT?.nelts mtv in
	   let values = MT?.values mtv in
	   let iroots = MT?.iroots mtv in

	   U32.v nelts < UInt.max_int U32.n /\

	   B.live h0 mt /\
	   B.live h0 values /\
	   B.freeable values /\
	   // `B.disjoint mt values` should be better.
	   loc_disjoint (loc_buffer mt) (loc_addr_of_buffer values) /\

	   B.live h0 iroots /\
	   hash_buf_allocated h0 iroots /\
	   hash_buf_disjoint h0 iroots /\
	   hash_buf_disjoint_ext h0 iroots iroots /\
	   
	   B.live h0 e /\ B.freeable e /\
	   B.disjoint iroots e /\
	   hash_buf_disjoint_ext h0 iroots e /\
	   hash_buf_disjoint_ext h0 iroots values /\
	   hash_buf_disjoint_ext h0 iroots mt))
	 (ensures (fun h0 _ h1 -> true))
let insert mt e =
  let mtv = B.index mt 0ul in
  let nelts = MT?.nelts mtv in
  let values = MT?.values mtv in
  let nvalues = MT?.nvalues mtv in
  let iroots = MT?.iroots mtv in
  insert_iroots (hide 32) nelts iroots e;

  let inelts = nelts + 1ul in
  let invalues = 
    if nelts = nvalues 
    then (insert_maximum_helper (reveal (MT?.nvsz mtv)) nelts;
	 2ul * nelts + 1ul)
    else nvalues in
  let invsz = hide (if nelts = nvalues then reveal (MT?.nvsz mtv) + 1 else reveal (MT?.nvsz mtv)) in
  // let hh1 = HST.get () in assert (B.live hh1 mt);
  let ivalues = insert_values (hide mt) nelts nvalues (MT?.nvsz mtv) values e in
  loc_disjoint_union_r (loc_buffer mt)
		       (loc_buffer ivalues)
		       (loc_addr_of_buffer values);
  // let hh2 = HST.get () in assert (B.live hh2 mt);
  B.upd mt 0ul (MT inelts invalues invsz ivalues iroots)

/// Getting the Merkle root

val merkle_root_of_iroots:
  nirs:uint32_t{U32.v nirs <= U32.n} ->
  irs:hash_buf{B.length irs >= U32.v nirs} -> 
  acc:vhash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 irs /\ hash_buf_allocated h0 irs /\
	   B.live h0 acc /\ B.disjoint irs acc))
	 (ensures (fun h0 _ h1 -> 
	   B.live h1 acc /\ modifies (loc_buffer acc) h0 h1))
let rec merkle_root_of_iroots nirs irs acc =
  if nirs = 0ul then ()
  else (let hh0 = HST.get () in
       hash_buf_allocated_gsub hh0 irs 1ul (nirs - 1ul);
       assert (B.live hh0 (B.get hh0 irs 0));
       merkle_root_of_iroots (nirs - 1ul) (B.sub irs 1ul (nirs - 1ul)) acc;
       let hh1 = HST.get () in
       assert (B.live hh1 (B.get hh1 irs 0));
       hash_from_hashes (B.index irs 0ul) acc acc)

val get_root:
  mt:mt_ptr -> rt:vhash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ 
	   B.live h0 (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 (MT?.iroots (B.get h0 mt 0)) /\
	   hash_buf_allocated h0 (MT?.iroots (B.get h0 mt 0)) /\
	   B.freeable (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 rt /\
	   B.disjoint (MT?.iroots (B.get h0 mt 0)) rt))
	 (ensures (fun h0 _ h1 -> true))
let get_root mt rt =
  let mtv = B.index mt 0ul in
  let nelts = MT?.nelts mtv in
  let irs = MT?.iroots mtv in
  let nirs = uint32_num_of_ones (hide 32) nelts in
  merkle_root_of_iroots nirs irs rt

/// Freeing the Merkle tree

val free_hashes:
  len:uint32_t ->
  hs:hash_buf{B.length hs = U32.v len} ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 hs /\ hash_buf_allocated h0 hs /\
	   hash_buf_disjoint h0 hs /\
	   hash_buf_disjoint_ext h0 hs hs))
	 (ensures (fun h0 _ h1 -> modifies (loc_hashes h0 hs) h0 h1))
	 (decreases (U32.v len))
let rec free_hashes len hs = 
  if len = 0ul then ()
  else (let hh0 = HST.get () in
       hash_buf_allocated_gsub hh0 hs 1ul (len - 1ul);
       hash_buf_disjoint_ext_gsub hh0 hs 1ul (len - 1ul) hs;
       free_hashes (len - 1ul) (B.sub hs 1ul (len - 1ul));

       B.free (B.index hs 0ul);
       
       let hh1 = HST.get () in
       assume (modifies (loc_hashes hh0 hs) hh0 hh1))

val free_merkle_tree: 
  mt:mt_ptr ->
  HST.ST unit
	 (requires (fun h0 -> 
	   let mtv = B.get h0 mt 0 in
	   let nelts = MT?.nelts mtv in
	   let values = MT?.values mtv in
	   let values_alloc = B.gsub values 0ul nelts in
	   let iroots = MT?.iroots mtv in

	   B.live h0 mt /\ B.freeable mt /\
	   B.live h0 values /\ B.freeable values /\
	   hash_buf_allocated h0 values_alloc /\
	   hash_buf_disjoint h0 values_alloc /\
	   hash_buf_disjoint_ext h0 values_alloc values /\
	   hash_buf_disjoint_ext h0 values_alloc mt /\
	   
	   B.live h0 iroots /\ B.freeable iroots /\
	   hash_buf_allocated h0 iroots /\
	   hash_buf_disjoint h0 iroots /\
	   hash_buf_disjoint_ext h0 iroots iroots /\
	   hash_buf_disjoint_ext h0 iroots values /\
	   hash_buf_disjoint_ext h0 iroots mt /\

	   B.disjoint values iroots /\
	   B.disjoint values mt /\
	   B.disjoint iroots mt))
	 (ensures (fun h0 _ h1 -> true))
#set-options "--z3rlimit 40"
let free_merkle_tree mt =
  let mtv = B.index mt 0ul in
  let nelts = MT?.nelts mtv in
  let values = MT?.values mtv in
  let values_alloc = B.sub values 0ul nelts in
  let iroots = MT?.iroots mtv in
  free_hashes 32ul iroots;
  B.free iroots;
  
  let hh0 = HST.get () in
  assume (B.live hh0 values /\ B.freeable values /\
  	 hash_buf_allocated hh0 values_alloc /\
  	 hash_buf_disjoint hh0 values_alloc /\
  	 hash_buf_disjoint_ext hh0 values_alloc values);
  free_hashes nelts values_alloc;
  B.free values;

  let hh1 = HST.get () in 
  assume (B.live hh1 mt /\ B.freeable mt);
  B.free mt

