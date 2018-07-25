module MerkleTree.Low

// open MerkleTree.High
// open EverCrypt.Hash

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq
open FStar.Integers
open FStar.BitVector

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

// module High = MerkleTree.High

let root = Monotonic.HyperHeap.root

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

let hash_size = 32
// type hash = b:B.buffer uint8_t{B.length b = hash_size}
type hash = b:B.buffer uint8_t
let hash_buf = B.buffer hash

assume val hash_from_hashes: 
  src1:hash -> src2:hash -> dst:hash -> 
  HST.ST unit
	 (requires (fun h0 ->
	   B.live h0 src1 /\ B.live h0 src2 /\ B.live h0 dst))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer dst) h0 h1))

/// Power of 2

val uint32_pow2: 
  sz:uint32_t{sz < 32ul} -> Tot (p:uint32_t{U32.v p = pow2 (U32.v sz)})
let uint32_pow2 sz =
  let p = UInt32.shift_left 1ul sz in
  assume (U32.v p = pow2 (U32.v sz));
  p

val is_pow2: nat -> GTot bool
let rec is_pow2 n =
  if n = 0 then false
  else if n = 1 then true
  else (n % 2 = 0 && is_pow2 (n / 2))

val uint32_is_pow2: n:uint32_t -> Tot (b:bool{b = is_pow2 (U32.v n)})
let uint32_is_pow2 n =
  let b = n <> 0ul && UInt32.logor n (n -% 1ul) = 0ul in
  assume (b = is_pow2 (U32.v n));
  b

val pow2_floor: 
  n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
let rec pow2_floor n =
  if n = 1 then 0 else 1 + pow2_floor (n / 2)

val uint32_pow2_floor: 
  n:uint32_t{n > 0ul} ->
  Tot (p:uint32_t{
    p < 32ul && pow2 (U32.v p) <= U32.v n && U32.v n < pow2 (U32.v p + 1) &&
    pow2_floor (U32.v n) = U32.v p}) 
      (decreases (U32.v n))
let rec uint32_pow2_floor n =
  if n = 1ul then 0ul 
  else (UInt.shift_right_value_aux_3 (U32.v n) 1;
       assert (U32.v (UInt32.shift_right n 1ul) < U32.v n);
       assume (1 + U32.v (uint32_pow2_floor (UInt32.shift_right n 1ul)) < 32);
       let p = 1ul + uint32_pow2_floor (UInt32.shift_right n 1ul) in
       assume (p < 32ul && pow2 (U32.v p) <= U32.v n && U32.v n < pow2 (U32.v p + 1) &&
	      pow2_floor (U32.v n) = U32.v p);
       p)

val pow2_is_pow2:
  n:nat ->
  Lemma (is_pow2 (pow2 n))
	[SMTPat (is_pow2 (pow2 n))]
let rec pow2_is_pow2 n =
  if n = 0 then ()
  else pow2_is_pow2 (n - 1)

val pow2_floor_pow2:
  p:nat -> 
  Lemma (pow2_floor (pow2 p) = p)
	[SMTPat (pow2_floor (pow2 p))]
let rec pow2_floor_pow2 p =
  if p = 0 then ()
  else pow2_floor_pow2 (p - 1)

/// About hash buffer

val buffer_for_each:
  #a:Type -> h:HS.mem -> b:B.buffer a -> 
  prop:(a -> GTot Type0) -> GTot Type0
let buffer_for_each #a h b prop =
  forall (i:nat{i < B.length b}). prop (B.get h b i)

val buffer_for_each_gsub:
  #a:Type -> h:HS.mem -> b:B.buffer a ->
  prop:(a -> GTot Type0) ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (U32.v i + U32.v len <= B.length b /\
		  buffer_for_each h b prop))
	(ensures (buffer_for_each h (B.gsub b i len) prop))
let buffer_for_each_gsub #a h b prop i len =
  admit ()

val buffer_for_each_gsub_gsub:
  #a:Type -> h:HS.mem -> b:B.buffer a ->
  prop:(a -> GTot Type0) ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (B.length b = U32.v len /\ i <= len /\
		  buffer_for_each h (B.gsub b 0ul i) prop /\
		  buffer_for_each h (B.gsub b i (len - i)) prop))
	(ensures (buffer_for_each h b prop))
let buffer_for_each_gsub_gsub #a h b prop i len =
  admit ()

val hash_buf_allocated: 
  h:HS.mem -> hs:hash_buf -> GTot Type0
let hash_buf_allocated h hs =
  buffer_for_each h hs
  (fun hb -> B.live h hb /\ B.length hb = hash_size)

val hash_buf_allocated_gsub:
  h:HS.mem -> hs:hash_buf ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (U32.v i + U32.v len <= B.length hs /\
		  hash_buf_allocated h hs))
	(ensures (hash_buf_allocated h (B.gsub hs i len)))
let hash_buf_allocated_gsub h hs i len =
  buffer_for_each_gsub h hs 
  (fun hb -> B.live h hb /\ B.length hb = hash_size)
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
  buffer_for_each_gsub_gsub h hs 
  (fun hb -> B.live h hb /\ B.length hb = hash_size)
  i len

/// Allocation by power of two

val alloc_sz_lg:
  nelts:nat{nelts > 0} -> 
  GTot (sz:nat{sz > 0 && pow2 (sz - 1) <= nelts && nelts < pow2 sz})
let rec alloc_sz_lg nelts = pow2_floor nelts + 1

unfold val alloc_sz: nelts:nat -> GTot nat
unfold let alloc_sz nelts =
  if nelts = 0 then 0
  else pow2 (alloc_sz_lg nelts) - 1

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
| MT: nelts:uint32_t ->
      // The value buffer will be resized when elements are added.
      // Resizing mechanism will be similar to that of C++ vector.
      nvalues:uint32_t{nvalues >= nelts} ->
      values:hash_buf{B.length values = U32.v nvalues} ->
      // The actual number of internal roots should be equal to 
      // the number of "set" bits of `nelts`.
      iroots:hash_buf{B.length iroots = U32.n} ->
      merkle_tree

let mt_ptr = B.pointer merkle_tree

/// Initialization

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
#set-options "--z3rlimit 10"
let rec init_hashes len hs =
  if len = 0ul then ()
  else (B.upd hs 0ul (B.malloc root (UInt8.uint_to_t 0) (U32.uint_to_t hash_size));
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
	 (ensures (fun h0 mt h1 -> true))
let create_merkle_tree _ = 
  let values = B.null in
  let iroots = create_hashes 32ul in
  init_hashes 32ul iroots;
  B.malloc root (MT 0ul 0ul values iroots) 1ul

/// Insertion

// NOTE: it is using the `vs` pointer directly (not copying the hash value).
val insert_values:
  nelts:uint32_t{U32.v nelts < UInt.max_int U32.n} ->
  nvs:uint32_t{nvs >= nelts && U32.v nvs <= UInt.max_int U32.n} ->
  vs:hash_buf{B.length vs = U32.v nvs} ->
  e:hash{B.length e = hash_size} -> 
  HST.ST (ivs:hash_buf{B.length ivs = (if nelts = nvs then 2 * U32.v nelts + 1 else U32.v nvs)})
	 (requires (fun h0 -> B.live h0 e /\ B.live h0 vs /\ B.freeable vs))
	 (ensures (fun h0 ivs h1 -> B.live h1 ivs /\ B.freeable ivs))
let insert_values nelts nvs vs e =
  if nelts = nvs 
  then (assume (2 * U32.v nelts + 1 <= UInt.max_int U32.n);
       let ivs = create_hashes (2ul * nelts + 1ul) in
       LowStar.BufferOps.blit vs 0ul ivs 0ul nelts;
       B.upd ivs nelts e;
       init_hashes_partial nelts (nelts + 1ul) ivs;
       B.free vs;
       ivs)
  else (B.upd vs nelts e; vs)

val copy_hash: 
  src:hash{B.length src = hash_size} -> dst:hash{B.length dst = hash_size} -> 
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 src /\ B.live h0 dst /\ B.disjoint src dst))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer dst) h0 h1 /\
	   B.as_seq h1 dst = B.as_seq h0 src))
let copy_hash src dst =
  blit src 0ul dst 0ul (U32.uint_to_t hash_size)

val insert_iroots:
  nelts:uint32_t{U32.v nelts < UInt.max_int U32.n} ->
  nirs:uint32_t ->
  irs:hash_buf ->
  nv:hash{B.length nv = hash_size} ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 irs /\ hash_buf_allocated h0 irs /\
	   B.live h0 nv))
	 (ensures (fun h0 _ h1 -> true))
#set-options "--z3rlimit 20"
let rec insert_iroots nelts nirs irs nv =
  if nelts = 0ul
  then (assume (B.length irs > 0);
       let hh0 = HST.get () in assert (B.live hh0 (B.get hh0 irs 0));
       assume (B.disjoint nv (B.index irs 0ul));
       copy_hash nv (B.index irs 0ul))
  else (assume (nirs > 0ul);
       assume (B.length irs >= U32.v nirs);
       let hh0 = HST.get () in
       hash_buf_allocated_gsub hh0 irs 1ul (nirs - 1ul);
       insert_iroots (nelts - uint32_pow2 (uint32_pow2_floor nelts))
		     (nirs - 1ul)
		     (B.sub irs 1ul (nirs - 1ul))
		     nv;
       assume (uint32_pow2_floor nelts + 1ul < 32ul);
       if nelts + 1ul = uint32_pow2 (uint32_pow2_floor nelts + 1ul)
       then (let hh1 = HST.get () in
	    assume (B.length irs > 1);
	    assume (B.live hh1 irs);
	    assume (B.live hh1 (B.get hh1 irs 0));
	    assume (B.live hh1 (B.get hh1 irs 1));
	    hash_from_hashes (B.index irs 0ul) (B.index irs 1ul)
			     (B.index irs 0ul))
       else ())

val num_iroots_of: n:uint32_t -> Tot uint32_t (decreases (U32.v n))
let rec num_iroots_of n =
  if n = 0ul then 0ul
  else (assume (num_iroots_of (n / 2ul) < 32ul);
       n % 2ul + num_iroots_of (n / 2ul))

val insert:
  mt:mt_ptr ->
  e:hash{B.length e = hash_size} -> 
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ 
	   B.live h0 (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 (MT?.iroots (B.get h0 mt 0)) /\
	   B.freeable (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 e))
	 (ensures (fun h0 nmt h1 -> true))
let insert mt e =
  let mtv = B.index mt 0ul in
  if U32.v (MT?.nelts mtv) >= UInt.max_int U32.n then ()
  else (let nelts = MT?.nelts mtv in
       let nvalues = MT?.nvalues mtv in
       let inelts = nelts + 1ul in
       assume (2 * U32.v nelts + 1 <= UInt.max_int U32.n);
       let invalues = if nelts = nvalues then 2ul * nelts + 1ul else nvalues in
       let ivalues = insert_values nelts nvalues (MT?.values mtv) e in
       let nirs = num_iroots_of nelts in
       let hh0 = HST.get () in 
       assume (B.live hh0 (MT?.iroots mtv) /\ hash_buf_allocated hh0 (MT?.iroots mtv));
       assume (B.live hh0 e);
       insert_iroots nelts nirs (MT?.iroots mtv) e;
       let hh1 = HST.get () in 
       assume (B.live hh1 mt);
       B.upd mt 0ul (MT inelts invalues ivalues (MT?.iroots mtv)))

/// Getting the Merkle root

val merkle_root_of_iroots:
  nirs:uint32_t{U32.v nirs <= U32.n} ->
  irs:hash_buf{B.length irs = U32.v nirs} -> 
  acc:hash{B.length acc = hash_size} ->
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

