module MerkleTree.Low

// TODO1: Use high-level spec for correctness
// open MerkleTree.High

// TODO2: Use `EverCrypt.Hash` directly
// open EverCrypt.Hash

open FStar.All
open FStar.Mul
open LowStar.Modifies
open LowStar.BufferOps
open FStar.Seq
open FStar.Integers
open FStar.Ghost

module List = FStar.List.Tot
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module S = FStar.Seq

// TODO1
// module High = MerkleTree.High

let root = Monotonic.HyperHeap.root

module U32 = FStar.UInt32
module U8 = FStar.UInt8
type uint32_t = U32.t
type uint8_t = U8.t

noextract val hash_size: nat
noextract let hash_size = 32
type hash = b:B.buffer uint8_t
type vhash = h:hash{B.length h = hash_size}
let hash_buf = B.buffer hash

// TODO2: When `EverCrypt.Hash` is connected if we define it.
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
  Math.Lemmas.pow2_lt_compat U32.n (U32.v sz);
  UInt32.shift_left 1ul sz

val is_pow2: nat -> GTot bool
let rec is_pow2 n =
  if n = 0 then false
  else if n = 1 then true
  else (n % 2 = 0 && is_pow2 (n / 2))

val pow2_floor: 
  n:nat{n > 0} -> GTot (p:nat{pow2 p <= n && n < pow2 (p + 1)})
let rec pow2_floor n =
  if n = 1 then 0 else 1 + pow2_floor (n / 2)

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

val pow2_is_pow2:
  n:nat ->
  Lemma (is_pow2 (pow2 n))
	[SMTPat (is_pow2 (pow2 n))]
let rec pow2_is_pow2 n =
  if n = 0 then ()
  else pow2_is_pow2 (n - 1)

val pow2_lt_compat_inv:
  p:nat -> q:nat ->
  Lemma (requires (pow2 p < pow2 q))
	(ensures (p < q))
let rec pow2_lt_compat_inv p q =
  if q <= p then Math.Lemmas.pow2_le_compat p q
  else ()

val pow2_le_compat_inv:
  p:nat -> q:nat ->
  Lemma (requires (pow2 p <= pow2 q))
	(ensures (p <= q))
let rec pow2_le_compat_inv p q =
  if q < p then Math.Lemmas.pow2_lt_compat p q
  else ()

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
  assert (forall (j:nat{j < B.length (B.gsub b i len)}).
	 B.get h (B.gsub b i len) j == B.get h b (U32.v i + j))

val buffer_for_each_gsub_gsub:
  #a:Type -> h:HS.mem -> b:B.buffer a ->
  prop:(a -> GTot Type0) ->
  i:uint32_t -> len:uint32_t ->
  Lemma (requires (B.length b = U32.v len /\ i <= len /\
		  buffer_for_each h (B.gsub b 0ul i) prop /\
		  buffer_for_each h (B.gsub b i (len - i)) prop))
	(ensures (buffer_for_each h b prop))
let buffer_for_each_gsub_gsub #a h b prop i len =
  assert (forall (j:nat{j < U32.v i}). B.get h b j == B.get h (B.gsub b 0ul i) j);
  assert (forall (j:nat{j >= U32.v i && j < B.length b}).
	 B.get h b j == B.get h (B.gsub b i (len - i)) (j - U32.v i))

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
	 (ensures (fun h0 mt h1 -> true))
let create_merkle_tree _ = 
  let values = B.null in
  let iroots = create_hashes 32ul in
  init_hashes 32ul iroots;
  B.malloc root (MT 0ul 0ul (hide 0) values iroots) 1ul

/// Insertion

// NOTE: it DIRECTLY stores the `vs` pointer value (not copying the hash value).
val insert_values:
  nelts:uint32_t{U32.v nelts < UInt.max_int U32.n} ->
  nvs:uint32_t{nvs >= nelts} ->
  nvsz:erased nat{U32.v nvs = pow2 (reveal nvsz) - 1} ->  
  vs:hash_buf{B.length vs = U32.v nvs} ->
  e:vhash ->
  HST.ST (ivs:hash_buf{B.length ivs = (if nelts = nvs then 2 * U32.v nelts + 1 else U32.v nvs)})
	 (requires (fun h0 -> B.live h0 e /\ B.live h0 vs /\ B.freeable vs))
	 (ensures (fun h0 ivs h1 -> B.live h1 ivs /\ B.freeable ivs))
#set-options "--z3rlimit 20"
let insert_values nelts nvs nvsz vs e =
  if nelts = nvs 
  then (pow2_lt_compat_inv (reveal nvsz) U32.n;
       assert (2 * U32.v nelts + 1 <= UInt.max_int U32.n);
       let ivs = create_hashes (2ul * nelts + 1ul) in
       LowStar.BufferOps.blit vs 0ul ivs 0ul nelts;
       B.upd ivs nelts e;
       init_hashes_partial nelts (nelts + 1ul) ivs;
       B.free vs;
       ivs)
  else (B.upd vs nelts e; vs)

val copy_hash: 
  src:vhash -> dst:vhash -> 
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 src /\ B.live h0 dst /\ B.disjoint src dst))
	 (ensures (fun h0 _ h1 ->
	   modifies (loc_buffer dst) h0 h1 /\
	   B.as_seq h1 dst = B.as_seq h0 src))
let copy_hash src dst =
  blit src 0ul dst 0ul 32ul

val insert_iroots:
  nelts:uint32_t{U32.v nelts < UInt.max_int U32.n} ->
  nirs:uint32_t ->
  irs:hash_buf ->
  nv:vhash ->
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

val num_iroots_of:
  n:uint32_t -> 
  Tot (nirs:uint32_t{U32.v nirs <= U32.n}) 
      (decreases (U32.v n))
let rec num_iroots_of n =
  if n = 0ul then 0ul
  else (assume (num_iroots_of (n / 2ul) < 32ul);
       n % 2ul + num_iroots_of (n / 2ul))

val insert:
  mt:mt_ptr -> e:vhash ->
  HST.ST unit
	 (requires (fun h0 -> 
	   B.live h0 mt /\ 
	   B.live h0 (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 (MT?.iroots (B.get h0 mt 0)) /\
	   B.freeable (MT?.values (B.get h0 mt 0)) /\
	   B.live h0 e))
	 (ensures (fun h0 _ h1 -> true))
let insert mt e =
  let mtv = B.index mt 0ul in
  // if MT?.nelts mtv >= UInt32.uint_to_t (UInt.max_int U32.n) then ()
  let nelts = MT?.nelts mtv in
  assume (2 * U32.v nelts + 1 <= UInt.max_int U32.n);
  let nvalues = MT?.nvalues mtv in
  let inelts = nelts + 1ul in
  let invalues = if nelts = nvalues then 2ul * nelts + 1ul else nvalues in
  let invsz = hide (if nelts = nvalues then reveal (MT?.nvsz mtv) + 1 else reveal (MT?.nvsz mtv)) in
  let ivalues = insert_values nelts nvalues (MT?.nvsz mtv) (MT?.values mtv) e in
  let nirs = num_iroots_of nelts in
  let hh0 = HST.get () in 
  assume (B.live hh0 (MT?.iroots mtv) /\ hash_buf_allocated hh0 (MT?.iroots mtv));
  assume (B.live hh0 e);
  insert_iroots nelts nirs (MT?.iroots mtv) e;
  let hh1 = HST.get () in 
  assume (B.live hh1 mt);
  B.upd mt 0ul (MT inelts invalues invsz ivalues (MT?.iroots mtv))

/// Getting the Merkle root

val merkle_root_of_iroots:
  nirs:uint32_t{U32.v nirs <= U32.n} ->
  irs:hash_buf{B.length irs = U32.v nirs} -> 
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
  assume (B.length irs = U32.v (num_iroots_of nelts));
  merkle_root_of_iroots (num_iroots_of nelts) irs rt

