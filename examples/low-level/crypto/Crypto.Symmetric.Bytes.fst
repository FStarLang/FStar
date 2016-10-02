module Crypto.Symmetric.Bytes

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils

 
type mem = FStar.HyperStack.mem

type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbytes (l:nat)  = b:bytes  {Seq.length b = l}
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}

val sel_bytes: h:mem -> l:UInt32.t -> buf:lbuffer(v l){Buffer.live h buf}
  -> GTot (lbytes (v l))
let sel_bytes h l buf = Buffer.as_seq h buf

val load_bytes: l:UInt32.t -> buf:lbuffer(v l) -> Stack (lbytes(v l))
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h0 buf /\ r == sel_bytes h1 l buf))
let rec load_bytes l buf = 
  assume false;//16-10-02 16-09-21 TODO 
  if l = 0ul then Seq.createEmpty else
  let b = Buffer.index buf 0ul in
  let t = load_bytes (l -^ 1ul) (Buffer.sub buf 1ul (l -^ 1ul)) in
  SeqProperties.cons b t


val store_bytes: l:UInt32.t -> buf:lbuffer(v l) -> b:lbytes(v l) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\ b == sel_bytes h1 l buf
  ))

val store_bytes_aux: len:UInt32.t -> buf:lbuffer(v len) -> i:UInt32.t  {i <=^ len} -> b:lbytes(v len) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\ b == sel_bytes h1 len buf
  ))
let rec store_bytes_aux len buf i b = 
  assume false;//16-09-21 TODO 
  if i <^ len then (
  Buffer.upd buf i (Seq.index b (v i));
  store_bytes_aux len buf (i +^ 1ul) b)
let store_bytes l buf b = store_bytes_aux l buf 0ul b


(* We need functions to load/store integers in byte buffers. Possibly elsewhere. *)

open FStar.Buffer
open FStar.Mul // 16-10-02 avoid?
open FStar.Int.Cast
// 16-10-02 pls go to Seq.fst
let head (#a:Type) (b:Seq.seq a {Seq.length b >= 1}) = Seq.index b 0
let tail (#a:Type) (b:Seq.seq a {Seq.length b >= 1}) = Seq.slice b 1 (Seq.length b)

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:bytes) : Tot (n:nat) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else ( 
      UInt8.v (head b) + pow2 8 * little_endian (tail b))

(*
val lemma_little_endian: b:bytes {Seq.length b > 0} -> Lemma 
  (little_endian b = UInt8.v (head b) + pow2 8 * little_endian (tail b))

let lemma_little_endian b = 
  if Seq.length b = 0 then () 
  else assume false
//16-10-02 ?
*)

val lemma_euclidean_division: a:nat -> b:nat -> Lemma
  (requires (a < pow2 8))
  (ensures  (a + pow2 8 * b < pow2 8 * (b + 1)))
let lemma_euclidean_division a b = ()

val lemma_factorise: a:nat -> b:nat -> Lemma (a + a * b = a * (b + 1))
let lemma_factorise a b = ()

#reset-options "--initial_fuel 1 --max_fuel 1"

val lemma_little_endian_is_bounded: b:bytes -> Lemma
  (requires True)
  (ensures  (little_endian b < pow2 (8 * Seq.length b)))
  (decreases (Seq.length b))
let rec lemma_little_endian_is_bounded b =
  if Seq.length b = 0 then ()
  else
    begin
    let s = Seq.slice b 1 (Seq.length b) in
    assert(Seq.length s = Seq.length b - 1);
    lemma_little_endian_is_bounded s;
    assert(UInt8.v (Seq.index b 0) < pow2 8);
    assert(little_endian s < pow2 (8 * Seq.length s));
    assert(little_endian b < pow2 8 + pow2 8 * pow2 (8 * (Seq.length b - 1)));
    lemma_euclidean_division (UInt8.v (Seq.index b 0)) (little_endian s);
    assert(little_endian b <= pow2 8 * (little_endian s + 1));
    assert(little_endian b <= pow2 8 * pow2 (8 * (Seq.length b - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (Seq.length b - 1));
    lemma_factorise 8 (Seq.length b - 1)
    end
 
#reset-options "--initial_fuel 0 --max_fuel 0"

val lemma_little_endian_lt_2_128: b:bytes {Seq.length b <= 16} -> Lemma
  (requires (True))
  (ensures  (little_endian b < pow2 128))
  [SMTPat (little_endian b)]
let lemma_little_endian_lt_2_128 b =
  lemma_little_endian_is_bounded b;
  if Seq.length b = 16 then ()
  else Math.Lemmas.pow2_lt_compat 128 (8 * Seq.length b)

 
(* loads a machine integer from a buffer of len bytes *)

#reset-options "--z3timeout 100" 

val load_uint32: len:UInt32.t { v len <= 4 } -> buf:lbuffer (v len) -> ST UInt32.t
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 n h1 -> 
    h0 == h1 /\ live h0 buf /\ 
    UInt32.v n == little_endian (sel_bytes h1 len buf)))

let rec load_uint32 len buf = 
  if len = 0ul then 0ul
  else
    let len = len -^ 1ul in
    let n = load_uint32 len (sub buf 1ul len) in
    let b = buf.(0ul) in 
    FStar.UInt32(uint8_to_uint32 b +^ 256ul *^ n)

val load_uint128: len:UInt32.t { v len <= 16 } -> buf:lbuffer (v len) -> ST UInt128.t
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 n h1 -> 
    h0 == h1 /\ live h0 buf /\ 
    UInt128.v n == little_endian (sel_bytes h1 len buf)))
 
#reset-options "--z3timeout 1000" 

// 16-10-02 128-bit constants??
let rec load_uint128 len buf = 
  if len = 0ul then uint64_to_uint128 0UL
  else
    let len = len -^ 1ul in
    let n = load_uint128 len (sub buf 1ul len) in
    let b = buf.(0ul) in 
    assume false;
    FStar.UInt128(uint64_to_uint128 (uint8_to_uint64 b) +^ uint64_to_uint128 256UL *^ n) 
//16-10-02 TODO not why this fails; maybe fewer lemmas on UInt128 ? 

(* stores a machine integer into a buffer of len bytes *)
// 16-10-02 subsumes Buffer.Utils.bytes_of_uint32 ?

val store_uint32: 
  len:UInt32.t {v len <= 4} -> buf:lbuffer (v len) -> 
  n:UInt32.t {UInt32.v n < pow2 (8 * v len)} -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> 
    Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\
    UInt32.v n == little_endian (sel_bytes h1 len buf)))

let rec store_uint32 len buf n = 
  if len <> 0ul then
    let len = len -^ 1ul in 
    let b = uint32_to_uint8 n in
    let n' = FStar.UInt32(n >>^ 8ul) in 
    assert(v n = UInt8.v b + 256 * v n');
    let buf' = Buffer.sub buf 1ul len in
    Math.Lemmas.pow2_plus 8 (8 * v len);
    store_uint32 len buf' n';
    buf.(0ul) <- b // updating after the recursive call helps verification
// verification is slow, not sure why; maybe pow2 8?
// check efficient compilation for all back-ends
 
val store_uint128: 
  len:UInt32.t {v len <= 16} -> buf:lbuffer (v len) -> 
  n:UInt128.t {UInt128.v n < pow2 (8 * v len)} -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> 
    Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\
    UInt128.v n = little_endian (sel_bytes h1 len buf)))
 
let rec store_uint128 len buf n = 
  if len <> 0ul then
    let len = len -^ 1ul in 
    let b = uint64_to_uint8 (uint128_to_uint64 n) in
    let n' = FStar.UInt128(n >>^ 8ul) in 
    assert(UInt128.v n = UInt8.v b + 256 * UInt128.v n');
    let buf' = Buffer.sub buf 1ul len in
    Math.Lemmas.pow2_plus 8 (8 * v len);
    store_uint128 len buf' n';
    buf.(0ul) <- b // updating after the recursive call helps verification
// verification is slow, not sure why; maybe pow2 8?
// check efficient compilation for all back-ends

 
