module Crypto.Symmetric.Chacha20

open FStar.Mul
open FStar.Ghost
(*  Machine integers *)
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
(*  Effects and memory layout *)
open FStar.HyperStack
open FStar.HST
(*  Buffers *)
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

// move elsewhere!
// manually inlined for now (for kremlin)
//type lbytes (n:nat) = b:bytes{length b = n}

type u64 = FStar.UInt64.t


(*** Chacha 20 ***)

type key = b:bytes{length b = 32}

// why not treating IV and Constant as bytes too? 

private type matrix = m:uint32s{length m = 16}
private type shuffle = 
  m:matrix -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))

(* lifted by hand for now: *)
private val line:
  m:matrix -> 
  a:u32{v a < 16} -> 
  b:u32{v b < 16} -> 
  d:u32{v d < 16} -> 
  s:u32{v s <= 32}-> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let line m a b d s = 
  upd m a (m.(a) +%^ m.(b));
  upd m d((m.(d) ^^  m.(a)) <<< s)

private val quarter_round:
  m:matrix -> 
  a:u32{v a < 16} -> 
  b:u32{v b < 16} -> 
  c:u32{v c < 16} -> 
  d:u32{v d < 16} -> STL unit
  (requires (fun h -> live h m))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let quarter_round m a b c d = 
(*
  let line a b d s = 
    upd m a (m.(a) +%^ m.(b));
    upd m d((m.(d) ^^  m.(a)) <<< s) in
*)    
  line m a b d 16ul;
  line m c d b 12ul;
  line m a b d  8ul; 
  line m c d b  7ul

private val column_round: shuffle 
let column_round m =
  quarter_round m 0ul 4ul  8ul 12ul;
  quarter_round m 1ul 5ul  9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

private val diagonal_round: shuffle
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul  8ul 13ul;
  quarter_round m 3ul 4ul  9ul 14ul

private val rounds: shuffle 
let rounds m = (* 20 rounds *)
  column_round m; diagonal_round m; 
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m

private val chacha20_init: 
  m:matrix -> k:key{disjoint m k} -> iv:u64 -> counter:u32 -> constant:u32 -> 
  STL unit
  (requires (fun h -> live h m /\ live h k))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))

private val updkey:
  m:matrix -> i:u32 { 4 <= v i /\ v i < 12 } -> k:key{disjoint m k} -> 
  STL unit
  (requires (fun h -> live h m /\ live h k))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let updkey m i k =
  upd m i (uint32_of_bytes (sub k ((i -^ 4ul) *^ 4ul) 4ul))
  //upd m (i +^ 4ul) (uint32_of_bytes (sub k (i *^ 4ul) 4ul))

let chacha20_init m key iv counter constant =
  upd m     0ul 0x61707865ul;
  upd m     1ul 0x3320646eul;
  upd m     2ul 0x79622d32ul;
  upd m     3ul 0x6b206574ul;
  updkey m  4ul key;
  updkey m  5ul key;
  updkey m  6ul key;
  updkey m  7ul key;
  updkey m  8ul key;
  updkey m  9ul key;
  updkey m 10ul key;
  updkey m 11ul key;
  upd m    12ul counter; 
  upd m    13ul constant;
  upd m    14ul (Int.Cast.uint64_to_uint32 iv);
  upd m    15ul (Int.Cast.uint64_to_uint32 (UInt64.shift_right iv 32ul))

(* lifted by hand for now: *)
private val add: 
  m: matrix -> m0: matrix{disjoint m m0} -> 
  i:u32 { i <^ 16ul } ->
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let add m m0 i = upd m i (m.(i) +%^ m0.(i)) 

private val sum_matrixes: 
  m: matrix -> m0:matrix{disjoint m m0} -> 
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let sum_matrixes m m0 =
//let add i = upd m i (m.(i) +%^ m0.(i)) in // inlined? 
  add m m0  0ul;
  add m m0  1ul;
  add m m0  2ul;
  add m m0  3ul;
  add m m0  4ul;
  add m m0  5ul;
  add m m0  6ul;
  add m m0  7ul;
  add m m0  8ul;
  add m m0  9ul;
  add m m0 10ul;
  add m m0 11ul;
  add m m0 12ul;
  add m m0 13ul;
  add m m0 14ul;
  add m m0 15ul

private val chacha20_update: 
  output:bytes -> 
  state:uint32s{length state = 32 /\ disjoint state output} ->
  len:u32{v len <= 64 /\ length output >= v len} -> STL unit
    (requires (fun h -> live h state /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_update output state len =
  (* Initial state *) 
  let m  = sub state  0ul 16ul in
  let m0 = sub state 16ul 16ul in // do we ever rely on m and m0 being contiguous?
  blit m 0ul m0 0ul 16ul;
  rounds m;
  (* Sum the matrixes *)
  sum_matrixes m m0;
  (* Serialize the state into byte stream *)
  bytes_of_uint32s output m len
// avoid this copy when XORing? merge the sum_matrix and output loops? we don't use m0 afterward. 

// computes one pseudo-random 64-byte block 
// (consider fixing len = 64ul)
let chacha20 output key iv counter constant len = 
  push_frame ();
  let state = create 0ul 32ul in
  chacha20_init (sub state 0ul 16ul) key iv counter constant;
  chacha20_update output state len;
  pop_frame ()

// Performance: it may be easier to precompute and re-use an expanded key (m0), 
// to avoid passing around (key, counter, iv, constant), and only have m on the stack.
// We may also merge the 3 final loops: sum_matrixes, bytes_of_uint32s, and outer XOR/ADD. 


(*** Counter-mode Encryption ***)

// The rest of this code is not specific to chacha20.
// It is parameterized by the initial counter (0, or 1 for some AEAD)
// and the block length (here 64 bytes).
// It should appear after PRF idealization.

let blocklen = 64ul
private let prf = chacha20

// XOR-based encryption and decryption (just swap ciphertext and plaintext)
val counter_mode: 
  k:key -> iv:u64 -> counter:u32 -> constant:u32 ->
  len:u32{v counter + v len / v blocklen < pow2 32} ->
  plaintext:bytes {length plaintext = v len /\ disjoint k plaintext} -> 
  ciphertext:bytes {length ciphertext = v len /\ disjoint k ciphertext /\ disjoint plaintext ciphertext} -> 
  STL unit
    (requires (fun h -> live h ciphertext /\ live h k /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))

#reset-options "--z3timeout 100"
// a bit slow, e.g. on the len precondition

let rec counter_mode key iv counter constant len plaintext ciphertext =
  if len =^ 0ul then () 
  else if len <^ blocklen 
  then (* encrypt final partial block *)
    begin
      let cipher = sub ciphertext  0ul len in 
      let plain  =  sub plaintext   0ul len in 
      prf cipher key iv counter constant len;
      xor_bytes_inplace cipher plain len
    end
  else (* encrypt full block *)
    begin
      let cipher = sub ciphertext  0ul blocklen in
      let plain  = sub plaintext   0ul blocklen in
      prf cipher key iv counter constant blocklen;
      xor_bytes_inplace cipher plain blocklen;
      let len = len -^ blocklen in
      let ciphertext = sub ciphertext blocklen len in
      let plaintext  = sub plaintext  blocklen len in
      counter_mode key iv (counter +^ 1ul) constant len plaintext ciphertext
    end

