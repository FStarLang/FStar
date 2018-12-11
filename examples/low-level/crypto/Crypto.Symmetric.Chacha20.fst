(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Crypto.Symmetric.Chacha20

// Concrete implementation of CHACHA20 and countermode encryption
// Not much point verifying its against a more complex pure specification.

open FStar.Mul
open FStar.Ghost
(*  Machine integers *)
open FStar.UInt8
open FStar.UInt32
open FStar.Int.Cast
(*  Effects and memory layout *)
open FStar.HyperStack
open FStar.HyperStack.ST
(*  Buffers *)
open FStar.Buffer
open Buffer.Utils

module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

type u64 = FStar.UInt64.t

// JP: see comment in Buffer.Utils.fst
#set-options "--lax"

(*** Chacha 20 ***)

inline_for_extraction let keylen   = 32ul
inline_for_extraction let blocklen = 64ul 
inline_for_extraction let ivlen    = 12ul

type lbytes l = b:bytes {length b = l}
type key   = lbytes (v keylen)
type block = lbytes (v blocklen)
type iv    = lbytes (v ivlen)

// internally, blocks are represented as 16 x 4-byte integers
private type matrix = m:uint32s{length m = v blocklen / 4}

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
  m.(a) <- m.(a) +%^ m.(b);
  m.(d) <-(m.(d) ^^  m.(a)) <<< s

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
  m:matrix -> k:key{disjoint m k} -> n:iv{disjoint m n} -> counter:u32 -> 
  STL unit
  (requires (fun h -> live h m /\ live h k /\ live h n ))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))

private val fill: m:matrix -> i:u32 -> len:u32 {v i + v len <= 16}-> src:bytes {length src = 4 * v len} -> 
  STL unit
  (requires (fun h -> live h m /\ live h src /\ disjoint m src))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let rec fill m i len src =
  if len <> 0ul then (
    m.(i) <- uint32_of_bytes (sub src 0ul 4ul); 
    let len = len -^ 1ul in 
    fill m (i +^ 1ul) len (sub src 4ul (4ul *^ len)))

//review handling of endianness

// RFC 7539 2.3
let chacha20_init m key iv counter =
  m.(0ul) <- 0x61707865ul;
  m.(1ul) <- 0x3320646eul;
  m.(2ul) <- 0x79622d32ul;
  m.(3ul) <- 0x6b206574ul;
  fill m 4ul 8ul key;
  m.(12ul) <- counter; 
  fill m 13ul 3ul iv

(* lifted by hand for now: *)
private val add: 
  m: matrix -> m0: matrix{disjoint m m0} -> 
  i:u32 { i <^ 16ul } ->
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let add m m0 i = 
  m.(i) <- m.(i) +%^ m0.(i)

private val sum_matrixes: 
  m: matrix -> m0:matrix{disjoint m m0} -> 
  STL unit
  (requires (fun h -> live h m /\ live h m0))
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let sum_matrixes m m0 =
//let add i = upd m i (m.(i) +%^ m0.(i)) in // inlined? 
// forUint32 0ul 15ul (fun i -> add m m0 i)
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
// (consider fixing len to 64ul)

val chacha20: 
  output:bytes -> 
  k:key ->
  n:iv ->
  counter: u32 ->
  len:u32{v len <= v blocklen /\ v len <= length output} -> STL unit
    (requires (fun h -> live h k /\ live h n /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 ))
let chacha20 output key n counter len = 
  push_frame ();
  let state = create 0ul 32ul in
  let m = sub state 0ul 16ul in
  chacha20_init m key n counter;
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

private let prf = chacha20

// XOR-based encryption and decryption (just swap ciphertext and plaintext)
val counter_mode: 
  k:key -> n:iv -> counter:u32 -> 
  len:u32{v counter + v len / v blocklen < pow2 32} ->
  plaintext:bytes {length plaintext = v len /\ disjoint k plaintext} -> 
  ciphertext:bytes {length ciphertext = v len /\ disjoint n ciphertext /\ disjoint k ciphertext /\ disjoint plaintext ciphertext} -> 
  STL unit
    (requires (fun h -> live h ciphertext /\ live h k /\ live h n /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))

#reset-options "--z3rlimit 100"
// a bit slow, e.g. on the len precondition

let rec counter_mode key iv counter len plaintext ciphertext =
  if len =^ 0ul then () 
  else if len <^ blocklen 
  then (* encrypt final partial block *)
    begin
      let cipher = sub ciphertext  0ul len in 
      let plain  = sub plaintext   0ul len in 
      prf cipher key iv counter len;
      xor_bytes_inplace cipher plain len
    end
  else (* encrypt full block *)
    begin
      let cipher = sub ciphertext  0ul blocklen in
      let plain  = sub plaintext   0ul blocklen in
      prf cipher key iv counter blocklen;
      xor_bytes_inplace cipher plain blocklen;
      let len = len -^ blocklen in
      let ciphertext = sub ciphertext blocklen len in
      let plaintext  = sub plaintext  blocklen len in
      counter_mode key iv (counter +^ 1ul) len plaintext ciphertext
    end

