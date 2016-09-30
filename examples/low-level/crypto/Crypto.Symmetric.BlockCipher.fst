module Crypto.Symmetric.BlockCipher

// Multiplexing and hiding concrete implementations: AES128, AES256, and CHACHA20. 
// Consider also enforcing key abstraction (but quite verbose to code; see Plain.fst).

open FStar.HyperStack
open FStar.HST
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.UInt32

// library stuff

type buffer = Buffer.buffer UInt8.t
type bytes  = Seq.seq UInt8.t 
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}
type lbytes  (l:nat) = b:bytes {Seq.length b = l}


type alg = 
//| AES128 
  | AES256 
  | CHACHA20 // RFC 7539 for the AEAD algorithm; RFC 7905 for the TLS ciphersuites

let keylen = function
//| AES128   -> 16ul
  | AES256   -> 32ul
  | CHACHA20 -> 32ul

let blocklen = function
//| AES128   -> 16ul
  | AES256   -> 16ul
  | CHACHA20 -> 64ul

let ivlen (a:alg) = 12ul 

type ctr = UInt32.t

type key a   = lbuffer (v (keylen a))
type block a = lbuffer (v (blocklen a))
type iv a    = lbuffer (v (ivlen a))

// IVs are now mutable byte arrays (UInt128s may be better)
// ideally, we need to get to their value as abstract indexes.

type ivv a   = lbytes (v (ivlen a))
let load_iv a (i: iv a) : ivv a = Plain.load_bytes (ivlen a) i

(* Update the counter, replace last 4 bytes of counter with num. *)
(* num is precalculated by the function who calls this function. *)
private val aes_store_counter: counter:lbuffer (v (blocklen AES256)) -> num:ctr -> Stack unit
    (requires (fun h -> live h counter))
    (ensures (fun h0 _ h1 -> live h1 counter /\ modifies_1 counter h0 h1))
let aes_store_counter b x =
  let b0 = FStar.Int.Cast.uint32_to_uint8 (x &^ 255ul) in
  let b1 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 8ul) &^ 255ul) in
  let b2 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 16ul) &^ 255ul) in
  let b3 = FStar.Int.Cast.uint32_to_uint8 ((x >>^ 24ul) &^ 255ul) in
  b.(15ul) <- b0;
  b.(14ul) <- b1;
  b.(13ul) <- b2;
  b.(12ul) <- b3


val compute:
  a: alg ->
  output:buffer -> 
  k:key a {disjoint output k} ->
  n:iv a {disjoint output n} ->
  counter: ctr ->
  len:UInt32.t { len <=^  blocklen a /\ v len <= length output} -> STL unit
    (requires (fun h -> live h k /\ live h n /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1 ))

#reset-options "--z3timeout 100" 

let compute a output k n counter len = 
  push_frame();
  begin match a with 
  | CHACHA20 -> // already specialized for counter mode
      let open Crypto.Symmetric.Chacha20 in 
      chacha20 output k n counter len

  | AES256 -> 
      let open Crypto.Symmetric.AES in 

      // all of this should be hoisted. 
      let sbox = create 0uy 256ul in 
      let w: xkey = Buffer.create 0uy (4ul *^ nb *^ (nr+^1ul)) in
      mk_sbox sbox; 
      keyExpansion k w sbox; 
      let ctr_block = Buffer.create 0uy (blocklen AES256) in 
      blit n 0ul ctr_block 0ul 12ul;

      let output_block = Buffer.create 0uy (blocklen AES256) in 
      aes_store_counter ctr_block counter; 
      cipher output_block ctr_block w sbox;
      blit output_block 0ul output 0ul len // too much copying!
  end;
  pop_frame()
  
