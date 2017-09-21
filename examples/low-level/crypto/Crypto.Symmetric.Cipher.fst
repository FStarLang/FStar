module Crypto.Symmetric.Cipher

// Multiplexing and hiding concrete implementations: AES128, AES256, and CHACHA20. 
// Consider also enforcing key abstraction (but quite verbose to code; see Plain.fst).

open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

open FStar.UInt32
open Crypto.Symmetric.Bytes
open Crypto.Indexing
open Crypto.Config

type alg = cipherAlg
let algi = cipherAlg_of_id

inline_for_extraction let keylen = function
  | AES128   -> 16ul
  | AES256   -> 32ul
  | CHACHA20 -> 32ul

inline_for_extraction let blocklen = function
  | AES128   -> 16ul
  | AES256   -> 16ul
  | CHACHA20 -> 64ul
inline_for_extraction
private let blocklen' = blocklen (* blocklen may be shadowed by Crypto.Symmetric.AES *)

inline_for_extraction let ivlen (a:alg) = 12ul 
inline_for_extraction private let ivlen' = ivlen (* may be shadowed by Crypto.Symmetric.Chacha20.ivlen *)

// Initialization function
// AES: S-box (256) + expanded key 4*nb*(nr+1)
// ChaCha20: only the key
inline_for_extraction let statelen = function
  | AES128   -> 432ul // 256 + 176
  | AES256   -> 496ul // 256 + 240
  | CHACHA20 -> 32ul

type ctr = UInt32.t

type key a   = lbuffer (v (keylen a))
type block a = lbuffer (v (blocklen a))
type state a = lbuffer (v (statelen a))

// 16-10-02 an integer value, instead of a lbuffer (v (ivlen)),
// so that it can be used both in abstract indexes and in real code.
inline_for_extraction type iv a    = n:UInt128.t { UInt128.v n < pow2 (v (8ul *^ ivlen a)) }

let init (#i:id) (k:key (algi i)) (s:state (algi i)) =
  let a = algi i in
  match a with
  | CHACHA20 ->
    Buffer.blit k 0ul s 0ul (keylen a)

  | AES128 ->
    let open Crypto.Symmetric.AES128 in
    let sbox = Buffer.sub s 0ul 256ul in
    let w = Buffer.sub s 256ul 176ul in
    (match aesImpl_of_id i with
    | HaclAES ->
      mk_sbox sbox;
      keyExpansion k w sbox
    | SpartanAES ->
      Spartan.keyExpansion k w sbox)

  | AES256 ->
    let open Crypto.Symmetric.AES in
    let sbox = Buffer.sub s 0ul 256ul in
    let w = Buffer.sub s 256ul 240ul in
    mk_sbox sbox;
    keyExpansion k w sbox    

// type ivv a   = lbytes (v (ivlen a))
// let load_iv a (i: iv a) : ivv a = Plain.load_bytes (ivlen a) i

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
  i:id ->
  output:buffer -> 
  st:state (algi i) {disjoint output st} ->
  n:iv (algi i) ->
  counter: ctr ->
  len:UInt32.t { len <=^  blocklen (algi i) /\ v len <= length output} -> Stack unit
    (requires (fun h -> live h st /\ live h output))
    (ensures (fun h0 _ h1 -> live h1 output /\ modifies_1 output h0 h1
      ))

#reset-options "--z3rlimit 50" 

let compute i output st n counter len = 
  let h0 = ST.get() in 
  push_frame(); 
  let a = algi i in
  begin match a with 
  | CHACHA20 -> // already specialized for counter mode
      let open Crypto.Symmetric.Chacha20 in // shadows ivlen
      let nbuf = Buffer.create 0uy (ivlen' CHACHA20) in
      let h1 = ST.get() in 
      store_uint128 (ivlen' CHACHA20) nbuf n;
      chacha20 output st nbuf counter len;
      let h2 = ST.get() in
      Buffer.lemma_reveal_modifies_2 output nbuf h1 h2;
      ()

  // ADL: TODO single parametric AES module
  | AES128 -> (
      let open Crypto.Symmetric.AES128 in // shadows blocklen
      let sbox = Buffer.sub st 0ul 256ul in
      let w = Buffer.sub st 256ul 176ul in
      let ctr_block = Buffer.create 0uy (blocklen' AES128) in
      store_uint128 (ivlen AES128) (Buffer.sub ctr_block 0ul (ivlen AES128)) n;
      aes_store_counter ctr_block counter;
      let output_block = Buffer.create 0uy (blocklen' AES128) in
      ( match aesImpl_of_id i with
          | HaclAES -> cipher output_block ctr_block w sbox
          | SpartanAES -> Spartan.cipher output_block ctr_block w sbox );
      blit output_block 0ul output 0ul len ) // too much copying!

  | AES256 -> 
      let open Crypto.Symmetric.AES in  // shadows blocklen
      let sbox = Buffer.sub st 0ul 256ul in
      let w = Buffer.sub st 256ul 240ul in
      let ctr_block = Buffer.create 0uy (blocklen' AES256) in 
      store_uint128 (ivlen AES256) (Buffer.sub ctr_block 0ul (ivlen AES256)) n;
      aes_store_counter ctr_block counter; 
      let output_block = Buffer.create 0uy (blocklen' AES256) in 
      cipher output_block ctr_block w sbox;
      blit output_block 0ul output 0ul len // too much copying!
  end;
  pop_frame()

//NB double-check this is indeed big-endian.

