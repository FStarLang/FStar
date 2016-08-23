module Crypto.AEAD.Chacha20Poly1305

open FStar.HST
open FStar.Buffer
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open Crypto.Symmetric.Chacha20
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305

//#set-options "--lax"

(* If the length is not a multipile of 16, pad to 16 *)
val pad_16: b:bytes -> len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16 /\ v len < 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let pad_16 b len =
  if len =^ 0ul then ()
  else memset (offset b len) 0uy (16ul -^ len)

(* Serializes the length into the appropriate format *)
val length_bytes: b:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let length_bytes b len aad_len =
  let l0 = Int.Cast.uint32_to_uint8 len in
  let l1 = Int.Cast.uint32_to_uint8 (len >>^ 8ul) in
  let l2 = Int.Cast.uint32_to_uint8 (len >>^ 16ul) in
  let l3 = Int.Cast.uint32_to_uint8 (len >>^ 24ul) in
  let al0 = Int.Cast.uint32_to_uint8 aad_len in
  let al1 = Int.Cast.uint32_to_uint8 (aad_len >>^ 8ul) in
  let al2 = Int.Cast.uint32_to_uint8 (aad_len >>^ 16ul) in
  let al3 = Int.Cast.uint32_to_uint8 (aad_len >>^ 24ul) in
  upd b 0ul al0;
  upd b 1ul al1;
  upd b 2ul al2;
  upd b 3ul al3;
  upd b 4ul 0uy;
  upd b 5ul 0uy;
  upd b 6ul 0uy;
  upd b 7ul 0uy;
  upd b 8ul l0;
  upd b 9ul l1;
  upd b 10ul l2;
  upd b 11ul l3;
  upd b 12ul 0uy;
  upd b 13ul 0uy;
  upd b 14ul 0uy;
  upd b 15ul 0uy;
  ()

(* AEAD-encrypt for Chacha20-Poly1305. Takes:
   - the additional data (aad)
   - the initial key (key)
   - an initialization vector (iv) and a constant (constant)
   - the plaintext
   - the length of the plaintext (len) and the length of the additional data (len_aad)
   The result is stored in
   - ciphertext for the Chacha20 ciphertext, using the key (key), the iv and the nonce   
   - the Poly1305 tag on the ciphertext and the additional data
   *)
   
val chacha20_aead_encrypt: ciphertext:bytes -> tag:bytes -> aad:bytes -> key:bytes -> iv:UInt64.t -> constant:UInt32.t -> plaintext:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> 
    live h ciphertext /\ live h tag /\ live h aad /\ live h key /\ live h plaintext
    /\ length ciphertext >= v len
    /\ length tag >= 16
    /\ length aad >= v aad_len
    /\ length key >= 32
    /\ length plaintext >= v len
  ))
  (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ modifies_2 ciphertext tag h0 h1 ))
let chacha20_aead_encrypt ciphertext tag aad key iv constant plaintext len aad_len =
  push_frame();

  (* Temporary buffers (to be improved) *)
  let otk   = create 0uy 32ul in (* OTK for Poly (to improve) *)
  let state = create 0ul 32ul in (* Chacha inner state *)
  let acc   = create 0UL 5ul  in (* Poly's accumulator *)
  let r     = create 0UL 5ul  in (* First half of poly's key, will be removed (merged with otk) *)
(*  let s     = create 0UL 5ul  in (\* Second half of poly's key, will be removed (merged with otk) *\) *)

  (*  Create OTK, using round '0' of Chacha20 *)
  let counter = 0ul in
  chacha20_init state key counter iv constant;
  chacha20_update otk state 32ul;

  (*  Encryption of the plaintext, using Chacha20, counter at 1 *)
  let counter = 1ul in
  chacha20_encrypt ciphertext key counter iv constant plaintext len;

  (*  MACing of the additional data, the ciphertext and the padding *)
  (* Compute the padding lengths *)
  let max = UInt32.div len 16ul in
  let rem = UInt32.rem len 16ul in
  let max_aad = UInt32.div aad_len 16ul in
  let rem_aad = UInt32.rem aad_len 16ul in
  (* Create padded blocks *)
  let padded_aad = create 0uy 16ul in
  let padded_ciphertext = create 0uy 16ul in
  let len_bytes = create 0uy 16ul in
  blit ciphertext (UInt32.mul max 16ul) padded_ciphertext 0ul rem;
  blit aad (UInt32.mul max_aad 16ul) padded_aad 0ul rem_aad;
  pad_16 padded_ciphertext rem;
  pad_16 padded_aad rem_aad;
  (* Initlialize MAC algorithm with one time key *)
  let log = poly1305_init acc r otk in
  (* Update MAC with
     - padded additional data
     - padded ciphertext
     - formatted length *)
  let aad_log = 
    let log = poly1305_loop log aad acc r max_aad in
    (* This is not length-constant time, the lengths are assumed to 
       be public data *)  
    if not(UInt32.eq rem_aad 0ul) then poly1305_update log padded_aad acc r
    else log in
  let aad_ciphertext_log = 
    let log = poly1305_loop aad_log ciphertext acc r max in
    if not(UInt32.eq rem 0ul) then poly1305_update log padded_ciphertext acc r
    else log in
  length_bytes len_bytes len aad_len;
  let full_log = poly1305_update aad_ciphertext_log len_bytes acc r in
  (* Finish MAC *)
  poly1305_finish tag acc (Buffer.sub otk 16ul 16ul);
  pop_frame()
