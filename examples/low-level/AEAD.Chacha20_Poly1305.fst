module AEAD.Chacha20_Poly1305

open FStar.HST
open FStar.Buffer
open FStar.UInt32
open Chacha_wip
open Poly.Bigint
open Poly.Poly1305_wip

val fill: b:bytes -> z:UInt8.t -> len:UInt32.t -> Stl unit
let rec fill b z len = 
  if UInt32.eq len 0ul then ()
  else (
    let i = len -^ 1ul in    
    upd b i z;
    fill b z i
  )

val pad_16: b:bytes -> len:UInt32.t -> Stl unit
let pad_16 b len =
  fill b 0uy (16ul -^ len)

val length_bytes: b:bytes -> len:UInt32.t -> aad_len:UInt32.t -> Stl unit
let length_bytes b len aad_len =
  let l0 = Int.Cast.uint32_to_uint8 len in
  let l1 = Int.Cast.uint32_to_uint8 (len ^>> 8ul) in
  let l2 = Int.Cast.uint32_to_uint8 (len ^>> 16ul) in
  let l3 = Int.Cast.uint32_to_uint8 (len ^>> 24ul) in
  let al0 = Int.Cast.uint32_to_uint8 aad_len in
  let al1 = Int.Cast.uint32_to_uint8 (aad_len ^>> 8ul) in
  let al2 = Int.Cast.uint32_to_uint8 (aad_len ^>> 16ul) in
  let al3 = Int.Cast.uint32_to_uint8 (aad_len ^>> 24ul) in
  upd b 0ul al0;
  upd b 1ul al1;
  upd b 2ul al2;
  upd b 3ul al3;
  upd b 4ul l0;
  upd b 5ul l1;
  upd b 6ul l2;
  upd b 7ul l3;
  ()

val chacha20_aead_encrypt: ciphertext:bytes -> tag:bytes -> aad:bytes -> key:bytes -> iv:UInt64.t -> constant:UInt32.t -> plaintext:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> live h ciphertext /\ live h tag /\ live h aad /\ live h key /\ live h plaintext))
  (ensures (fun h0 _ h1 -> True))
let chacha20_aead_encrypt ciphertext tag aad key iv constant plaintext len aad_len =
  push_frame();

  (* Temporary buffers (to be improved) *)
  let otk = create 0uy 64ul in   (* OTK for Chacha (to improve) *)
  let state = create 0ul 32ul in (* Chacha inner state *)
  let acc = create 0UL 5ul in (* Poly's accumulator *)
  let r = create 0UL 5ul in (* First half of poly's key, will be removed (merged with otk) *)
  let s = create 0UL 5ul in (* Second half of poly's key, will be removed (merged with otk) *)

  (* Create OTK *)
  let counter = 0ul in
  chacha20_init state key counter iv constant;
  bytes_of_uint32s otk state 64ul; // Unnecessary copy, will be removed with different encoding

  (* Encrypt plaintext *)
  let counter = counter +^ 1ul in
  chacha20_encrypt ciphertext key counter iv constant plaintext len;

  (* MAC *)
  let max = UInt32.div len 16ul in
  let rem = UInt32.rem len 16ul in
  let max_aad = UInt32.div aad_len 16ul in
  let rem_aad = UInt32.rem aad_len 16ul in
  (* Padded blocks *)
  let padded_aad = create 0uy 16ul in
  let padded_ciphertext = create 0uy 16ul in
  let len_bytes = create 0uy 8ul in
  blit ciphertext (UInt32.mul max 16ul) padded_ciphertext 0ul rem;
  blit aad (UInt32.mul max_aad 16ul) padded_aad 0ul rem_aad;
  pad_16 padded_ciphertext rem;
  pad_16 padded_aad rem_aad;
  (* Initlialize MAC algorithm *)
  poly1305_init acc r s otk;
  (* Update MAC *)
  poly1305_step aad acc r max_aad;
  if not(UInt32.eq rem_aad 0ul) then poly1305_step padded_aad acc r 1ul;
  poly1305_step ciphertext acc r max;
  if not(UInt32.eq rem 0ul) then poly1305_step padded_ciphertext acc r 1ul;
  length_bytes len_bytes len aad_len;
  poly1305_last len_bytes acc r 8ul;
  (* Finish MAC *)
  poly1305_finish tag acc s;
  ()
