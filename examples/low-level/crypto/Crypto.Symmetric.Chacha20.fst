module Crypto.Symmetric.Chacha20


open FStar.HyperStack
open FStar.ST
open FStar.Buffer
open FStar.Int.Cast
open FStar.UInt32


let u32 = FStar.UInt32.t
let uint8_p = buffer FStar.UInt8.t

type chacha_ctx = b:Buffer.buffer u32{length b = 16}

val lemma_max_uint32: n:nat -> 
  Lemma (requires (n = 32))
        (ensures (pow2 n = 4294967296))
        [SMTPat (pow2 n)]
let lemma_max_uint32 n = assert_norm (pow2 32 = 4294967296)

let op_Less_Less_Less (a:u32) (s:u32{FStar.UInt32.v s <= 32}) : Tot u32 =
  (a <<^ s) |^ (a >>^ (FStar.UInt32 (32ul -^ s)))


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 5"

let load32_le (k:uint8_p) : Stack u32
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> h0 == h1))
  = let k0 = k.(0ul) in
    let k1 = k.(1ul) in
    let k2 = k.(2ul) in
    let k3 = k.(3ul) in
    let z = uint8_to_uint32 k0
            |^ (uint8_to_uint32 k1 <<^ 8ul)
            |^ (uint8_to_uint32 k2 <<^ 16ul)
            |^ (uint8_to_uint32 k3 <<^ 24ul) in
    z

let store32_le (k:uint8_p) (x:u32) : Stack unit
  (requires (fun h -> live h k /\ length k >= 4))
  (ensures  (fun h0 _ h1 -> modifies_1 k h0 h1 /\ live h1 k))
  = k.(0ul) <- uint32_to_uint8 x;
    k.(1ul) <- uint32_to_uint8 (x >>^ 8ul);
    k.(2ul) <- uint32_to_uint8 (x >>^ 16ul);
    k.(3ul) <- uint32_to_uint8 (x >>^ 24ul)


val chacha_keysetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 32 /\ disjoint ctx k} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 ctx /\ modifies_1 ctx h0 h1))
let chacha_keysetup ctx k =
    ctx.(0ul)  <- (0x61707865ul);
    ctx.(1ul)  <- (0x3320646eul);
    ctx.(2ul)  <- (0x79622d32ul);
    ctx.(3ul)  <- (0x6b206574ul);
    ctx.(4ul)  <- load32_le(offset k  0ul);
    ctx.(5ul)  <- load32_le(offset k  4ul);
    ctx.(6ul)  <- load32_le(offset k  8ul);
    ctx.(7ul)  <- load32_le(offset k 12ul);
    ctx.(8ul)  <- load32_le(offset k 16ul);
    ctx.(9ul)  <- load32_le(offset k 20ul);
    ctx.(10ul) <- load32_le(offset k 24ul);
    ctx.(11ul) <- load32_le(offset k 28ul)


val chacha_ietf_ivsetup:
  ctx:chacha_ctx ->
  k:uint8_p{length k = 32 /\ disjoint ctx k} ->
  counter:u32 ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h k))
    (ensures  (fun h0 _ h1 -> live h1 ctx /\ modifies_1 ctx h0 h1))
let chacha_ietf_ivsetup ctx iv counter =
    ctx.(12ul) <- counter;
    ctx.(13ul) <- load32_le(iv);
    ctx.(14ul) <- load32_le(offset iv 4ul);
    ctx.(15ul) <- load32_le(offset iv 8ul)


#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 100"

val chacha_encrypt_bytes_core:
  ctx:chacha_ctx ->
  m:uint8_p{length m >= 64} ->
  c:uint8_p{length c >= 64 /\ disjoint ctx c} ->
  Stack unit
    (requires (fun h -> live h ctx /\ live h c /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 c h0 h1 /\ live h1 c))
let chacha_encrypt_bytes_core ctx m c =
  let j0 = ctx.(0ul) in
  let j1 = ctx.(1ul) in
  let j2 = ctx.(2ul) in
  let j3 = ctx.(3ul) in
  let j4 = ctx.(4ul) in
  let j5 = ctx.(5ul) in
  let j6 = ctx.(6ul) in
  let j7 = ctx.(7ul) in
  let j8 = ctx.(8ul) in
  let j9 = ctx.(9ul) in
  let j10 = ctx.(10ul) in
  let j11 = ctx.(11ul) in
  let j12 = ctx.(12ul) in
  let j13 = ctx.(13ul) in
  let j14 = ctx.(14ul) in
  let j15 = ctx.(15ul) in
  let x0 = j0 in
  let x1 = j1 in
  let x2 = j2 in
  let x3 = j3 in
  let x4 = j4 in
  let x5 = j5 in
  let x6 = j6 in
  let x7 = j7 in
  let x8 = j8 in
  let x9 = j9 in
  let x10 = j10 in
  let x11 = j11 in
  let x12 = j12 in
  let x13 = j13 in
  let x14 = j14 in
  let x15 = j15 in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 1 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 2 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 3 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 4 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 5 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 6 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 7 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 8 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 9 *)
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 16ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 12ul in
  let x0 = x0 +%^ x4 in
  let x12 = x12 ^^ x0 in
  let x12 = x12 <<< 8ul in
  let x8 = x8 +%^ x12 in
  let x4 = x4 ^^ x8 in
  let x4 = x4 <<< 7ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 16ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 12ul in
  let x1 = x1 +%^ x5 in
  let x13 = x13 ^^ x1 in
  let x13 = x13 <<< 8ul in
  let x9 = x9 +%^ x13 in
  let x5 = x5 ^^ x9 in
  let x5 = x5 <<< 7ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 16ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 12ul in
  let x2 = x2 +%^ x6 in
  let x14 = x14 ^^ x2 in
  let x14 = x14 <<< 8ul in
  let x10 = x10 +%^ x14 in
  let x6 = x6 ^^ x10 in
  let x6 = x6 <<< 7ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 16ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 12ul in
  let x3 = x3 +%^ x7 in
  let x15 = x15 ^^ x3 in
  let x15 = x15 <<< 8ul in
  let x11 = x11 +%^ x15 in
  let x7 = x7 ^^ x11 in
  let x7 = x7 <<< 7ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 16ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 12ul in
  let x0 = x0 +%^ x5 in
  let x15 = x15 ^^ x0 in
  let x15 = x15 <<< 8ul in
  let x10 = x10 +%^ x15 in
  let x5 = x5 ^^ x10 in
  let x5 = x5 <<< 7ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 16ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 12ul in
  let x1 = x1 +%^ x6 in
  let x12 = x12 ^^ x1 in
  let x12 = x12 <<< 8ul in
  let x11 = x11 +%^ x12 in
  let x6 = x6 ^^ x11 in
  let x6 = x6 <<< 7ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 16ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 12ul in
  let x2 = x2 +%^ x7 in
  let x13 = x13 ^^ x2 in
  let x13 = x13 <<< 8ul in
  let x8 = x8 +%^ x13 in
  let x7 = x7 ^^ x8 in
  let x7 = x7 <<< 7ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 16ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 12ul in
  let x3 = x3 +%^ x4 in
  let x14 = x14 ^^ x3 in
  let x14 = x14 <<< 8ul in
  let x9 = x9 +%^ x14 in
  let x4 = x4 ^^ x9 in
  let x4 = x4 <<< 7ul in
  (* 10 *)
  let x0 = x0 +%^ j0 in
  let x1 = x1 +%^ j1 in
  let x2 = x2 +%^ j2 in
  let x3 = x3 +%^ j3 in
  let x4 = x4 +%^ j4 in
  let x5 = x5 +%^ j5 in
  let x6 = x6 +%^ j6 in
  let x7 = x7 +%^ j7 in
  let x8 = x8 +%^ j8 in
  let x9 = x9 +%^ j9 in
  let x10 = x10 +%^ j10 in
  let x11 = x11 +%^ j11 in
  let x12 = x12 +%^ j12 in
  let x13 = x13 +%^ j13 in
  let x14 = x14 +%^ j14 in
  let x15 = x15 +%^ j15 in
  let open FStar.Buffer in
  let m0 = load32_le (sub m 0ul 4ul) in
  let m1 = load32_le (sub m 4ul 4ul) in
  let m2 = load32_le (sub m 8ul 4ul) in
  let m3 = load32_le (sub m 12ul 4ul) in
  let m4 = load32_le (sub m 16ul 4ul) in
  let m5 = load32_le (sub m 20ul 4ul) in
  let m6 = load32_le (sub m 24ul 4ul) in
  let m7 = load32_le (sub m 28ul 4ul) in
  let m8 = load32_le (sub m 32ul 4ul) in
  let m9 = load32_le (sub m 36ul 4ul) in
  let m10 = load32_le (sub m 40ul 4ul) in
  let m11 = load32_le (sub m 44ul 4ul) in
  let m12 = load32_le (sub m 48ul 4ul) in
  let m13 = load32_le (sub m 52ul 4ul) in
  let m14 = load32_le (sub m 56ul 4ul) in
  let m15 = load32_le (sub m 60ul 4ul) in
  let x0 = x0 ^^ m0 in
  let x1 = x1 ^^ m1 in
  let x2 = x2 ^^ m2 in
  let x3 = x3 ^^ m3 in
  let x4 = x4 ^^ m4 in
  let x5 = x5 ^^ m5 in
  let x6 = x6 ^^ m6 in
  let x7 = x7 ^^ m7 in
  let x8 = x8 ^^ m8 in
  let x9 = x9 ^^ m9 in
  let x10 = x10 ^^ m10 in
  let x11 = x11 ^^ m11 in
  let x12 = x12 ^^ m12 in
  let x13 = x13 ^^ m13 in
  let x14 = x14 ^^ m14 in
  let x15 = x15 ^^ m15 in
  store32_le (sub c 0ul 4ul) x0;
  store32_le (sub c 4ul 4ul) x1;
  store32_le (sub c 8ul 4ul) x2;
  store32_le (sub c 12ul 4ul) x3;
  store32_le (sub c 16ul 4ul) x4;
  store32_le (sub c 20ul 4ul) x5;
  store32_le (sub c 24ul 4ul) x6;
  store32_le (sub c 28ul 4ul) x7;
  store32_le (sub c 32ul 4ul) x8;
  store32_le (sub c 36ul 4ul) x9;
  store32_le (sub c 40ul 4ul) x10;
  store32_le (sub c 44ul 4ul) x11;
  store32_le (sub c 48ul 4ul) x12;
  store32_le (sub c 52ul 4ul) x13;
  store32_le (sub c 56ul 4ul) x14;
  store32_le (sub c 60ul 4ul) x15


module U32 = FStar.UInt32

val chacha_encrypt_bytes_loop:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:U32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
let rec chacha_encrypt_bytes_loop ctx m c len =
  if FStar.UInt32 (len <^ 64ul) then ()
  else (
    chacha_encrypt_bytes_core ctx m c;
    let ctr = ctx.(12ul) in
    ctx.(12ul) <- FStar.UInt32 (ctr +%^ 1ul);
    chacha_encrypt_bytes_loop ctx (offset m 64ul) (offset c 64ul) (FStar.UInt32 (len -^ 64ul))
  )


val chacha_encrypt_bytes_finish:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c /\ U32.v len < 64} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
let chacha_encrypt_bytes_finish ctx m c len =
  let hinit = ST.get() in
  push_frame();
  let h0 = ST.get() in
  let tmp = create (0uy) 64ul in
  let h0' = ST.get() in
  blit m 0ul tmp 0ul len;
  let h1 = ST.get() in
  chacha_encrypt_bytes_core ctx tmp tmp;
  let h2 = ST.get() in
  blit tmp 0ul c 0ul len;
  let h3 = ST.get() in
  lemma_modifies_2_1'' ctx c h0 h2 h3;
  pop_frame();
  let hfin = ST.get() in
  ()


val chacha_encrypt_bytes:
  ctx:chacha_ctx ->
  m:uint8_p ->
  c:uint8_p{disjoint ctx c} ->
  len:UInt32.t{U32.v len <= length m /\ U32.v len <= length c} ->
  Stack unit
    (requires (fun h -> live h c /\ live h m /\ live h ctx))
    (ensures  (fun h0 _ h1 -> live h1 c /\ modifies_2 ctx c h0 h1))
let rec chacha_encrypt_bytes ctx m c len =
  chacha_encrypt_bytes_loop ctx m c len;
  UInt.logand_mask (U32.v len) 6;
  assert_norm(pow2 6 = 64);
  Math.Lemmas.euclidean_division_definition (v len) 64;
  let rem = U32 (len &^ 63ul) in // % 64
  let q   = U32 (len >>^ 6ul) in // / 64
  if FStar.UInt32 (rem >=^ 0ul) then (
    let m = offset m (U32 (len -^ rem)) in
    let c = offset c (U32 (len -^ rem)) in
    chacha_encrypt_bytes_finish ctx m c rem)
