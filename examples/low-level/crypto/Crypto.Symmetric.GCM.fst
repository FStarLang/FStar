module Crypto.Symmetric.GCM

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.UInt8
open FStar.Int.Cast
open FStar.Buffer

module U32 = FStar.UInt32
type u32 = FStar.UInt32.t

assume MaxUInt8 : pow2 8 = 256
assume MaxUInt32: pow2 32 = 4294967296
assume MaxUInt64: pow2 64 > 0xfffffffffffffff
assume MaxUInt128: pow2 128 > pow2 64

#set-options "--z3timeout 10 --max_fuel 0 --initial_fuel 0"

type bytes = buffer byte

(* Define a type for all 16-byte block cipher algorithm *)
type cipher_alg (k: pos) = key:bytes{length key = k} ->
    input:bytes{length input = 16 /\ disjoint input key} ->
    out:bytes{length out = 16 /\ disjoint key out /\ disjoint input out} ->
    Stack unit
    (requires (fun h -> live h key /\ live h input /\ live h out))
    (ensures (fun h0 _ h1 -> live h1 key /\ live h1 input /\ live h1 out
        /\ modifies_1 out h0 h1))

(* * Every block of message is regarded as an element in Galois field GF(2^128), **)
(* * it is represented as 16 bytes. The following several functions are basic    **)
(* * operations in this field.                                                   **)
(* * gf128_add: addition. Equivalent to bitxor.                                  **)
(* * gf128_shift_right: shift right by 1 bit. Used in multiplication.            **)
(* * gf128_mul: multiplication. Achieved by combining 128 additions.             **)

(* Every function "func_name_loop" is a helper for function "func_name". *)
private val gf128_add_loop: a:bytes{length a = 16} ->
    b:bytes{length b = 16 /\ disjoint a b} ->
    dep:u32{U32.v dep <= 16} ->
    Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies_1 a h0 h1))
let rec gf128_add_loop a b dep =
  if U32 (dep =^ 0ul) then () else begin
    let i = U32 (dep -^ 1ul) in
    let ai = a.(i) in
    let bi = b.(i) in
    let x = ai ^^ bi in
    a.(i) <- x;
    gf128_add_loop a b i
  end

(* In place addition. Calculate "a + b" and store the result in a. *)
val gf128_add: a:bytes{length a = 16} ->
    b:bytes{length b = 16 /\ disjoint a b} ->
    Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies_1 a h0 h1))
let gf128_add a b = gf128_add_loop a b 16ul

private val gf128_shift_right_loop: a:bytes{length a = 16} ->
    dep:u32{U32.v dep < 16} ->
    Stack unit
    (requires (fun h -> live h a))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let rec gf128_shift_right_loop a dep =
  if U32.eq dep 0ul then begin
    let ai = a.(0ul) in
    let x = shift_right ai 1ul in
    a.(0ul) <- x
  end else begin
    let i = U32 (dep -^ 1ul) in
    let hd = a.(i) in
    let tl = a.(dep) in
    let x = (hd <<^ 7ul) +%^ (tl >>^ 1ul) in
    a.(dep) <- x;
    gf128_shift_right_loop a i
  end

(* In place shift. Calculate "a >> 1" and store the result in a. *)
private val gf128_shift_right: a:bytes{length a = 16} -> Stack unit
    (requires (fun h -> live h a))
    (ensures (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1))
let gf128_shift_right a = gf128_shift_right_loop a 15ul

(* Generate mask. If the i-th bit of num is 1 then return 11111111, otherwise return 00000000. *)
private val ith_bit_mask: num:byte -> i:u32{U32.v i < 8} -> Tot byte
let ith_bit_mask num i =
  let proj = shift_right (128uy) i in
  let res = logand num proj in
  eq_mask res proj

private val apply_mask_loop: a:bytes{length a = 16} ->
    m:bytes{length m = 16 /\ disjoint a m} ->
    msk:byte -> dep:u32{U32.v dep <= 16} -> Stack unit
    (requires (fun h -> live h a /\ live h m))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 m /\ modifies_1 m h0 h1))
let rec apply_mask_loop a m msk dep =
  if U32 (dep =^ 0ul) then () 
  else begin
    let i = U32 (dep -^ 1ul) in
    let ai = a.(i) in
    let x = ai &^ msk in
    m.(i) <- x;
    apply_mask_loop a m msk i
  end

(* This will apply a mask to each byte of bytes. *)
(* Mask a with msk, and store the result in m. *)
private val apply_mask: a:bytes{length a = 16} ->
    m:bytes{length m = 16 /\ disjoint a m} ->
    msk:byte -> Stack unit
    (requires (fun h -> live h a /\ live h m))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 m /\ modifies_1 m h0 h1))
let apply_mask a m msk = apply_mask_loop a m msk 16ul

private val r_mul: byte
let r_mul = 225uy

private val gf128_mul_loop: a:bytes{length a = 16} ->
    b:bytes{length b = 16 /\ disjoint a b} ->
    tmp:bytes{length tmp = 32 /\ disjoint a tmp /\ disjoint b tmp} ->
    dep:u32{U32.v dep <= 128} ->
    Stack unit
    (requires (fun h -> live h a /\ live h b /\ live h tmp))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ live h1 tmp
        /\ modifies_2 a tmp h0 h1))
let rec gf128_mul_loop a b tmp dep =
  if U32.eq dep 128ul then () else begin
    let r = sub tmp 0ul 16ul in
    let m = sub tmp 16ul 16ul in
    let num = b.(U32 (dep /^ 8ul)) in
    let msk = ith_bit_mask num (U32.rem dep 8ul) in
    apply_mask a m msk;
    gf128_add r m;
    let num = a.(15ul) in
    let msk = ith_bit_mask num 7ul in
    gf128_shift_right a;
    let num = a.(0ul) in
    a.(0ul) <- (num ^^ (logand msk r_mul));
    gf128_mul_loop a b tmp (U32 (dep +^ 1ul))
  end

(* In place multiplication. Calculate "a * b" and store the result in a.    *)
(* WARNING: can only pass lax check and may have issues with constant time. *)
val gf128_mul: a:bytes{length a = 16} ->
    b:bytes{length b = 16 /\ disjoint a b} -> Stack unit
    (requires (fun h -> live h a /\ live h b))
    (ensures (fun h0 _ h1 -> live h1 a /\ live h1 b /\ modifies_1 a h0 h1))
let gf128_mul a b =
  push_frame();
  let tmp = create (0uy) 32ul in
  gf128_mul_loop a b tmp 0ul;
  blit tmp 0ul a 0ul 16ul;
  pop_frame()

(* During authentication, the length information should also be included. *)
(* This function will generate an element in GF128 by:                    *)
(* 1. express len of additional data and len of ciphertext as 64-bit int; *)
(* 2. concatenate the two integers to get a 128-bit block.                *)
private val mk_len_info: len_info:bytes{length len_info = 16} ->
    len_1:u32 -> len_2:u32 -> Stack unit
    (requires (fun h -> live h len_info))
    (ensures (fun h0 _ h1 -> live h1 len_info /\ modifies_1 len_info h0 h1))
let mk_len_info len_info len_1 len_2 =
  let last = shift_left (uint32_to_uint8 len_1) 3ul in
  let open FStar.UInt32 in
  upd len_info 7ul last;
  let len_1 = len_1 >>^ 5ul in
  upd len_info 6ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 5ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 4ul (uint32_to_uint8 len_1);
  let len_1 = len_1 >>^ 8ul in
  upd len_info 3ul (uint32_to_uint8 len_1);
  let last = FStar.UInt8 (uint32_to_uint8 len_2 <<^ 3ul) in
  upd len_info 15ul last;
  let len_2 = len_2 >>^ 5ul in
  upd len_info 14ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 13ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 12ul (uint32_to_uint8 len_2);
  let len_2 = len_2 >>^ 8ul in
  upd len_info 11ul (uint32_to_uint8 len_2)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val ghash_loop_: tag:bytes{length tag = 16} ->
    auth_key:bytes{length auth_key = 16 /\ disjoint tag auth_key} ->
    str:bytes{disjoint tag str /\ disjoint auth_key tag} ->
    len:u32{length str = U32.v len} ->
    dep:u32{U32.v dep <= U32.v len} -> Stack unit
    (requires (fun h -> U32.v len - U32.v dep <= 16 /\ live h tag /\ live h auth_key /\ live h str))
    (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let ghash_loop_ tag auth_key str len dep =
  push_frame();
  let last = create (0uy) 16ul in
  blit str dep last 0ul (U32 (len -^ dep));
  gf128_add tag last;
  gf128_mul tag auth_key;
  pop_frame()

(* WARNING: can only pass lax check and may have issues with constant time. *)
private val ghash_loop: tag:bytes{length tag = 16} ->
    auth_key:bytes{length auth_key = 16 /\ disjoint tag auth_key} ->
    str:bytes{disjoint tag str /\ disjoint auth_key tag} ->
    len:u32{length str = U32.v len} ->
    dep:u32{U32.v dep <= U32.v len} -> Stack unit
    (requires (fun h -> live h tag /\ live h auth_key /\ live h str))
    (ensures (fun h0 _ h1 -> live h1 tag /\ live h1 auth_key /\ live h1 str /\ modifies_1 tag h0 h1))
let rec ghash_loop tag auth_key str len dep =
  (* Appending zeros if the last block is not a complete one. *)
  if U32 (16ul >=^ (len -^ dep)) then begin
    ghash_loop_ tag auth_key str len dep
  end else begin
    let next = U32.add dep 16ul in
    let si = sub str dep 16ul in
    gf128_add tag si;
    gf128_mul tag auth_key;
    ghash_loop tag auth_key str len next
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

(* A hash function used in authentication. It will authenticate additional data first, *)
(* then ciphertext and at last length information. The result is stored in tag.        *)
(* WARNING: can only pass lax check. *)
val ghash: auth_key:bytes{length auth_key = 16} ->
    ad:bytes{disjoint auth_key ad} ->
    adlen:u32{U32.v adlen = length ad} ->
    ciphertext:bytes{disjoint auth_key ciphertext /\ disjoint ad ciphertext} ->
    len:u32{U32.v len = length ciphertext} ->
    tag:bytes{length tag = 16 /\ disjoint auth_key tag /\ disjoint ad tag /\ disjoint ciphertext tag} ->
    Stack unit
    (requires (fun h -> live h auth_key /\ live h ad /\ live h ciphertext /\ live h tag))
    (ensures (fun h0 _ h1 -> live h1 auth_key /\ live h1 ad /\ live h1 ciphertext /\ live h1 tag
        /\ modifies_1 tag h0 h1))
let ghash auth_key ad adlen ciphertext len tag =
  push_frame();
  let h0 = HST.get() in
  let len_info = create (0uy) 16ul in
  mk_len_info len_info adlen len;
  let h1 = HST.get() in
  assert(modifies_0 h0 h1);
  fill tag (0uy) 16ul;
  ghash_loop tag auth_key ad adlen 0ul;
  ghash_loop tag auth_key ciphertext len 0ul;
  gf128_add tag len_info;
  gf128_mul tag auth_key;
  let h2 = HST.get() in
  assert(modifies_1 tag h1 h2);
  pop_frame()

(* Update the counter, replace last 4 bytes of counter with num. *)
(* num is precalculated by the function who calls this function. *)
private val update_counter: counter:bytes{length counter = 16} ->
    num:u32 -> Stack unit
    (requires (fun h -> live h counter))
    (ensures (fun h0 _ h1 -> live h1 counter /\ modifies_1 counter h0 h1))
let update_counter counter num =
  let open FStar.UInt32 in
  upd counter 15ul (uint32_to_uint8 num);
  let num = num >>^ 8ul in
  upd counter 14ul (uint32_to_uint8 num);
  let num = num >>^ 8ul in
  upd counter 13ul (uint32_to_uint8 num);
  let num = num >>^ 8ul in
  upd counter 12ul (uint32_to_uint8 num)

(* WARNING: may have issues with constant time. *)
private val auth_body: #k:pos -> alg:cipher_alg k ->
    ciphertext:bytes ->
    tag:bytes{length tag = 16 /\ disjoint ciphertext tag} ->
    key:bytes{length key = k /\ disjoint key ciphertext /\ disjoint tag key} ->
    nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:bytes{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    len:u32{length ciphertext = U32.v len} ->
    tmp:bytes{length tmp = 48 /\ disjoint ciphertext tmp /\ disjoint tag tmp /\ disjoint key tmp /\ disjoint nonce tmp /\ disjoint ad tmp} ->
    Stack unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad /\ live h tmp))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 tmp
        /\ modifies_2 tag tmp h0 h1))
let auth_body #k alg ciphertext tag key nonce cnt ad adlen len tmp =
  let h0 = HST.get() in
  fill tag (0uy) 16ul;
  let auth_key = sub tmp 0ul 16ul in
  alg key tag auth_key;
  ghash auth_key ad adlen ciphertext len tag;
  let counter = sub tmp 16ul 16ul in
  blit nonce 0ul counter 0ul 12ul;
  update_counter counter cnt;
  let c0 = sub tmp 32ul 16ul in
  alg key counter c0;
  gf128_add tag c0;
  let h1 = HST.get() in
  assert(live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 tmp /\ modifies_2 tag tmp h0 h1)

private val authenticate: #k:pos -> alg:cipher_alg k ->
    ciphertext:bytes ->
    tag:bytes{length tag = 16 /\ disjoint ciphertext tag} ->
    key:bytes{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:bytes{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad
        /\ modifies_1 tag h0 h1))
let authenticate #k alg ciphertext tag key nonce cnt ad adlen len =
  push_frame();
  let tmp = create (0uy) 48ul in
  auth_body #k alg ciphertext tag key nonce cnt ad adlen len tmp;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 50"

private val encrypt_loop: #k:pos -> alg:cipher_alg k ->
    ciphertext:bytes ->
    key:bytes{length key = k /\ disjoint ciphertext key} ->
    cnt:u32 ->
    plaintext:bytes{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint key plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    tmp:bytes{length tmp = 48 /\ disjoint ciphertext tmp /\ disjoint key tmp /\ disjoint plaintext tmp} ->
    dep:u32{U32.v dep <= U32.v len} ->
    Stack unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h plaintext /\ live h tmp))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp
        /\ modifies_2 ciphertext tmp h0 h1))
let rec encrypt_loop #k alg ciphertext key cnt plaintext len tmp dep =
  (* Appending zeros if the last block is not a complete one. *)
  if U32 (16ul >=^ (len -^ dep)) then begin
    let h0 = HST.get() in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let last = sub tmp 16ul 16ul in
    blit plaintext dep last 0ul (U32 (len -^ dep));
    let ci = sub tmp 32ul 16ul in
    alg key counter ci;
    gf128_add ci last;
    blit ci 0ul ciphertext dep (U32 (len -^ dep));
    let h1 = HST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end else begin
    let h0 = HST.get() in
    let pi = sub plaintext dep 16ul in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let ci = sub ciphertext dep 16ul in
    alg key counter ci;
    gf128_add ci pi;
    encrypt_loop #k alg ciphertext key (U32 (cnt +%^ 1ul)) plaintext len tmp (U32 (dep +^ 16ul));
    let h1 = HST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3timeout 20"

private val encrypt_body: #k:pos -> alg:cipher_alg k ->
    ciphertext:bytes ->
    tag:bytes{length tag = 16 /\ disjoint ciphertext tag} ->
    key:bytes{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:bytes{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    plaintext:bytes{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint tag plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext /\ disjoint ad plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 plaintext
        /\ modifies_2 ciphertext tag h0 h1))
let encrypt_body #k alg ciphertext tag key nonce cnt ad adlen plaintext len =
  push_frame();
  let tmp = create (0uy) 48ul in
  blit nonce 0ul tmp 0ul 12ul;
  encrypt_loop #k alg ciphertext key (U32 (cnt +%^ 1ul)) plaintext len tmp 0ul;
  authenticate #k alg ciphertext tag key nonce cnt ad adlen len;
  pop_frame()

#reset-options "--initial_fuel 0 --max_fuel 0"

(* * In GCM, an initialization vector is used to generate a 96-bit nonce, and can have any length. **)
(* * This version only allows 96-bit iv. This needs to be fixed.                                   **)
val encrypt: #k:pos -> alg:cipher_alg k ->
    ciphertext:bytes ->
    tag:bytes{length tag = 16 /\ disjoint ciphertext tag} ->
    key:bytes{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    iv:bytes{length iv = 12 /\ disjoint ciphertext iv /\ disjoint tag iv /\ disjoint key iv} ->
    ad:bytes{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint iv ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    plaintext:bytes{length plaintext = length ciphertext /\ disjoint ciphertext plaintext /\ disjoint tag plaintext /\ disjoint key plaintext /\ disjoint iv plaintext /\ disjoint ad plaintext} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack unit
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h iv /\ live h ad /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 iv /\ live h1 ad /\ live h1 plaintext
        /\ modifies_2 ciphertext tag h0 h1))
let encrypt #k alg ciphertext tag key iv ad adlen plaintext len =
  encrypt_body #k alg ciphertext tag key iv 1ul ad adlen plaintext len

(* * This is an incomplete decrypt function. The main idea is to compute tag first. **)
(* * If the result is compatible with the tag that user gives, then it will decrypt **)
(* * the ciphertext. Otherwise it will refuse to decrypt. The current GCM uses      **)
(* * encrypt function to decrypt and let the user check the tag himself.            **)
(*
val decrypt_body: #k:pos -> alg:cipher_alg k ->
    plaintext:u8s ->
    key:u8s{length key = k /\ disjoint plaintext key} ->
    nonce:u8s{length nonce = 12 /\ disjoint plaintext nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ciphertext:u8s{length ciphertext = length plaintext /\ disjoint plaintext ciphertext /\ disjoint key ciphertext /\ disjoint nonce ciphertext} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack unit
    (requires (fun h -> live h plaintext /\ live h key /\ live h nonce /\ live h ciphertext))
    (ensures (fun h0 _ h1 -> live h1 plaintext /\ live h1 key /\ live h1 nonce /\ live h1 ciphertext
        /\ modifies_1 plaintext h0 h1))
let decrypt_body #k alg plaintext key nonce cnt ciphertext len =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 48ul in
  blit nonce 0ul tmp 0ul 12ul;
  encrypt_loop #k alg plaintext key (U32.add_mod cnt 1ul) ciphertext len tmp 0ul;
  pop_frame()

val check_tag: #k:pos -> alg:cipher_alg k ->
    ciphertext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint ciphertext tag} ->
    key:u8s{length key = k /\ disjoint ciphertext key /\ disjoint tag key} ->
    nonce:u8s{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint tag nonce /\ disjoint key nonce} ->
    cnt:u32 ->
    ad:u8s{disjoint ciphertext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint nonce ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack bool
    (requires (fun h -> live h ciphertext /\ live h tag /\ live h key /\ live h nonce /\ live h ad))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad
        /\ modifies_0 h0 h1))
let check_tag #k alg ciphertext tag key nonce cnt ad adlen len =
  push_frame();
  let tmp = create (uint8_to_sint8 0uy) 16ul in
  authenticate #k alg ciphertext tmp key nonce cnt ad adlen len;
  let res = (* Compare tmp and tag *) true in
  pop_frame();
  admit();
  res

val decrypt: #k:pos -> alg:cipher_alg k ->
    plaintext:u8s ->
    tag:u8s{length tag = 16 /\ disjoint plaintext tag} ->
    key:u8s{length key = k /\ disjoint plaintext key /\ disjoint tag key} ->
    iv:u8s{length iv = 12 /\ disjoint plaintext iv /\ disjoint tag iv /\ disjoint key iv} ->
    ad:u8s{disjoint plaintext ad /\ disjoint tag ad /\ disjoint key ad /\ disjoint iv ad} ->
    adlen:u32{length ad = U32.v adlen} ->
    ciphertext:u8s{length ciphertext = length plaintext /\ disjoint plaintext ciphertext /\ disjoint tag ciphertext /\ disjoint key ciphertext /\ disjoint iv ciphertext /\ disjoint ad ciphertext} ->
    len:u32{length ciphertext = U32.v len} ->
    Stack bool
    (requires (fun h -> live h plaintext /\ live h tag /\ live h key /\ live h iv /\ live h ad /\ live h ciphertext))
    (ensures (fun h0 r h1 -> live h1 plaintext /\ live h1 tag /\ live h1 key /\ live h1 iv /\ live h1 ad /\ live h1 ciphertext
        /\ ((r /\ modifies_1 plaintext h0 h1) \/ ((not r) /\ modifies_0 h0 h1))))
let decrypt #k alg plaintext tag key iv ad adlen ciphertext len =
  let h0 = HST.get() in
  let check = check_tag #k alg ciphertext tag key iv 1ul ad adlen len in
  if not check then begin
    let h1 = HST.get() in
    assert(modifies_0 h0 h1);
    false
  end else begin
    let h0' = HST.get() in
    assert(modifies_0 h0 h0');
    decrypt_body #k alg plaintext key iv 1ul ciphertext len;
    let h1 = HST.get() in
    assert(modifies_1 plaintext h0 h1);admit();
    true
  end
*)
