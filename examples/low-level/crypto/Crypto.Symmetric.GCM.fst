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
module Crypto.Symmetric.GCM

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.UInt8
open FStar.Int.Cast
open FStar.Buffer

module U32 = FStar.UInt32
type u32 = FStar.UInt32.t

#set-options "--z3rlimit 10 --max_fuel 0 --initial_fuel 0"

type bytes = buffer byte

// carved out GF128 implementation
open Crypto.Symmetric.GF128


(* Define a type for all 16-byte block cipher algorithm *)
type cipher_alg (k: pos) = key:bytes{length key = k} ->
    input:bytes{length input = 16 /\ disjoint input key} ->
    out:bytes{length out = 16 /\ disjoint key out /\ disjoint input out} ->
    Stack unit
    (requires (fun h -> live h key /\ live h input /\ live h out))
    (ensures (fun h0 _ h1 -> live h1 key /\ live h1 input /\ live h1 out
        /\ modifies_1 out h0 h1))


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
#set-options "--z3rlimit 20"	
//NS: Hints are not replayable for this function, and for a few others below	
let auth_body #k alg ciphertext tag key nonce cnt ad adlen len tmp =
  let h0 = ST.get() in
  fill tag 0uy 16ul;
  let auth_key = sub tmp 0ul 16ul in
  alg key tag auth_key;
  ghash auth_key ad adlen ciphertext len tag;
  let counter = sub tmp 16ul 16ul in
  blit nonce 0ul counter 0ul 12ul;
  update_counter counter cnt;
  let c0 = sub tmp 32ul 16ul in
  alg key counter c0;
  finish tag c0;
  let h1 = ST.get() in
  assert(live h1 ciphertext /\ live h1 tag /\ live h1 key /\ live h1 nonce /\ live h1 ad /\ live h1 tmp /\ modifies_2 tag tmp h0 h1)

#set-options "--z3rlimit 10"	
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

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 50"

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
  if U32.(16ul >=^ (len -^ dep)) then begin
    let h0 = ST.get() in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let last = sub tmp 16ul 16ul in
    blit plaintext dep last 0ul (U32.(len -^ dep));
    let ci = sub tmp 32ul 16ul in
    alg key counter ci;
    gf128_add ci last;
    blit ci 0ul ciphertext dep (U32.(len -^ dep));
    let h1 = ST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end else begin
    let h0 = ST.get() in
    let pi = sub plaintext dep 16ul in
    let counter = sub tmp 0ul 16ul in
    update_counter counter cnt;
    let ci = sub ciphertext dep 16ul in
    alg key counter ci;
    gf128_add ci pi;
    encrypt_loop #k alg ciphertext key (U32.(cnt +%^ 1ul)) plaintext len tmp (U32.(dep +^ 16ul));
    let h1 = ST.get() in
    assert(live h1 ciphertext /\ live h1 key /\ live h1 plaintext /\ live h1 tmp /\ modifies_2 ciphertext tmp h0 h1)
  end

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 20"

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
  encrypt_loop #k alg ciphertext key (U32.(cnt +%^ 1ul)) plaintext len tmp 0ul;
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
  let h0 = ST.get() in
  let check = check_tag #k alg ciphertext tag key iv 1ul ad adlen len in
  if not check then begin
    let h1 = ST.get() in
    assert(modifies_0 h0 h1);
    false
  end else begin
    let h0' = ST.get() in
    assert(modifies_0 h0 h0');
    decrypt_body #k alg plaintext key iv 1ul ciphertext len;
    let h1 = ST.get() in
    assert(modifies_1 plaintext h0 h1);admit();
    true
  end
*)
