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
module Crypto.KrmlTest

(* Note: this file uses the test library from KreMLin and should extract to both
   C (via kremlib.c) and OCaml (via jk's implementation of kremlib in
   OCaml). Here's a suggested few lines you can put in your ~/.emacs:

(setq fstar-subp-prover-args '(
                               "--include" "D:/cygwin/home/protz/Code/fstar/ulib/hyperstack"
                               "--include" "D:/cygwin/home/protz/Code/fstar/examples/low-level/crypto/spartan"
                               "--include" "D:/cygwin/home/protz/Code/kremlin/kremlib"
                               "--include" "D:/cygwin/home/protz/Code/kremlin/test"
                               ))

*)

open FStar.UInt32
open FStar.Ghost
open FStar.Buffer
open FStar.HyperStack.ST

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Crypto.Config
open Crypto
open Buffer
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST

module Plain = Crypto.Plain
module MAC = Crypto.Symmetric.MAC
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module AE = Crypto.AEAD
module AETypes = Crypto.AEAD.Invariant
module D = Crypto.AEAD.Decrypt
module E = Crypto.AEAD.Encrypt

module L = FStar.List.Tot

#set-options "--lax"


let mk_buf_t (len:nat) =
  unit -> StackInline (Buffer.buffer UInt8.t)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 ->
       let open FStar.HyperStack in
       let open FStar.Buffer in
       ~(contains h0 b)
       /\ live h1 b /\ idx b = 0 /\ Buffer.length b = len
       /\ frameOf b = h0.tip
       /\ Map.domain h1.h == Map.domain h0.h
       /\ modifies_0 h0 h1
       ))

let mk_aad : mk_buf_t 12
  = fun () ->
    Buffer.createL [ 0x50uy; 0x51uy; 0x52uy; 0x53uy; 0xc0uy; 0xc1uy; 0xc2uy; 0xc3uy; 0xc4uy; 0xc5uy; 0xc6uy; 0xc7uy ]

let mk_key : mk_buf_t 32
  = fun () ->
    Buffer.createL [0x80uy; 0x81uy; 0x82uy; 0x83uy; 0x84uy; 0x85uy; 0x86uy; 0x87uy; 0x88uy; 0x89uy; 0x8auy; 0x8buy; 0x8cuy; 0x8duy; 0x8euy; 0x8fuy;
	     0x90uy; 0x91uy; 0x92uy; 0x93uy; 0x94uy; 0x95uy; 0x96uy; 0x97uy; 0x98uy; 0x99uy; 0x9auy; 0x9buy; 0x9cuy; 0x9duy; 0x9euy; 0x9fuy ]

let mk_ivBuffer : mk_buf_t 12
  = fun () ->
    Buffer.createL [0x07uy; 0x00uy; 0x00uy; 0x00uy; 0x40uy; 0x41uy; 0x42uy; 0x43uy; 0x44uy; 0x45uy; 0x46uy; 0x47uy ]

#set-options "--lax"
let mk_expected_cipher : mk_buf_t 130
  = fun () ->
    Buffer.createL [0xd3uy; 0x1auy; 0x8duy; 0x34uy; 0x64uy; 0x8euy; 0x60uy; 0xdbuy; 0x7buy; 0x86uy; 0xafuy; 0xbcuy; 0x53uy; 0xefuy; 0x7euy; 0xc2uy;
	     0xa4uy; 0xaduy; 0xeduy; 0x51uy; 0x29uy; 0x6euy; 0x08uy; 0xfeuy; 0xa9uy; 0xe2uy; 0xb5uy; 0xa7uy; 0x36uy; 0xeeuy; 0x62uy; 0xd6uy;
	     0x3duy; 0xbeuy; 0xa4uy; 0x5euy; 0x8cuy; 0xa9uy; 0x67uy; 0x12uy; 0x82uy; 0xfauy; 0xfbuy; 0x69uy; 0xdauy; 0x92uy; 0x72uy; 0x8buy;
	     0x1auy; 0x71uy; 0xdeuy; 0x0auy; 0x9euy; 0x06uy; 0x0buy; 0x29uy; 0x05uy; 0xd6uy; 0xa5uy; 0xb6uy; 0x7euy; 0xcduy; 0x3buy; 0x36uy;
	     0x92uy; 0xdduy; 0xbduy; 0x7fuy; 0x2duy; 0x77uy; 0x8buy; 0x8cuy; 0x98uy; 0x03uy; 0xaeuy; 0xe3uy; 0x28uy; 0x09uy; 0x1buy; 0x58uy;
	     0xfauy; 0xb3uy; 0x24uy; 0xe4uy; 0xfauy; 0xd6uy; 0x75uy; 0x94uy; 0x55uy; 0x85uy; 0x80uy; 0x8buy; 0x48uy; 0x31uy; 0xd7uy; 0xbcuy;
	     0x3fuy; 0xf4uy; 0xdeuy; 0xf0uy; 0x8euy; 0x4buy; 0x7auy; 0x9duy; 0xe5uy; 0x76uy; 0xd2uy; 0x65uy; 0x86uy; 0xceuy; 0xc6uy; 0x4buy;
	     0x61uy; 0x16uy; 0x1auy; 0xe1uy; 0x0buy; 0x59uy; 0x4fuy; 0x09uy; 0xe2uy; 0x6auy; 0x7euy; 0x90uy; 0x2euy; 0xcbuy; 0xd0uy; 0x60uy;
	     0x06uy; 0x91uy ]


let tweak pos b = Buffer.upd b pos (UInt8.logxor (Buffer.index b pos) 42uy)

val test: unit -> ST bool //16-10-04 workaround against very large inferred type.
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
#set-options "--z3rlimit 1000"
let test() =
  push_frame();
  let plainlen = 114ul in
  let plainrepr = FStar.Buffer.createL [
    0x4cuy; 0x61uy; 0x64uy; 0x69uy; 0x65uy; 0x73uy; 0x20uy; 0x61uy;
    0x6euy; 0x64uy; 0x20uy; 0x47uy; 0x65uy; 0x6euy; 0x74uy; 0x6cuy;
    0x65uy; 0x6duy; 0x65uy; 0x6euy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x63uy; 0x6cuy; 0x61uy; 0x73uy;
    0x73uy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy; 0x27uy; 0x39uy; 0x39uy;
    0x3auy; 0x20uy; 0x49uy; 0x66uy; 0x20uy; 0x49uy; 0x20uy; 0x63uy;
    0x6fuy; 0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x6fuy; 0x66uy; 0x66uy;
    0x65uy; 0x72uy; 0x20uy; 0x79uy; 0x6fuy; 0x75uy; 0x20uy; 0x6fuy;
    0x6euy; 0x6cuy; 0x79uy; 0x20uy; 0x6fuy; 0x6euy; 0x65uy; 0x20uy;
    0x74uy; 0x69uy; 0x70uy; 0x20uy; 0x66uy; 0x6fuy; 0x72uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x66uy; 0x75uy; 0x74uy; 0x75uy;
    0x72uy; 0x65uy; 0x2cuy; 0x20uy; 0x73uy; 0x75uy; 0x6euy; 0x73uy;
    0x63uy; 0x72uy; 0x65uy; 0x65uy; 0x6euy; 0x20uy; 0x77uy; 0x6fuy;
    0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x62uy; 0x65uy; 0x20uy; 0x69uy;
    0x74uy; 0x2euy
    ] in

  let i:id = testId CHACHA20_POLY1305 in
  assume(not(prf i)); // Implementation used to extract satisfies this
  // let plain = Plain.create i 0uy plainlen in
  // let plainval = load_bytes plainlen plainrepr in
  // let plainbytes = Plain.make #i (v plainlen) plainval in
  // Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let plain = Plain.unsafe_hide_buffer i plainrepr in
  let aad = mk_aad () in
  let aadlen = 12ul in
  let key = mk_key () in
  let ivBuffer = mk_ivBuffer() in

  let iv : Crypto.Symmetric.Cipher.iv (cipherAlg_of_id i) =
    lemma_little_endian_is_bounded (load_bytes 12ul ivBuffer);
    load_uint128 12ul ivBuffer in
  let expected_cipher = mk_expected_cipher () in
  let cipherlen = plainlen +^ 16ul in
  assert(Buffer.length expected_cipher = v cipherlen);
  let cipher = Buffer.create 0uy cipherlen in
  let st = AE.coerce i HH.root key in

  // To prove the assertion below for the concrete constants in PRF, AEAD:
  assert_norm (114 <= pow2 14);
  assert_norm (FStar.Mul.(114 <= 1999 * 64));
  assert(AETypes.safelen i (v plainlen) 1ul);
  //NS: These 3 separation properties are explicitly violated by allocating st in HH.root
  //    Assuming them for the moment
  assume (
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) (AETypes.AEADState?.log_region st) /\
    HH.disjoint (Buffer.frameOf cipher) (AETypes.AEADState?.log_region st) /\
    HH.disjoint (Buffer.frameOf aad) (AETypes.AEADState?.log_region st)
  );
  AEAD.Encrypt.encrypt i st iv aadlen aad plainlen plain cipher;

  TestLib.compare_and_print (C.string_of_literal "cipher") expected_cipher cipher cipherlen;

  (* let ok_0 = diff "cipher" cipherlen expected_cipher cipher in *)

  let decrypted = Plain.create i 0uy plainlen in

  let st = AE.genReader st in
  let ok_1 = AEAD.Decrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in

  TestLib.compare_and_print (C.string_of_literal "decryption") (bufferRepr #i plain) (bufferRepr #i decrypted) plainlen;
  (* let ok_2 = diff "decryption" plainlen (bufferRepr #i decrypted) (bufferRepr #i plain) in *)

  // testing that decryption fails when truncating aad or tweaking the ciphertext.
  let fail_0 = AEAD.Decrypt.decrypt i st iv (aadlen -^ 1ul) (Buffer.sub aad 0ul (aadlen -^ 1ul)) plainlen decrypted cipher in

  tweak 3ul cipher;
  let fail_1 = AEAD.Decrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak 3ul cipher;

  tweak plainlen cipher;
  let fail_2 = AEAD.Decrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak plainlen cipher;

  pop_frame ();
  (* ok_0 && ok_1 && ok_2 && not (fail_0 || fail_1 || fail_2)  *)
  ok_1 && not (fail_0 || fail_1 || fail_2)


// JP: unused parameter [tn] makes the function polymorphic... which I managed
// to tell using the F* log
let test_aes_gcm i (tn: UInt32.t) key ivBuffer aadlen aad plainlen plainrepr expected_cipher =
  push_frame();

  assume false;//16-10-31
  (* dump "Key" 32ul key; *)
  (* dump "IV" 12ul ivBuffer; *)
  (* dump "Plaintext" plainlen plainrepr; *)
  (* dump "Additional Data" aadlen aad; *)

  assume(not(prf i)); // Implementation used to extract satisfies this
  // let plain = Plain.create i 1uy plainlen in
  // let plainval = load_bytes plainlen plainrepr in
  // let plainbytes = Plain.make #i (v plainlen) plainval in
  // Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let plain = Plain.unsafe_hide_buffer i plainrepr in

  let st = AE.coerce i HH.root key in
  let iv : Crypto.Symmetric.Cipher.iv (cipherAlg_of_id i) =
    lemma_little_endian_is_bounded (load_bytes 12ul ivBuffer);
    load_uint128 12ul ivBuffer in
  let cipherlen = plainlen +^ 16ul in
  let cipher = Buffer.create 2uy cipherlen in
  AEAD.Encrypt.encrypt i st iv aadlen aad plainlen plain cipher;

  (* let ok_0 = diff "cipher" cipherlen expected_cipher cipher in  *)
  TestLib.compare_and_print (C.string_of_literal "cipher")  expected_cipher cipher cipherlen;

  let st = AE.genReader st in
  let decrypted = Plain.create i 3uy plainlen in
  let ok_1 = AEAD.Decrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  (* let ok_2 = diff "decryption" plainlen (bufferRepr #i plain) (bufferRepr #i decrypted) in *)

  TestLib.compare_and_print (C.string_of_literal "decryption") (bufferRepr #i decrypted) (bufferRepr #i plain) plainlen;
  (* let ok_2 = diff "decryption" plainlen (bufferRepr #i decrypted) (bufferRepr #i plain) in *)

  pop_frame();
  (* ok_0 && ok_1 && ok_2 *)
  ok_1


val test_aes_gcm_0: unit -> St bool
let test_aes_gcm_0 () =
  let i:id = testId AES_128_GCM in
  let k = Buffer.create 0uy 16ul in
  let plainlen = 0ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = Buffer.createL [
    0x58uy; 0xe2uy; 0xfcuy; 0xceuy; 0xfauy; 0x7euy; 0x30uy; 0x61uy;
    0x36uy; 0x7fuy; 0x1duy; 0x57uy; 0xa4uy; 0xe7uy; 0x45uy; 0x5auy ] in
  test_aes_gcm i 1ul k iv aadlen aad plainlen plain cipher

val test_aes_gcm_1: unit -> St bool
let test_aes_gcm_1 () =
  let i:id = testId AES_256_GCM in
  let k = Buffer.create 0uy 32ul in
  let plainlen = 0ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = Buffer.createL [
    0x53uy; 0x0fuy; 0x8auy; 0xfbuy; 0xc7uy; 0x45uy; 0x36uy; 0xb9uy;
    0xa9uy; 0x63uy; 0xb4uy; 0xf1uy; 0xc4uy; 0xcbuy; 0x73uy; 0x8buy ] in
  test_aes_gcm i 1ul k iv aadlen aad plainlen plain cipher

val test_aes_gcm_2: unit -> St bool
let test_aes_gcm_2 () =
  let i:id = testId AES_256_GCM in
  let k = Buffer.create 0uy 32ul in
  let plainlen = 16ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = Buffer.createL [
    0xceuy; 0xa7uy; 0x40uy; 0x3duy; 0x4duy; 0x60uy; 0x6buy; 0x6euy;
    0x07uy; 0x4euy; 0xc5uy; 0xd3uy; 0xbauy; 0xf3uy; 0x9duy; 0x18uy;

    0xd0uy; 0xd1uy; 0xc8uy; 0xa7uy; 0x99uy; 0x99uy; 0x6buy; 0xf0uy;
    0x26uy; 0x5buy; 0x98uy; 0xb5uy; 0xd4uy; 0x8auy; 0xb9uy; 0x19uy ] in
  assume(Buffer.length cipher = v(plainlen +^ 16ul));
  test_aes_gcm i 2ul k iv aadlen aad plainlen plain cipher

val test_aes_gcm_3: unit -> St bool
let test_aes_gcm_3 () =
  let i:id = testId AES_256_GCM in
  let k = Buffer.createL [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy;
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  assume(Buffer.length k = v 32ul);
  let plainlen = 64ul in
  let plain = Buffer.createL [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy;
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy;
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy;
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy;
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy;
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy;
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy;
    0xbauy; 0x63uy; 0x7buy; 0x39uy; 0x1auy; 0xafuy; 0xd2uy; 0x55uy ] in
  assume(Buffer.length plain = v plainlen);
  let iv = Buffer.createL [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy;
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  assume(Buffer.length iv = v 12ul);
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = Buffer.createL [
    0x52uy; 0x2duy; 0xc1uy; 0xf0uy; 0x99uy; 0x56uy; 0x7duy; 0x07uy;
    0xf4uy; 0x7fuy; 0x37uy; 0xa3uy; 0x2auy; 0x84uy; 0x42uy; 0x7duy;
    0x64uy; 0x3auy; 0x8cuy; 0xdcuy; 0xbfuy; 0xe5uy; 0xc0uy; 0xc9uy;
    0x75uy; 0x98uy; 0xa2uy; 0xbduy; 0x25uy; 0x55uy; 0xd1uy; 0xaauy;
    0x8cuy; 0xb0uy; 0x8euy; 0x48uy; 0x59uy; 0x0duy; 0xbbuy; 0x3duy;
    0xa7uy; 0xb0uy; 0x8buy; 0x10uy; 0x56uy; 0x82uy; 0x88uy; 0x38uy;
    0xc5uy; 0xf6uy; 0x1euy; 0x63uy; 0x93uy; 0xbauy; 0x7auy; 0x0auy;
    0xbcuy; 0xc9uy; 0xf6uy; 0x62uy; 0x89uy; 0x80uy; 0x15uy; 0xaduy;

    0xb0uy; 0x94uy; 0xdauy; 0xc5uy; 0xd9uy; 0x34uy; 0x71uy; 0xbduy;
    0xecuy; 0x1auy; 0x50uy; 0x22uy; 0x70uy; 0xe3uy; 0xccuy; 0x6cuy ] in
  assume(Buffer.length cipher = v (plainlen +^ 16ul));
  test_aes_gcm i 3ul k iv aadlen aad plainlen plain cipher

val test_aes_gcm_4: unit -> St bool
let test_aes_gcm_4 () =
  let i:id = testId AES_256_GCM in
  let k = Buffer.createL [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy;
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy;
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  assume(Buffer.length k = v 32ul);
  let plainlen = 60ul in
  let plain = Buffer.createL [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy;
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy;
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy;
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy;
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy;
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy;
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy;
    0xbauy; 0x63uy; 0x7buy; 0x39uy ] in
  assume(Buffer.length plain = v plainlen);
  let iv = Buffer.createL [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy;
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  assume(Buffer.length iv = v 12ul);
  let aadlen = 20ul in
  let aad = Buffer.createL [
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy;
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy;
    0xabuy; 0xaduy; 0xdauy; 0xd2uy ] in
  assume(Buffer.length aad = v aadlen);
  let cipher = Buffer.createL [
    0x52uy; 0x2duy; 0xc1uy; 0xf0uy; 0x99uy; 0x56uy; 0x7duy; 0x07uy;
    0xf4uy; 0x7fuy; 0x37uy; 0xa3uy; 0x2auy; 0x84uy; 0x42uy; 0x7duy;
    0x64uy; 0x3auy; 0x8cuy; 0xdcuy; 0xbfuy; 0xe5uy; 0xc0uy; 0xc9uy;
    0x75uy; 0x98uy; 0xa2uy; 0xbduy; 0x25uy; 0x55uy; 0xd1uy; 0xaauy;
    0x8cuy; 0xb0uy; 0x8euy; 0x48uy; 0x59uy; 0x0duy; 0xbbuy; 0x3duy;
    0xa7uy; 0xb0uy; 0x8buy; 0x10uy; 0x56uy; 0x82uy; 0x88uy; 0x38uy;
    0xc5uy; 0xf6uy; 0x1euy; 0x63uy; 0x93uy; 0xbauy; 0x7auy; 0x0auy;
    0xbcuy; 0xc9uy; 0xf6uy; 0x62uy;
                                    0x76uy; 0xfcuy; 0x6euy; 0xceuy;
    0x0fuy; 0x4euy; 0x17uy; 0x68uy; 0xcduy; 0xdfuy; 0x88uy; 0x53uy;
    0xbbuy; 0x2duy; 0x55uy; 0x1buy ] in
  assume(Buffer.length cipher = v (plainlen +^ 16ul));
  test_aes_gcm i 4ul k iv aadlen aad plainlen plain cipher

val main: unit -> ST FStar.Int32.t
  (requires (fun h -> True))
  (ensures  (fun h0 r h1 -> True))
let main () =
  let _ = test() in
  let _ = test_aes_gcm_0 () in
  let _ = test_aes_gcm_1 () in
  let _ = test_aes_gcm_2 () in
  let _ = test_aes_gcm_3 () in
  let _ = test_aes_gcm_4 () in
  C.exit_success
