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
module Crypto.Test 

open FStar.UInt32
open FStar.Ghost

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Crypto.Config
open Buffer
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module AE = Crypto.AEAD
module AETypes = Crypto.AEAD.Invariant

module AEEncrypt = Crypto.AEAD.Encrypt
module AEDecrypt = Crypto.AEAD.Decrypt

module L = FStar.List.Tot

// Some helpers for our test routines

(** Shadowing Buffer.createL (trusting length passed) *)
val createL: #a:Type -> len:nat -> init:list a -> StackInline (Buffer.buffer a)
  (requires (fun h -> 0 < len /\ len < UInt.max_int 32))
  (ensures (fun (h0:mem) b h1 ->
     len > 0
     /\ ~(Buffer.contains h0 b)
     /\ Buffer.live h1 b /\ Buffer.idx b = 0 /\ Buffer.length b = len
     /\ Buffer.frameOf b = (HS.(h0.tip))
     /\ Map.domain (HS.(h1.h)) == Map.domain (HS.(h0.h))
     /\ Buffer.modifies_0 h0 h1
     /\ Buffer.as_seq h1 b == Seq.of_list init))
let createL #a len init =
  assume (L.length init == len);
  Buffer.createL init

unfold inline_for_extraction let mk_buf_t (len:nat) = 
  unit -> StackInline (Buffer.buffer UInt8.t)
     (requires (fun h -> True))
     (ensures (fun (h0:mem) b h1 -> 
       let open FStar.HyperStack in
       let open FStar.Buffer in
       ~(contains h0 b)
       /\ live h1 b /\ idx b = 0 /\ Buffer.length b = len
       /\ frameOf b = h0.tip
       /\ Map.domain h1.h == Map.domain h0.h
       /\ modifies_0 h0 h1))

let mk_aad : mk_buf_t 12
  = fun () ->
    createL 12 [ 
      0x50uy; 0x51uy; 0x52uy; 0x53uy; 0xc0uy; 0xc1uy; 0xc2uy; 0xc3uy; 
      0xc4uy; 0xc5uy; 0xc6uy; 0xc7uy ]

let mk_key : mk_buf_t 32
  = fun () -> 
    createL 32 [
      0x80uy; 0x81uy; 0x82uy; 0x83uy; 0x84uy; 0x85uy; 0x86uy; 0x87uy; 
      0x88uy; 0x89uy; 0x8auy; 0x8buy; 0x8cuy; 0x8duy; 0x8euy; 0x8fuy; 
      0x90uy; 0x91uy; 0x92uy; 0x93uy; 0x94uy; 0x95uy; 0x96uy; 0x97uy; 
      0x98uy; 0x99uy; 0x9auy; 0x9buy; 0x9cuy; 0x9duy; 0x9euy; 0x9fuy ]

let mk_ivBuffer : mk_buf_t 12 
  = fun () -> 
    createL 12 [
      0x07uy; 0x00uy; 0x00uy; 0x00uy; 0x40uy; 0x41uy; 0x42uy; 0x43uy; 
      0x44uy; 0x45uy; 0x46uy; 0x47uy ]

#set-options "--lax"
let mk_expected_cipher : mk_buf_t 130
  = fun () -> 
    createL 130 [
      0xd3uy; 0x1auy; 0x8duy; 0x34uy; 0x64uy; 0x8euy; 0x60uy; 0xdbuy; 
      0x7buy; 0x86uy; 0xafuy; 0xbcuy; 0x53uy; 0xefuy; 0x7euy; 0xc2uy; 
      0xa4uy; 0xaduy; 0xeduy; 0x51uy; 0x29uy; 0x6euy; 0x08uy; 0xfeuy; 
      0xa9uy; 0xe2uy; 0xb5uy; 0xa7uy; 0x36uy; 0xeeuy; 0x62uy; 0xd6uy; 
      0x3duy; 0xbeuy; 0xa4uy; 0x5euy; 0x8cuy; 0xa9uy; 0x67uy; 0x12uy; 
      0x82uy; 0xfauy; 0xfbuy; 0x69uy; 0xdauy; 0x92uy; 0x72uy; 0x8buy; 
      0x1auy; 0x71uy; 0xdeuy; 0x0auy; 0x9euy; 0x06uy; 0x0buy; 0x29uy; 
      0x05uy; 0xd6uy; 0xa5uy; 0xb6uy; 0x7euy; 0xcduy; 0x3buy; 0x36uy;
      0x92uy; 0xdduy; 0xbduy; 0x7fuy; 0x2duy; 0x77uy; 0x8buy; 0x8cuy; 
      0x98uy; 0x03uy; 0xaeuy; 0xe3uy; 0x28uy; 0x09uy; 0x1buy; 0x58uy; 
      0xfauy; 0xb3uy; 0x24uy; 0xe4uy; 0xfauy; 0xd6uy; 0x75uy; 0x94uy; 
      0x55uy; 0x85uy; 0x80uy; 0x8buy; 0x48uy; 0x31uy; 0xd7uy; 0xbcuy; 
      0x3fuy; 0xf4uy; 0xdeuy; 0xf0uy; 0x8euy; 0x4buy; 0x7auy; 0x9duy; 
      0xe5uy; 0x76uy; 0xd2uy; 0x65uy; 0x86uy; 0xceuy; 0xc6uy; 0x4buy; 
      0x61uy; 0x16uy; 0x1auy; 0xe1uy; 0x0buy; 0x59uy; 0x4fuy; 0x09uy; 
      0xe2uy; 0x6auy; 0x7euy; 0x90uy; 0x2euy; 0xcbuy; 0xd0uy; 0x60uy; 
      0x06uy; 0x91uy ] 
#reset-options

// TESTING 

val load_string: l:UInt32.t -> buf:lbuffer (v l) -> Stack string // (s:string {String.length s == v l})
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 s h1 -> h0 == h1 ))
let rec load_string l buf = 
  if l = 0ul then "" else
  //16-09-20 we miss String.init, proper refinements, etc
  let b = UInt8.v (Buffer.index buf 0ul) in
  let s = String.make 1 (Char.char_of_int b) in
  let t = load_string (l -^ 1ul) (Buffer.sub buf 1ul (l -^ 1ul)) in
  String.strcat s t

val store_string: len:UInt32.t -> buf:lbuffer (v len) -> i:UInt32.t {i <=^ len} -> s:string {String.length s = v len} -> Stack unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1))
let rec store_string len buf i s = 
  if i <^ len then
    begin
    Buffer.upd buf i (UInt8.uint_to_t (Char.int_of_char (String.index s (v i)))); 
    store_string len buf (i +^ 1ul) s
    end

(*
let print (s:bytes) (len:int) : unit =
  for i = 0 to len - 1 do
    Printf.printf "%02x" (index s i);
    if i < len - 1 then print_string ":"
  done;
  print_string "\n"
    
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Elapsed time for %s : %fs\n" s (Sys.time() -. t)
*)

val from_string: len:UInt32.t -> string -> StackInline (lbuffer (v len))
  (requires (fun h0 -> True))
  (ensures  (fun h0 r h1 -> ~(Buffer.live h0 r) /\ Buffer.live h1 r /\
    Buffer.modifies_0 h0 h1))
let from_string len s = 
  let buf = Buffer.create 0uy len in
  (if String.length s = v len then store_string len buf 0ul s);
  buf 


(*
val store_bytestring: len:UInt32.t -> buf:lbuffer (v len) -> i:UInt32.t {i <=^ len} -> s:string {String.length s = v len + v len} -> Stack unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ modifies_1 buf h0 h1))

let digit (c:Char.char) = 
  let x = Char.int_of_char c - Char.int_of_char '0' in
  if x < 0 || x >= 16 then 0uy else UInt8.uint_to_t x

let rec store_bytestring len buf i s =
  if i <^ len then (
  let x1 = digit (String.index s (UInt32.v i + UInt32.v i)) in
  let x0 = digit (String.index s (UInt32.v i + UInt32.v i + 1)) in
  //assert(x1 <^ 16uy /\ x0 <^ 16uy);
  Buffer.upd buf i (FStar.UInt8.(x1 *^ 16uy +^ x0));
  store_bytestring len buf (FStar.UInt32(i +^ 1ul)) s )

let from_bytestring s = 
  let l = String.length s in 
  assume(l/2 + l/2 = l /\  l/2 <= UInt.max_int UInt32.n);
  let len = UInt32.uint_to_t (l/2) in 
  let buf = Buffer.create 0uy len in 
  store_bytestring len buf 0ul s;  
  buf 
*)

let verbose = false // use for debugging

val diff: string -> l:UInt32.t -> expected:lbuffer (v l) -> computed:lbuffer (v l) -> ST bool
  (requires (fun h -> Buffer.live h expected /\ Buffer.live h computed))
  (ensures  (fun h0 b h1 -> h0 == h1))
let diff name len expected computed =
  let r = Buffer.eqb expected computed len in 
  if verbose || not r then 
    let _ = IO.debug_print_string ("Expected "^name^":\n") in 
    let _ = print_buffer expected 0ul len in 
    let _ = IO.debug_print_string ("Computed "^name^":\n") in
    let _ = print_buffer computed 0ul len in
    let _ = r || IO.debug_print_string "ERROR: unexpected result.\n" in
    r
  else r 

val dump: string -> l:UInt32.t -> b:lbuffer (v l) ->  ST unit
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 b h1 -> h0 == h1))
let dump name len b =
  if verbose then 
    let _ = IO.debug_print_string (name^":\n") in 
    let _ = print_buffer b 0ul len in
    ()

let tweak pos b = Buffer.upd b pos (UInt8.logxor (Buffer.index b pos) 42uy) 

val test: unit -> ST bool 
  (requires (fun _ -> True))
  (ensures  (fun h0 _ h1 -> True))
#set-options "--z3rlimit 50"
let test () = 
  push_frame(); 
  let plainlen = 114ul in 
  let plainrepr = from_string plainlen 
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it." in

  let i = testId CHACHA20_POLY1305 in
  assume(not(prf i)); // Implementation used to extract satisfies this
  let plain = Crypto.Plain.create i 0uy plainlen in 
  let plainval = load_bytes plainlen plainrepr in
  let plainbytes = Crypto.Plain.make #i (v plainlen) plainval in 
  Crypto.Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let aad = mk_aad () in
  let aadlen = 12ul in
  let key = mk_key () in 
  let ivBuffer = mk_ivBuffer() in 

  dump "Key" 32ul key;
  dump "IV" 12ul ivBuffer;
  dump "Additional Data" 12ul aad;

  let iv : Crypto.Symmetric.Cipher.iv (cipherAlg_of_id i) = 
    lemma_little_endian_is_bounded (load_bytes 12ul ivBuffer);
    load_uint128 12ul ivBuffer in
  let expected_cipher = mk_expected_cipher () in
  let cipherlen = plainlen +^ 16ul in
  assert(Buffer.length expected_cipher == v cipherlen);
  let cipher = Buffer.create 0uy cipherlen in
  let rgn = new_region HH.root in
  let st = AE.coerce i rgn key in
  // To prove the assertion below for the concrete constants in PRF, AEAD:
  assert_norm (114 <= pow2 14);  
  assert_norm (FStar.Mul.(114 <= 1999 * 64));
  assert_norm (AETypes.safelen i (v plainlen) 1ul);
  //TODO: may as well assume False
  assume (
    HS.is_eternal_region (Buffer.frameOf cipher) /\
    HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\
    HS.is_eternal_region (Buffer.frameOf aad));
  AEEncrypt.encrypt i st iv aadlen aad plainlen plain cipher;
  let ok_0 = diff "cipher" cipherlen expected_cipher cipher in

  let decrypted = Crypto.Plain.create i 0uy plainlen in
  let st = AE.genReader st in
  let ok_1 = AEDecrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  let ok_2 = diff "decryption" plainlen (bufferRepr #i decrypted) (bufferRepr #i plain) in

  // testing that decryption fails when truncating aad or tweaking the ciphertext.
  let fail_0 = AEDecrypt.decrypt i st iv (aadlen -^ 1ul) (Buffer.sub aad 0ul (aadlen -^ 1ul)) plainlen decrypted cipher in

  tweak 3ul cipher;
  let fail_1 = AEDecrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak 3ul cipher;

  tweak plainlen cipher;
  let fail_2 = AEDecrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak plainlen cipher;
  
  pop_frame ();
  ok_0 && ok_1 && ok_2 && not (fail_0 || fail_1 || fail_2) 

let alg i = Crypto.AEAD.Encoding.alg i
let aadmax = Crypto.AEAD.Encoding.aadmax
let safelen = Crypto.AEAD.Invariant.safelen

val test_aes_gcm: 
  i:id -> 
  tn:UInt32.t -> 
  key:lbuffer (v (Cipher.keylen (alg i))) ->
  ivBuffer:lbuffer 12 ->
  aadlen:UInt32.t {aadlen <=^ aadmax} -> 
  aad:lbuffer (v aadlen) -> 
  plainlen:UInt32.t{safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} -> 
  plainrepr:lbuffer (v plainlen) -> 
  cipher:lbuffer (v plainlen + v MAC.taglen) 
  { 
    Buffer.disjoint aad cipher /\
    Buffer.disjoint plainrepr aad /\
    Buffer.disjoint plainrepr cipher
//  HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
//  HH.disjoint (Buffer.frameOf cipher) st.log_region /\
//  HH.disjoint (Buffer.frameOf aad) st.log_region
  }
  ->
  ST bool //16-10-04 workaround against very large inferred type. 
  (requires (fun h -> True))
    //Buffer.live h key /\
    //Buffer.live h ivBuffer /\
    //Buffer.live h aad /\
    //Buffer.live h plainrepr /\
    //Buffer.live h cipher))
  (ensures (fun _ _ _ -> True))

let test_aes_gcm i tn key ivBuffer aadlen aad plainlen plainrepr expected_cipher =
  let h0 = ST.get() in
  assume (not(prf i) /\
    Buffer.live h0 key /\
    Buffer.live h0 ivBuffer /\
    Buffer.live h0 aad /\
    Buffer.live h0 plainrepr /\
    Buffer.live h0 expected_cipher);
  push_frame();

  dump "Key" (Cipher.keylen (alg i)) key;
  dump "IV" 12ul ivBuffer;
  dump "Plaintext" plainlen plainrepr;
  dump "Additional Data" aadlen aad;

  let plain = Crypto.Plain.create i 1uy plainlen in
  let plainval = load_bytes plainlen plainrepr in
  let plainbytes = Crypto.Plain.make #i (v plainlen) plainval in 
  Crypto.Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext

  let st = AE.coerce i HH.root key in
  let h = ST.get() in
  assume (Buffer.live h ivBuffer);
  let iv : Crypto.Symmetric.Cipher.iv (cipherAlg_of_id i) = 
    lemma_little_endian_is_bounded (load_bytes 12ul ivBuffer);
    load_uint128 12ul ivBuffer in
  let cipherlen = plainlen +^ 16ul in
  let cipher = Buffer.create 2uy cipherlen in
  assume False; // TODO: Satisfy requirements of AE.encrypt
  AEEncrypt.encrypt i st iv aadlen aad plainlen plain cipher;
  let ok_0 = diff "cipher" cipherlen expected_cipher cipher in

  let st = AE.genReader st in
  let decrypted = Crypto.Plain.create i 3uy plainlen in
  let ok_1 = AEDecrypt.decrypt i st iv aadlen aad plainlen decrypted cipher in
  let ok_2 = diff "decryption" plainlen (bufferRepr #i plain) (bufferRepr #i decrypted) in

  pop_frame();
  ok_0 && ok_1 && ok_2


val test_aes_gcm_1: unit -> St bool
let test_aes_gcm_1 () =
  push_frame();
  let i:id = testId AES_256_GCM in
  let k = Buffer.create 0uy 32ul in
  let plainlen = 0ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = createL 16 [
    0x53uy; 0x0fuy; 0x8auy; 0xfbuy; 0xc7uy; 0x45uy; 0x36uy; 0xb9uy;
    0xa9uy; 0x63uy; 0xb4uy; 0xf1uy; 0xc4uy; 0xcbuy; 0x73uy; 0x8buy ] in
  let b = test_aes_gcm i 1ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_2: unit -> St bool
let test_aes_gcm_2 () =
  push_frame();
  let i:id = testId AES_256_GCM in
  let k = Buffer.create 0uy 32ul in
  let plainlen = 16ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = createL 32 [
    0xceuy; 0xa7uy; 0x40uy; 0x3duy; 0x4duy; 0x60uy; 0x6buy; 0x6euy;
    0x07uy; 0x4euy; 0xc5uy; 0xd3uy; 0xbauy; 0xf3uy; 0x9duy; 0x18uy;
    0xd0uy; 0xd1uy; 0xc8uy; 0xa7uy; 0x99uy; 0x99uy; 0x6buy; 0xf0uy;
    0x26uy; 0x5buy; 0x98uy; 0xb5uy; 0xd4uy; 0x8auy; 0xb9uy; 0x19uy ] in
  assert_norm(AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 2ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_3: unit -> St bool
let test_aes_gcm_3 () =
  push_frame();
  let i:id = testId AES_256_GCM in
  let k = createL 32 [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy; 
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  let plainlen = 64ul in
  let plain = createL 64 [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy; 
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy; 
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy; 
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy; 
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy; 
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy; 
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy; 
    0xbauy; 0x63uy; 0x7buy; 0x39uy; 0x1auy; 0xafuy; 0xd2uy; 0x55uy ] in
  let iv = createL 12 [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = createL 80 [
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
  assert_norm(AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 3ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_4: unit -> St bool
let test_aes_gcm_4 () =
  push_frame();
  let i:id = testId AES_256_GCM in
  let k = createL 32 [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy; 
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  let plainlen = 60ul in
  let plain = createL 60 [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy; 
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy; 
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy; 
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy; 
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy; 
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy; 
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy; 
    0xbauy; 0x63uy; 0x7buy; 0x39uy ] in
  let iv = createL 12 [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  let aadlen = 20ul in 
  let aad = createL 20 [
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 
    0xabuy; 0xaduy; 0xdauy; 0xd2uy ] in
  let cipher = createL 76 [
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
  assert_norm(AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 4ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_5: unit -> St bool
let test_aes_gcm_5 () =
  push_frame();
  let i:id = testId AES_128_GCM in
  let k = Buffer.create 0uy 16ul in
  let plainlen = 0ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  let cipher = createL 16 [
    0x58uy; 0xe2uy; 0xfcuy; 0xceuy; 0xfauy; 0x7euy; 0x30uy; 0x61uy; 
    0x36uy; 0x7fuy; 0x1duy; 0x57uy; 0xa4uy; 0xe7uy; 0x45uy; 0x5auy ] in
  let b = test_aes_gcm i 1ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_6: unit -> St bool
let test_aes_gcm_6 () =
  push_frame();
  let i:id = testId AES_128_GCM in
  let k = Buffer.create 0uy 16ul in
  let plainlen = 16ul in
  let plain = Buffer.create 0uy plainlen in
  let iv = Buffer.create 0uy 12ul in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in 
  let cipher = createL 32 [
    0x03uy; 0x88uy; 0xdauy; 0xceuy; 0x60uy; 0xb6uy; 0xa3uy; 0x92uy; 
    0xf3uy; 0x28uy; 0xc2uy; 0xb9uy; 0x71uy; 0xb2uy; 0xfeuy; 0x78uy; 
    0xabuy; 0x6euy; 0x47uy; 0xd4uy; 0x2cuy; 0xecuy; 0x13uy; 0xbduy; 
    0xf5uy; 0x3auy; 0x67uy; 0xb2uy; 0x12uy; 0x57uy; 0xbduy; 0xdfuy ] in
  assert_norm (AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 2ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b

let cipher7 =
 [
    0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy;
    0x4buy; 0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy;
    0xe3uy; 0xaauy; 0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy;
    0x35uy; 0xc1uy; 0x7euy; 0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy;
    0x21uy; 0xd5uy; 0x14uy; 0xb2uy; 0x54uy; 0x66uy; 0x93uy; 0x1cuy;
    0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy; 0x84uy; 0xaauy; 0x05uy;
    0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy; 0xacuy; 0x97uy;
    0x3duy; 0x58uy; 0xe0uy; 0x91uy; 0x47uy; 0x3fuy; 0x59uy; 0x85uy;

    0x4duy; 0x5cuy; 0x2auy; 0xf3uy; 0x27uy; 0xcduy; 0x64uy; 0xa6uy;
    0x2cuy; 0xf3uy; 0x5auy; 0xbduy; 0x2buy; 0xa6uy; 0xfauy; 0xb4uy ]

let plain7 = [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy;
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy;
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy;
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy;
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy;
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy;
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy;
    0xbauy; 0x63uy; 0x7buy; 0x39uy; 0x1auy; 0xafuy; 0xd2uy; 0x55uy ]

#set-options "--z3rlimit 100"

val test_aes_gcm_7: unit -> St bool
let test_aes_gcm_7 () =
  push_frame();
  let i:id = testId AES_128_GCM in
  let k = createL 16 [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  let plainlen = 64ul in
  assert_norm (L.length plain7 == 64);
  let plain = Buffer.createL plain7 in
  let iv = createL 12 [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  let aadlen = 0ul in
  let aad = Buffer.create 0uy aadlen in
  assert_norm (L.length cipher7 == 80);
  let cipher = Buffer.createL cipher7 in
  assert_norm (AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 3ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val test_aes_gcm_8: unit -> St bool
let test_aes_gcm_8 () =
  push_frame();
  let i:id = testId AES_128_GCM in
  let k = createL 16 [
    0xfeuy; 0xffuy; 0xe9uy; 0x92uy; 0x86uy; 0x65uy; 0x73uy; 0x1cuy; 
    0x6duy; 0x6auy; 0x8fuy; 0x94uy; 0x67uy; 0x30uy; 0x83uy; 0x08uy ] in
  let plainlen = 60ul in
  let plain = createL 60 [
    0xd9uy; 0x31uy; 0x32uy; 0x25uy; 0xf8uy; 0x84uy; 0x06uy; 0xe5uy; 
    0xa5uy; 0x59uy; 0x09uy; 0xc5uy; 0xafuy; 0xf5uy; 0x26uy; 0x9auy; 
    0x86uy; 0xa7uy; 0xa9uy; 0x53uy; 0x15uy; 0x34uy; 0xf7uy; 0xdauy; 
    0x2euy; 0x4cuy; 0x30uy; 0x3duy; 0x8auy; 0x31uy; 0x8auy; 0x72uy; 
    0x1cuy; 0x3cuy; 0x0cuy; 0x95uy; 0x95uy; 0x68uy; 0x09uy; 0x53uy; 
    0x2fuy; 0xcfuy; 0x0euy; 0x24uy; 0x49uy; 0xa6uy; 0xb5uy; 0x25uy; 
    0xb1uy; 0x6auy; 0xeduy; 0xf5uy; 0xaauy; 0x0duy; 0xe6uy; 0x57uy; 
    0xbauy; 0x63uy; 0x7buy; 0x39uy ] in
  let iv = createL 12 [
    0xcauy; 0xfeuy; 0xbauy; 0xbeuy; 0xfauy; 0xceuy; 0xdbuy; 0xaduy; 
    0xdeuy; 0xcauy; 0xf8uy; 0x88uy ] in
  let aadlen = 20ul in 
  let aad = createL 20 [
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 
    0xfeuy; 0xeduy; 0xfauy; 0xceuy; 0xdeuy; 0xaduy; 0xbeuy; 0xefuy; 
    0xabuy; 0xaduy; 0xdauy; 0xd2uy ] in
  let cipher = createL 76 [
    0x42uy; 0x83uy; 0x1euy; 0xc2uy; 0x21uy; 0x77uy; 0x74uy; 0x24uy;
    0x4buy; 0x72uy; 0x21uy; 0xb7uy; 0x84uy; 0xd0uy; 0xd4uy; 0x9cuy;
    0xe3uy; 0xaauy; 0x21uy; 0x2fuy; 0x2cuy; 0x02uy; 0xa4uy; 0xe0uy;
    0x35uy; 0xc1uy; 0x7euy; 0x23uy; 0x29uy; 0xacuy; 0xa1uy; 0x2euy;
    0x21uy; 0xd5uy; 0x14uy; 0xb2uy; 0x54uy; 0x66uy; 0x93uy; 0x1cuy;
    0x7duy; 0x8fuy; 0x6auy; 0x5auy; 0xacuy; 0x84uy; 0xaauy; 0x05uy;
    0x1buy; 0xa3uy; 0x0buy; 0x39uy; 0x6auy; 0x0auy; 0xacuy; 0x97uy;
    0x3duy; 0x58uy; 0xe0uy; 0x91uy;
                                    0x5buy; 0xc9uy; 0x4fuy; 0xbcuy;
    0x32uy; 0x21uy; 0xa5uy; 0xdbuy; 0x94uy; 0xfauy; 0xe9uy; 0x5auy;
    0xe7uy; 0x12uy; 0x1auy; 0x47uy ] in
  assert_norm (AETypes.safelen i (v plainlen) 2ul);
  let b = test_aes_gcm i 4ul k iv aadlen aad plainlen plain cipher in
  pop_frame();
  b


val main: bool
let main =
  let ok = test () in
  let _  = IO.debug_print_string ("AEAD (CHACHA20_POLY1305) test vector" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_1() in 
  let _  = IO.debug_print_string ("AEAD (AES_256_GCM) test vector 1" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_2() in 
  let _  = IO.debug_print_string ("AEAD (AES_256_GCM) test vector 2" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_3() in 
  let _  = IO.debug_print_string ("AEAD (AES_256_GCM) test vector 3" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_4() in 
  let _  = IO.debug_print_string ("AEAD (AES_256_GCM) test vector 4" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_5() in 
  let _  = IO.debug_print_string ("AEAD (AES_128_GCM) test vector 1" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_6() in 
  let _  = IO.debug_print_string ("AEAD (AES_128_GCM) test vector 2" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_7() in 
  let _  = IO.debug_print_string ("AEAD (AES_128_GCM) test vector 3" ^ (if ok then ": Ok.\n" else ":\nERROR.\n")) in
  let ok = test_aes_gcm_8() in 
  IO.debug_print_string ("AEAD (AES_128_GCM) test vector 4" ^ (if ok then ": Ok.\n" else ":\nERROR.\n"))
