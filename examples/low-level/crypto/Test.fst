module Test 

open FStar.HST
open FStar.UInt32
open FStar.Ghost

open Crypto.Symmetric.Bytes
open Plain 
open Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC
module PRF = Crypto.Symmetric.Chacha20.PRF
module AE = Crypto.AEAD.Chacha20Poly1305.Ideal

// TESTING 

val load_string: l:UInt32.t -> buf:lbuffer (v l) -> STL string // (s:string {String.length s == v l})
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 s h1 -> h0 == h1 ))
let rec load_string l buf = 
  if l = 0ul then "" else
  //16-09-20 we miss String.init, proper refinements, etc
  let b = UInt8.v (Buffer.index buf 0ul) in
  let s = String.make 1 (Char.char_of_int b) in
  let t = load_string (l -^ 1ul) (Buffer.sub buf 1ul (l -^ 1ul)) in
  String.strcat s t

val store_string: len:UInt32.t -> buf:lbuffer (v len) -> i:UInt32.t {i <=^ len} -> s:string {String.length s = v len} -> STL unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1))
 
let rec store_string len buf i s = 
  if i <^ len then (
  Buffer.upd buf i (UInt8.uint_to_t (Char.int_of_char (String.index s (v i)))); 
  store_string len buf (i +^ 1ul) s )


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
  (ensures (fun h0 r h1 -> Buffer.modifies_0 h0 h1 /\ Buffer.live h1 r )) // how to express freshness?

let from_string len s = 
  let buf = Buffer.create 0uy len in
  (if String.length s = v len then store_string len buf 0ul s);
  buf 

(*
val store_bytestring: len:UInt32.t -> buf:lbuffer (v len) -> i:UInt32.t {i <=^ len} -> s:string {String.length s = v len + v len} -> STL unit
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
  Buffer.upd buf i (FStar.UInt8(x1 *^ 16uy +^ x0));
  store_bytestring len buf (FStar.UInt32(i +^ 1ul)) s )

let from_bytestring s = 
  let l = String.length s in 
  assume(l/2 + l/2 = l /\  l/2 <= UInt.max_int UInt32.n);
  let len = UInt32.uint_to_t (l/2) in 
  let buf = Buffer.create 0uy len in 
  store_bytestring len buf 0ul s;  
  buf 
*)


val test: unit -> ST UInt32.t //16-10-04 workaround against very large inferred type. 
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
let test() = 
  push_frame(); 
  let plainlen = 114ul in 
  let plainrepr = from_string plainlen 
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it." in

  let i:id = 42ul in
  assume(not(Plain.authId i));
  let plain = Plain.create i 0uy plainlen in 
  let plainbytes = make (v plainlen) (load_bytes plainlen plainrepr) in 
  Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let aad = Buffer.createL [
    0x50uy; 0x51uy; 0x52uy; 0x53uy; 0xc0uy; 0xc1uy; 0xc2uy; 0xc3uy; 0xc4uy; 0xc5uy; 0xc6uy; 0xc7uy ] in
  let aadlen = 12ul in 
  let key = Buffer.createL [ 
    0x80uy; 0x81uy; 0x82uy; 0x83uy; 0x84uy; 0x85uy; 0x86uy; 0x87uy; 0x88uy; 0x89uy; 0x8auy; 0x8buy; 0x8cuy; 0x8duy; 0x8euy; 0x8fuy; 
    0x90uy; 0x91uy; 0x92uy; 0x93uy; 0x94uy; 0x95uy; 0x96uy; 0x97uy; 0x98uy; 0x99uy; 0x9auy; 0x9buy; 0x9cuy; 0x9duy; 0x9euy; 0x9fuy ] in
  let ivBuffer = Buffer.createL [
    0x07uy; 0x00uy; 0x00uy; 0x00uy; 0x40uy; 0x41uy; 0x42uy; 0x43uy; 0x44uy; 0x45uy; 0x46uy; 0x47uy ] in
  let iv = load_uint128 12ul ivBuffer in
  let expected_cipher = Buffer.createL [ 
    0xd3uy; 0x1auy; 0x8duy; 0x34uy; 0x64uy; 0x8euy; 0x60uy; 0xdbuy; 0x7buy; 0x86uy; 0xafuy; 0xbcuy; 0x53uy; 0xefuy; 0x7euy; 0xc2uy; 
    0xa4uy; 0xaduy; 0xeduy; 0x51uy; 0x29uy; 0x6euy; 0x08uy; 0xfeuy; 0xa9uy; 0xe2uy; 0xb5uy; 0xa7uy; 0x36uy; 0xeeuy; 0x62uy; 0xd6uy; 
    0x3duy; 0xbeuy; 0xa4uy; 0x5euy; 0x8cuy; 0xa9uy; 0x67uy; 0x12uy; 0x82uy; 0xfauy; 0xfbuy; 0x69uy; 0xdauy; 0x92uy; 0x72uy; 0x8buy; 
    0x1auy; 0x71uy; 0xdeuy; 0x0auy; 0x9euy; 0x06uy; 0x0buy; 0x29uy; 0x05uy; 0xd6uy; 0xa5uy; 0xb6uy; 0x7euy; 0xcduy; 0x3buy; 0x36uy; 
    0x92uy; 0xdduy; 0xbduy; 0x7fuy; 0x2duy; 0x77uy; 0x8buy; 0x8cuy; 0x98uy; 0x03uy; 0xaeuy; 0xe3uy; 0x28uy; 0x09uy; 0x1buy; 0x58uy; 
    0xfauy; 0xb3uy; 0x24uy; 0xe4uy; 0xfauy; 0xd6uy; 0x75uy; 0x94uy; 0x55uy; 0x85uy; 0x80uy; 0x8buy; 0x48uy; 0x31uy; 0xd7uy; 0xbcuy; 
    0x3fuy; 0xf4uy; 0xdeuy; 0xf0uy; 0x8euy; 0x4buy; 0x7auy; 0x9duy; 0xe5uy; 0x76uy; 0xd2uy; 0x65uy; 0x86uy; 0xceuy; 0xc6uy; 0x4buy; 
    0x61uy; 0x16uy; 0x1auy; 0xe1uy; 0x0buy; 0x59uy; 0x4fuy; 0x09uy; 0xe2uy; 0x6auy; 0x7euy; 0x90uy; 0x2euy; 0xcbuy; 0xd0uy; 0x60uy; 
    0x06uy; 0x91uy ] in 
  let cipherlen = plainlen +^ 16ul in 
  assert(Buffer.length expected_cipher = v cipherlen);
  // print_string "Testing AEAD chacha20_poly1305...\n";
  let cipher = Buffer.create 0uy cipherlen in
  let st = AE.gen i HH.root in 
  AE.encrypt i st iv aadlen aad plainlen plain cipher; 
  let ok0 = Buffer.eqb expected_cipher cipher cipherlen in
  // failwith "ERROR: encrypted ciphertext mismatch";

  let decrypted = Plain.create i 0uy plainlen in
  let is_verified = AE.decrypt i st iv aadlen aad plainlen decrypted cipher = 0ul in

  let ok1 = Buffer.eqb (bufferRepr #i decrypted) (bufferRepr #i plain) plainlen in
  //failwith "ERROR: decrypted plaintext mismatch"

  pop_frame ();
  if is_verified && ok0 && ok1 then 0ul else 1ul


(* missing a library:

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) -> HST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  test();
  C.exit_success

*)
