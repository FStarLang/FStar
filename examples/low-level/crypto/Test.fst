module Test 

open FStar.HST
open FStar.UInt32
open FStar.Ghost

open Plain // including library stuff
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
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ modifies_1 buf h0 h1))
 
let rec store_string len buf i s = 
  if i <^ len then (
  Buffer.upd buf i (UInt8.uint_to_t (Char.int_of_char (String.index s (v i)))); 
  store_string len buf (i +^ 1ul) s )

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


let from_string (len:UInt32.t) s = 
  let buf = Buffer.create 0uy len in
  if String.length s = v len then store_string len buf 0ul s;  
  buf 

let from_bytestring s = 
  let l = String.length s in 
  assume(l/2 + l/2 = l /\  l/2 <= UInt.max_int UInt32.n);
  let len = UInt32.uint_to_t (l/2) in 
  let buf = Buffer.create 0uy len in 
  store_bytestring len buf 0ul s;  
  buf 
  

let test =
  push_frame(); 
  let plainlen = 114ul in 
  let plainrepr = from_string plainlen "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it." in

  let i:id = 42ul in
  let plain = Plain.create i 0uy plainlen in 
  let plainbytes = make (v plainlen) (load_bytes plainlen plainrepr) in 
  Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let aad = from_bytestring "50515253c0c1c2c3c4c5c6c7" in
  let aadlen = 12ul in 
  let key = from_bytestring "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f" in
  let iv = FStar.UInt64.of_string "0x4746454443424140" in
  let expected_cipher = from_bytestring (strcat "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116" "1ae10b594f09e26a7e902ecbd0600691") in 
  // print_string "Testing AEAD chacha20_poly1305...\n";
  let cipher = Buffer.create 0uy (plainlen +^ 16ul) in
  let decrypted = Plain.create i 0uy plainlen in

  let st = AE.gen i HH.root in 

  AE.encrypt i st iv aadlen aad plainlen plain cipher; 
  let is_verified = AE.decrypt i st iv aadlen aad plainlen decrypted cipher in
  
  pop_frame ()


//  let st = ... in 
(*
  time (fun () -> for i = 0 to 999 do
                    chacha20_aead_encrypt key iv constant 12 aad 114 plaintext ciphertext tag;
                  done) () "1000 iterations";
  (* Output result *)
  diff "cipher" expected_ciphertext ciphertext 114;
  diff "tag" expected_tag tag 16;

  let decrypted = FStar_Buffer.create 0 114 in
  if chacha20_aead_decrypt key iv constant 12 aad 114 decrypted ciphertext tag = 0
  then diff "decryption" plaintext decrypted 114
  else print_string "decryption failed";
*)


(*
let diff name expected computed len =
  print_string ("Expected "^name^":\n"); print expected len;
  print_string ("Computed "^name^":\n"); print computed len;
  if not(FStar_Buffer.eqb expected computed 16) then
    failwith "Doesn't match expected result"
*)         
