module Crypto.Test 

open FStar.UInt32
open FStar.Ghost

open Crypto.Symmetric.Bytes
open Plain 
open Buffer
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC
module PRF = Crypto.Symmetric.PRF
module AE = Crypto.AEAD
module AETypes = Crypto.AEAD.Invariant

module L = FStar.List.Tot

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
    let l = [ 0x50uy; 0x51uy; 0x52uy; 0x53uy; 0xc0uy; 0xc1uy; 0xc2uy; 0xc3uy; 0xc4uy; 0xc5uy; 0xc6uy; 0xc7uy ] in
    //assert_norm (L.length l == 12); // Doesn't work, the normalizer doesn't normalize a match
    assume (L.length l == 12);
    Buffer.createL l

let mk_key : mk_buf_t 32
  = fun () -> 
    let l = [0x80uy; 0x81uy; 0x82uy; 0x83uy; 0x84uy; 0x85uy; 0x86uy; 0x87uy; 0x88uy; 0x89uy; 0x8auy; 0x8buy; 0x8cuy; 0x8duy; 0x8euy; 0x8fuy; 
	     0x90uy; 0x91uy; 0x92uy; 0x93uy; 0x94uy; 0x95uy; 0x96uy; 0x97uy; 0x98uy; 0x99uy; 0x9auy; 0x9buy; 0x9cuy; 0x9duy; 0x9euy; 0x9fuy ] in
    assume (L.length l == 32);	     
    Buffer.createL l

let mk_ivBuffer : mk_buf_t 12 
  = fun () -> 
    let l = [0x07uy; 0x00uy; 0x00uy; 0x00uy; 0x40uy; 0x41uy; 0x42uy; 0x43uy; 0x44uy; 0x45uy; 0x46uy; 0x47uy ] in
    assume (L.length l == 12);
    Buffer.createL l

#set-options "--lax"
let mk_expected_cipher : mk_buf_t 130
  = fun () -> 
    let l = [0xd3uy; 0x1auy; 0x8duy; 0x34uy; 0x64uy; 0x8euy; 0x60uy; 0xdbuy; 0x7buy; 0x86uy; 0xafuy; 0xbcuy; 0x53uy; 0xefuy; 0x7euy; 0xc2uy; 
	     0xa4uy; 0xaduy; 0xeduy; 0x51uy; 0x29uy; 0x6euy; 0x08uy; 0xfeuy; 0xa9uy; 0xe2uy; 0xb5uy; 0xa7uy; 0x36uy; 0xeeuy; 0x62uy; 0xd6uy; 
	     0x3duy; 0xbeuy; 0xa4uy; 0x5euy; 0x8cuy; 0xa9uy; 0x67uy; 0x12uy; 0x82uy; 0xfauy; 0xfbuy; 0x69uy; 0xdauy; 0x92uy; 0x72uy; 0x8buy; 
	     0x1auy; 0x71uy; 0xdeuy; 0x0auy; 0x9euy; 0x06uy; 0x0buy; 0x29uy; 0x05uy; 0xd6uy; 0xa5uy; 0xb6uy; 0x7euy; 0xcduy; 0x3buy; 0x36uy; 
	     0x92uy; 0xdduy; 0xbduy; 0x7fuy; 0x2duy; 0x77uy; 0x8buy; 0x8cuy; 0x98uy; 0x03uy; 0xaeuy; 0xe3uy; 0x28uy; 0x09uy; 0x1buy; 0x58uy; 
	     0xfauy; 0xb3uy; 0x24uy; 0xe4uy; 0xfauy; 0xd6uy; 0x75uy; 0x94uy; 0x55uy; 0x85uy; 0x80uy; 0x8buy; 0x48uy; 0x31uy; 0xd7uy; 0xbcuy; 
	     0x3fuy; 0xf4uy; 0xdeuy; 0xf0uy; 0x8euy; 0x4buy; 0x7auy; 0x9duy; 0xe5uy; 0x76uy; 0xd2uy; 0x65uy; 0x86uy; 0xceuy; 0xc6uy; 0x4buy; 
	     0x61uy; 0x16uy; 0x1auy; 0xe1uy; 0x0buy; 0x59uy; 0x4fuy; 0x09uy; 0xe2uy; 0x6auy; 0x7euy; 0x90uy; 0x2euy; 0xcbuy; 0xd0uy; 0x60uy; 
	     0x06uy; 0x91uy ] in 
    assume (L.length l == 130);	     
    Buffer.createL l
    
#reset-options

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

let verbose = false

val diff: string -> l:UInt32.t -> expected:lbuffer (v l) -> computed:lbuffer (v l) -> ST bool
  (requires (fun h -> Buffer.live h expected /\ Buffer.live h computed))
  (ensures (fun h0 b h1 -> h0 == h1))
  
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
  (ensures (fun h0 b h1 -> h0 == h1))
let dump name len b =
  if verbose then 
    let _ = IO.debug_print_string (name^":\n") in 
    let _ = print_buffer b 0ul len in
    ()

let tweak pos b = Buffer.upd b pos (UInt8.logxor (Buffer.index b pos) 42uy) 

val test: unit -> ST bool //16-10-04 workaround against very large inferred type. 
  (requires (fun _ -> True))
  (ensures (fun _ _ _ -> True))
#set-options "--z3timeout 100000"  
let test() = 
  push_frame(); 
  let plainlen = 114ul in 
  let plainrepr = from_string plainlen 
    "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it." in

  let i:id = { cipher = CHACHA20_POLY1305; uniq = 42ul } in
  assume(not(prf i)); // Implementation used to extract satisfies this
  let plain = Plain.create i 0uy plainlen in 
  let plainval = load_bytes plainlen plainrepr in
  let plainbytes = Plain.make #i (v plainlen) plainval in 
  Plain.store plainlen plain plainbytes; // trying hard to forget we know the plaintext
  let aad = mk_aad () in
  let aadlen = 12ul in
  let key = mk_key () in 
  let ivBuffer = mk_ivBuffer() in 

  dump "Key" 32ul key;
  dump "IV" 12ul ivBuffer;
  dump "Additional Data" 12ul aad;

  let iv : Crypto.Symmetric.Cipher.iv (cipher_of_id i) = 
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
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) (AETypes.(st.log_region)) /\
    HH.disjoint (Buffer.frameOf cipher) (AETypes.(st.log_region)) /\
    HH.disjoint (Buffer.frameOf aad) (AETypes.(st.log_region))
  );
  AE.encrypt i st iv aadlen aad plainlen plain cipher;
  let ok_0 = diff "cipher" cipherlen expected_cipher cipher in

  let decrypted = Plain.create i 0uy plainlen in
  let st = AE.genReader st in
  let ok_1 = AE.decrypt i st iv aadlen aad plainlen decrypted cipher in
  let ok_2 = diff "decryption" plainlen (bufferRepr #i decrypted) (bufferRepr #i plain) in

  // testing that decryption fails when truncating aad or tweaking the ciphertext.
  let fail_0 = AE.decrypt i st iv (aadlen -^ 1ul) (Buffer.sub aad 0ul (aadlen -^ 1ul)) plainlen decrypted cipher in

  tweak 3ul cipher;
  let fail_1 = AE.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak 3ul cipher;

  tweak plainlen cipher;
  let fail_2 = AE.decrypt i st iv aadlen aad plainlen decrypted cipher in
  tweak plainlen cipher;
  
  pop_frame ();
  ok_0 && ok_1 && ok_2 && not (fail_0 || fail_1 || fail_2) 

val main: bool
let main =
  let ok = test () in
  IO.debug_print_string ("AEAD (CHACHA20_POLY1305) test vector" ^ (if ok then ": Ok.\n" else ":\nERROR.\n"))
  
// enabling plaintext access for real test vector

(* missing a library:

val main: Int32.t -> FStar.Buffer.buffer (FStar.Buffer.buffer C.char) -> ST.Stack Int32.t (fun _ -> true) (fun _ _ _ -> true)
let main argc argv =
  test();
  C.exit_success


private let hex1 (x:UInt8.t {FStar.UInt8.(x <^ 16uy)}) = 
  FStar.UInt8.(
    if x <^ 10uy then UInt8.to_string x else 
    if x = 10uy then "a" else 
    if x = 11uy then "b" else 
    if x = 12uy then "c" else 
    if x = 13uy then "d" else 
    if x = 14uy then "e" else "f")
private let hex2 x = 
  FStar.UInt8.(hex1 (x /^ 16uy) ^ hex1 (x %^ 16uy))

val print_buffer: s:buffer -> i:UInt32.t{UInt32.v i <= length s} -> len:UInt32.t{UInt32.v len <= length s} -> Stack unit
  (requires (fun h -> live h s))
  (ensures (fun h0 _ h1 -> h0 == h1))
let rec print_buffer s i len =
  let open FStar.UInt32 in
  if i <^ len then
    begin
      let b = Buffer.index s i in
      print (hex2 b);
      if i %^ 16ul = 0ul then print "\n";
      print_buffer s (i +^ 1ul) len
    end
  else
    print "\n"

*)
