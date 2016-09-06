module AEAD 

// implementing TLS AEAD interface using low-level crypto;
// aka a mini CoreCrypto (with the same function signatures)

open FStar.HST
open FStar.Buffer
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils

// same FStar libraries as for mitls-fstar, but nothing TLS-specific
//TODO: use monotonicity
open FStar.Seq
open FStar.SeqProperties


//TODO fix path to open it
open Platform.Bytes // with bytes as immutable sequences of chars

(*** Plumbing ***)

(* let index_u8 (b:bytes) (i:nat { n <= length b })= 
  if i = length b then () else
  let v: UInt.uint_t 8 = index b i in 
  UInt8.uint_to_t v
*)

type bbytes = b:bytes { UInt.size (length b) 32 }

val bytes_from_buffer: buf: buffer UInt8.t -> len:UInt32.t { v len = Buffer.length buf } -> STL (lbytes (v len))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1))
let bytes_from_buffer buf len = 
  let s = to_seq buf len in 
  let contents (i:nat{ i < v len}) = FStar.Char.char_of_int (UInt8.v (Seq.index s i)) in
  initBytes (v len) contents 

val blit_bytes': i:nat -> buf:buffer UInt8.t -> bs:bytes {length bs = Buffer.length buf} -> STL unit 
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ modifies_1 buf h0 h1)) 
let rec blit_bytes' i buf bs = 
  if length bs <= i then () 
  else
    begin
      Buffer.upd buf (UInt32.uint_to_t i) (UInt8.uint_to_t (FStar.Char.int_of_char (index bs i)));
      blit_bytes' (i + 1) buf bs
    end
let blit_bytes = blit_bytes' 0

(*
val buffer_from_bytes: b:bbytes -> STL (buffer UInt8.t)
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> ... { Buffer.length buf = length b }
*)

let buffer_from_bytes b = 
  let len = UInt32.uint_to_t (length b) in 
  let buf = Buffer.create 0uy len in 
  blit_bytes buf b;
  buf 


open FStar.Mul

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:Seq.seq UInt8.t) : Tot (n:nat { Seq.length b > 0 ==> UInt.size n (8 * (Seq.length b))}) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else 
      begin 
        assume false; //TODO not sure which lemmas to use here. 
        UInt8.v (Seq.index b 0) + pow2 8 * little_endian (Seq.slice b 1 (Seq.length b))
      end
      
let u64_from_bytes (bs:lbytes 8)  = 
  let contents (i:nat{ i < 8 }) = UInt8.uint_to_t (FStar.Char.int_of_char (index bs i)) in 
  let s = Seq.init 8 contents in 
  let n = little_endian s in 
  assume (UInt.size n 64); 
  UInt64.uint_to_t n
  
(*** Core AEAD ***)

let taglen = 16ul
let constant = 7ul 

type key = lbytes 32
type iv = lbytes 8

type cipher = c:bbytes { length c >= v taglen }
type plain = p:bbytes { UInt.size (length p + v taglen) 32 } 

val encrypt: alg:'a -> k:key -> iv:iv -> aad:bbytes -> p:plain -> ST cipher
  (requires (fun _ -> True)) 
  (ensures (fun h0 c h1 -> h0 == h1 (* /\ length c = length p + v taglen *) ))

module Core = Crypto.AEAD.Chacha20Poly1305

let encrypt _ k iv aad plain = 
  push_frame();

  let kB = buffer_from_bytes k in
  let iv = u64_from_bytes iv in
  let aadB = buffer_from_bytes aad in
  let len = UInt32.uint_to_t (length plain) in 
  let plainB = buffer_from_bytes plain in 
  let cipherB = Buffer.create 0uy (len +^ taglen) in 
  Core.chacha20_aead_encrypt 
    kB iv constant 
    (UInt32.uint_to_t (length aad)) aadB 
    len plainB 
    (Buffer.sub cipherB 0ul len) 
    (Buffer.sub cipherB len taglen); 
  let cipher = bytes_from_buffer cipherB (len +^ taglen) in

  pop_frame(); 
  cipher 

val decrypt: alg:'a -> k:key -> iv:iv -> aad:bbytes -> c:cipher -> ST (option bbytes)
  (requires (fun _ -> True)) 
  (ensures (fun h0 o h1 -> h0 == h1 (* /\ (match o with | Some p -> length c = length p + v taglen | None -> True) *) ))

#reset-options "--z3timeout 100"

let decrypt _ k iv aad cipher = 
  push_frame();

  let kB = buffer_from_bytes k in
  let iv = u64_from_bytes iv in
  let aadB = buffer_from_bytes aad in
  let len = UInt32.uint_to_t (length cipher) -^ taglen in 
  let plainB = Buffer.create 0uy len in 
  let cipherB = buffer_from_bytes cipher in 
  let verified = Core.chacha20_aead_decrypt
    kB iv constant 
    (UInt32.uint_to_t (length aad)) aadB 
    len plainB 
    (Buffer.sub cipherB 0ul len) 
    (Buffer.sub cipherB len taglen) in
  let o = if verified = 0ul then Some(bytes_from_buffer plainB len) else None in

  pop_frame(); 
  o

