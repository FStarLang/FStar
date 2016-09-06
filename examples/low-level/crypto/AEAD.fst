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

let bytes_from_buffer buf len = 
  let s = to_seq buf len in 
  let contents (i:nat{ i < v len}) = FStar.Char.char_of_int (v (Seq.index s i)) in
  init (v len) contents 

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

open FStar.Mul

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:Seq.seq UInt8.t) : Tot (n:nat { Seq.length b > 0 ==> UInt.size n (8 * (Seq.length b))}) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else 
      begin 
        let x = pow2 8 * little_endian (Seq.slice b 1 (Seq.length b)) in
        assert( x < pow2 (8 * (Seq.length b)) - pow2 8);
        let y = UInt8.v (Seq.index b 0) in
        y
      end
      
let u64_from_bytes bs:lbytes 8  = 
  let s = Seq.init (length bs) (fun i -> UInt8.uint_to_t (FStar.Char.int_of_char (index bs i))) in 
  UInt64.uint_to_t (little_endian s)
  
(*** Core AEAD ***)

let taglen = 16ul
let constant = 7ul 

type key = lbytes 32
type iv = lbytes 8

type bbytes = b:bytes { UInt.size (length b) 32 }

type cipher = b:bbytes { length b >= v taglen }
type plain = b:bbytes { UInt.size (length b + v taglen) 32 } 

val encrypt: alg:'a -> k:key -> iv:iv -> aad:bbytes -> plain -> ST cipher 
  (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))
val decrypt: alg:'a -> k:key -> iv:iv -> aad:bbytes -> cipher -> ST plain 
  (requires (fun _ -> True)) (ensures (fun h0 _ h1 -> h0 == h1))

module Core = Crypto.AEAD.Chacha20Poly1305

let encrypt _ k iv aad plain = 
  push_frame();

  let kB = Buffer.create 0uy 32ul in
  blit_bytes kB k; 

  let iv = u64_from_bytes iv in

  let aadlen   = UInt32.uint_to_t (length aad) in
  let aadB    = Buffer.create 0uy aadlen in 
  blit_bytes aadB aad;

  let plainlen = UInt32.uint_to_t (length plain) in
  let plainB  = Buffer.create 0uy plainlen in 
  blit_bytes plainB plain; 

  let cipherB = Buffer.create 0uy (plainlen +^ taglen) in 
  Core.chacha20_aead_encrypt 
   kB iv constant 
   aadlen aadB 
   plainlen (sub cipherB 0uy plainlen) (sub cipherB plainlen taglen); 

  let cipher = bytes_from_buffer cipherB (plainlen +^ taglen) in

  pop_frame(); 
  cipher 

let decrypt _ k iv aad cipher = 
  push_frame();

  let kB = Buffer.create 0uy 32ul in
  blit_bytes kB k; 

  let iv = u64_from_bytes iv in

  let aadlen   = UInt32.uint_to_t (length aad) in
  let aadB    = Buffer.create 0uy aadlen in 
  blit_bytes aadB aad;

  let cipherlen = UInt32.uint_to_t (length cipher) in
  let cipherB = Buffer.create 0uy cipherlen in 
  blit_bytes cipherB cipher;

  let plainlen = cipherlen -^ taglen in 
  let plainB  = Buffer.create 0uy plainlen in 
  Core.chacha20_aead_decrypt
   kB iv constant 
   aadlen aadB 
   plainlen (sub cipherB 0uy plainlen) (sub cipherB plainlen taglen); 

  let plain = bytes_from_buffer plainB plainlen in

  pop_frame(); 
  plain

