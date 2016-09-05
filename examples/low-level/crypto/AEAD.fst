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

let index_u8 (b:bytes) (i:nat { n <= length bytes })= 
  if i = length b then () else
  let v: UInt.uint_t 8 = index b i in 
  UInt8.uint_to_t v

//TODO buffer_from_bytes and bytes_from_buffer, as written above. 

//TODO u64_from_bytes
//TODO u32_from_nat

let taglen = 16ul
let constant = 7ul 

type key = lbytes 32
type iv = lbytes 8
type cipher = b:bytes { length b >= v taglen }

val encrypt: alg:'a -> k:key -> iv:iv -> aad:bytes -> plain:bytes -> STL cipher
val decrypt: alg:'a -> k:key -> iv:iv -> aad:bytes -> cipher -> STL bytes 

module Core = Crypto.AEAD.Chacha20Poly1305

let encrypt _ k iv aad plain = 
  push_frame();

  let kB = create 0uy 32ul in
  buffer_from_bytes kB k; 

  let iv = u64_from_bytes iv in

  let aadlen   = u32_from_nat (length aad) in
  let aadB    = create 0uy aadlen in 
  buffer_from_bytes aadB aad;

  let plainlen = u32_from_nat (length plain) in
  let plainB  = create 0uy plainlen in 
  buffer_from_bytes plainB plain; 

  let cipherB = create 0uy (plainlen +^ taglen) in 
  Core.chacha20_aead_encrypt 
   kB iv constant 
   aadlen aadB 
   plainlen (sub cipherB 0uy plainlen) (sub cipherB plainlen taglen); 

  let cipher = bytes_from_buffer cipherB (plainlen +^ taglen) in

  pop_frame(); 
  cipher 

let decrypt _ k iv aad cipher = 
  push_frame();

  let kB = create 0uy 32ul in
  buffer_from_bytes kB k; 

  let iv = u64_from_bytes iv in

  let aadlen   = u32_from_nat (length aad) in
  let aadB    = create 0uy aadlen in 
  buffer_from_bytes aadB aad;

  let cipherlen = u32_from_nat (length cipher) in
  let cipherB = create 0uy cipherlen in 
  buffer_from_bytes cipherB cipher;

  let plainlen = cipherlen -^ taglen in 
  let plainB  = create 0uy plainlen in 
  Core.chacha20_aead_decrypt
   kB iv constant 
   aadlen aadB 
   plainlen (sub cipherB 0uy plainlen) (sub cipherB plainlen taglen); 

  let plain = bytes_from_buffer plainB plainlen in

  pop_frame(); 
  plain

