module Crypto.AEAD.Chacha20Poly1305

open FStar.HST
open FStar.Buffer
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open Crypto.Symmetric.Chacha20

// now hiding the 1-time MAC state & implementation
module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

//TODO move to some library
type lbytes (n:nat) = b:bytes{length b = n}

(* If the length is not a multipile of 16, pad to 16 *)
val pad_16: b:lbytes 16 -> len:UInt32.t { v len <= 16 } -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> 
    live h1 b /\ modifies_1 b h0 h1
    //TODO: be more precise, e.g. implement an injective spec.
  )) 
let pad_16 b len =
  // if len =^ 0ul then () else 
  memset (offset b len) 0uy (16ul -^ len)

let uint32_bytes v : Tot (u8 * u8 * u8 * u8)= 
  Int.Cast.uint32_to_uint8 v,
  Int.Cast.uint32_to_uint8 (v >>^ 8ul),
  Int.Cast.uint32_to_uint8 (v >>^ 16ul),
  Int.Cast.uint32_to_uint8 (v >>^ 24ul)

let upd_uint32 (b:bytes {length b >= 4}) x : STL unit
  (requires (fun h -> live h b /\ length b >= 4))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1)) =
  let v0,v1,v2,v3 = uint32_bytes x in 
  upd b 0ul v0;
  upd b 1ul v1;
  upd b 2ul v2;
  upd b 3ul v3

(* Serializes the two lengths into the final MAC word *)
private val length_word: b:lbytes 16 -> aad_len:UInt32.t -> len:UInt32.t -> STL unit
  (requires (fun h -> live h b))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
  // we'll similarly need an injective spec
let length_word b aad_len len =
  assume false; // not sure why this fails.
  upd_uint32 (offset b  0ul) aad_len;
  upd_uint32 (offset b  4ul) 0ul;
  upd_uint32 (offset b  8ul) len;
  upd_uint32 (offset b 12ul) 0ul

private val add_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.itext -> 
  a : MAC.accB i ->
  len: UInt32.t ->
  txt:lbytes (v len) -> STL MAC.itext
  (requires (fun h -> 
    live h txt /\ MAC.acc_inv st l0 a h))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\ 
    live h1 txt /\ 
//?    (MAC.ideal ==> l1 = MAC.encode_pad l0 (MAC.sel_bytes h0 txt)) /\
    MAC.acc_inv st l1 a h1))

let rec add_bytes #i st log a len txt =
  assume false; //TODO
  if len = 0ul then log 
  else if len <^ 16ul then 
    begin
      let w = create 0uy 16ul in
      blit txt 0ul w 0ul len;
      pad_16 w len;
      MAC.add st log a w
    end
  else 
    begin
      let w = Buffer.sub txt 0ul 16ul in 
      let log = MAC.add st log a w in
      add_bytes st log a (len -^ 16ul) (offset txt 16ul)
    end


(* AEAD-encrypt for Chacha20-Poly1305. Takes:
   - the initial key (key), an initialization vector (iv) and a constant (constant)
   - the additional data (aad)
   - the plaintext
   - the length of the plaintext (len) and the length of the additional data (len_aad)
   The result is stored in
   - ciphertext for the Chacha20 ciphertext, using the key (key), the iv and the nonce   
   - the Poly1305 tag on the ciphertext and the additional data
   *)

val chacha20_aead_encrypt: 
  key:lbytes 32 -> iv:UInt64.t -> constant:UInt32.t -> 
  aadlen:UInt32.t -> aadtext:lbytes (v aadlen) -> 
  plainlen:UInt32.t -> plaintext:lbytes (v plainlen) -> 
  ciphertext:lbytes (v plainlen) -> tag:MAC.tagB -> 
  STL unit
  (requires (fun h -> 
    live h key /\ live h aadtext /\ live h plaintext /\ 
    live h ciphertext /\ live h tag ))
  (ensures (fun h0 _ h1 -> 
    modifies_2 ciphertext tag h0 h1 /\ 
    live h1 ciphertext /\ live h1 tag ))

let chacha20_aead_encrypt key iv constant aadlen aadtext plainlen plaintext ciphertext tag =
  assume false; //TODO
  push_frame();

  (* Create OTK, using round '0' of Chacha20 *)
  (* Temporary buffers (to be improved) *)
  let state = create 0ul 32ul in (* Chacha inner state *)
  let counter = 0ul in
  chacha20_init state key counter iv constant;
  let otk  = create 0uy 32ul in (* OTK for Poly (to improve) *)
  chacha20_update otk state 32ul;

  (*  Encryption of the plaintext, using Chacha20, counter at 1 *)
  let counter = 1ul in
  chacha20_encrypt ciphertext key counter iv constant plaintext plainlen;

  (* Initialize MAC algorithm with one time key *)
  (* encapsulate (r,s) and a; we should probably clear otk *)
  let ak = MAC.coerce MAC.someId HyperHeap.root otk in 
  let acc = MAC.start ak in

  (* Update MAC with
     - padded additional data
     - padded ciphertext
     - formatted length *)
  (* the log is a sequence of abstract elements that encode the message *)
  (* This is not length-constant time, the lengths are assumed to be public data *)  

  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aadlen aadtext in
  let l = add_bytes ak l acc plainlen ciphertext in 
  let l = 
    let final_word = create 0uy 16ul in 
    length_word final_word aadlen plainlen;
    MAC.add ak l acc final_word in
  
  (* Finish MAC *)
  MAC.mac ak l acc tag;
  
  pop_frame()

  
//TODO: decryption!
