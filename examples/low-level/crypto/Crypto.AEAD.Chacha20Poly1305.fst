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


(* If the length is not a multipile of 16, pad to 16 *)
val pad_16: b:bytes -> len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16 /\ v len < 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let pad_16 b len =
  if len =^ 0ul then ()
  else memset (offset b len) 0uy (16ul -^ len)

let uint32_bytes v : Tot (u8 * u8 * u8 * u8)= 
  Int.Cast.uint32_to_uint8 v,
  Int.Cast.uint32_to_uint8 (v >>^ 8ul),
  Int.Cast.uint32_to_uint8 (v >>^ 16ul),
  Int.Cast.uint32_to_uint8 (v >>^ 24ul)

let upd_uint32 b x : STL unit
  (requires (fun h -> live h b /\ length b >= 4))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1)) =

  let v0,v1,v2,v3 = uint32_bytes x in 
  upd b 0ul v0;
  upd b 1ul v1;
  upd b 2ul v2;
  upd b 3ul v3

(* Serializes the lengths into the appropriate format *)
private val length_bytes: b:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let length_bytes b len aad_len =
  upd_uint32 (offset b  0ul) len;
  upd_uint32 (offset b  4ul) 0ul;
  upd_uint32 (offset b  8ul) aad_len;
  upd_uint32 (offset b 12ul) 0ul


private val add_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.itext -> 
  a : MAC.accB i ->
  l : UInt32.t ->
  txt:bytes { length txt = v l } -> STL MAC.itext
  (requires (fun h -> 
    live h txt /\ MAC.acc_inv st l0 a h))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\ 
    live h1 txt /\ 
//?    (MAC.ideal ==> l1 = MAC.encode_pad l0 (MAC.sel_bytes h0 txt)) /\
    MAC.acc_inv st l1 a h1))

let rec add_bytes #i st log a l txt =
  assume false; //TODO
  if l = 0ul then log 
  else if l <^ 16ul then 
    begin
      let w = create 0uy 16ul in
      blit txt 0ul w 0ul l;
      pad_16 w (16ul -^ l);
      MAC.add st log a w
    end
  else 
    begin
      let w = Buffer.sub txt 0ul 16ul in 
      let l = MAC.add st log a w in
      let txt = offset txt 16ul in 
      add_bytes st log a l txt 
    end


(* AEAD-encrypt for Chacha20-Poly1305. Takes:
   - the additional data (aad)
   - the initial key (key)
   - an initialization vector (iv) and a constant (constant)
   - the plaintext
   - the length of the plaintext (len) and the length of the additional data (len_aad)
   The result is stored in
   - ciphertext for the Chacha20 ciphertext, using the key (key), the iv and the nonce   
   - the Poly1305 tag on the ciphertext and the additional data
   *)

val chacha20_aead_encrypt: ciphertext:bytes -> tag:bytes -> aad:bytes -> key:bytes -> iv:UInt64.t -> constant:UInt32.t -> plaintext:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> 
    live h ciphertext /\ live h tag /\ live h aad /\ live h key /\ live h plaintext
    /\ length ciphertext >= v len
    /\ length tag >= 16
    /\ length aad >= v aad_len
    /\ length key >= 32
    /\ length plaintext >= v len
  ))
  (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 tag /\ modifies_2 ciphertext tag h0 h1 ))
let chacha20_aead_encrypt ciphertext tag aad key iv constant plaintext len aad_len =
  assume false; //TODO
  push_frame();

  (* Temporary buffers (to be improved) *)
  let state = create 0ul 32ul in (* Chacha inner state *)
  chacha20_init state key 0ul iv constant;

  (*  Create OTK, using round '0' of Chacha20 *)
  let counter = 0ul in
  let otk   = create 0uy 32ul in (* OTK for Poly (to improve) *)
  chacha20_update otk state 32ul;

  (*  Encryption of the plaintext, using Chacha20, counter at 1 *)
  let counter = 1ul in
  chacha20_encrypt ciphertext key counter iv constant plaintext len;

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

  let final_word = create 0uy 16ul in 
  length_bytes final_word len aad_len;

  let l = MAC.text_0 in 
  let l = add_bytes ak l acc aad_len aad in
  let l = add_bytes ak l acc len ciphertext in 
  let l = MAC.add ak l acc final_word in
  
  (* Finish MAC *)
  MAC.mac ak l acc tag;
  
  pop_frame()

  
//TODO: decryption!
