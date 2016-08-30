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

//#set-options "--lax"

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
val length_bytes: b:bytes -> len:UInt32.t -> aad_len:UInt32.t -> STL unit
  (requires (fun h -> live h b /\ length b >= 16))
  (ensures  (fun h0 _ h1 -> live h1 b /\ modifies_1 b h0 h1))
let length_bytes b len aad_len =
  upd_uint32 (offset b  0ul) len;
  upd_uint32 (offset b  4ul) 0ul;
  upd_uint32 (offset b  8ul) aad_len;
  upd_uint32 (offset b 12ul) 0ul
  

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

(*
val mac_inv 
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.ilog -> 
  a : MAC.accB i -> Type

let mac_inv #i st l0 a h = 
  let r = MAC.State.r st in 
  live h a /\ 
  MAC.norm h a /\ 
  MAC.norm h r /\
  (MAC.ideal ==> MAC.sel_elem h a = Spec.poly l0 (MAC.sel_elem h r))))

val mac_bytes:
  #i: MAC.id ->
  st: MAC.state i ->
  l0: MAC.ilog -> 
  a : MAC.accB i ->
  txt:bytes -> STL MAC.ilog
  (requires (fun h -> 
    live h txt /\ mac_inv sst l0 a h))
  (ensures (fun h0 l1 h1 -> 
    modifies_1 a h0 h1 /\ 
    live h1 txt /\ mac_inv st l0 a h1live h1 a /\ MAC.norm h1 a /\ 
    (MAC.ideal ==> l1 = MAC.encode_pad l0 (MAC.sel_bytes h0 txt) /\
             MAC.sel_elem h1 a = Spec.poly l1 (MAC.sel_elem h0 r))))

let rec loop #i st l0 a txt ctr =
  if ctr = 0 then l0 else 
  begin
    let w = sub txt 0ul 16ul in
    let l1 = add st l0 a w in 
    let txt1 = offset txt 16ul in
    loop st l1 a txt1 (ctr - 1)
  end
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
  push_frame();

  (* Temporary buffers (to be improved) *)
  let state = create 0ul 32ul in (* Chacha inner state *)
  chacha20_init state key counter iv constant;

  (*  Create OTK, using round '0' of Chacha20 *)
  let counter = 0ul in
  let otk   = create 0uy 32ul in (* OTK for Poly (to improve) *)
  chacha20_update otk state 32ul;

  (*  Encryption of the plaintext, using Chacha20, counter at 1 *)
  let counter = 1ul in
  chacha20_encrypt ciphertext key counter iv constant plaintext len;

  (*  MACing of the additional data, the ciphertext and the padding *)
  (* Compute the padding lengths *)
  let max = UInt32.div len 16ul in
  let rem = UInt32.rem len 16ul in
  let max_aad = UInt32.div aad_len 16ul in
  let rem_aad = UInt32.rem aad_len 16ul in
  (* Create padded blocks *)
  let padded_aad = create 0uy 16ul in
  let padded_ciphertext = create 0uy 16ul in
  let len_bytes = create 0uy 16ul in
  blit ciphertext (UInt32.mul max 16ul) padded_ciphertext 0ul rem;
  pad_16 padded_ciphertext rem; // not needed, unless buffer reuse
  blit aad (UInt32.mul max_aad 16ul) padded_aad 0ul rem_aad;
  pad_16 padded_aad rem_aad;    // not needed, unless buffer reuse

  (* Initialize MAC algorithm with one time key *)
  (* encapsulate (r,s) and a; we should probably clear otk *)
  let ak = MAC.coerce root otk in 
  let acc = MAC.start ak in

  (* the log is a sequence of abstract elements that encode the message *)

  (* Update MAC with
     - padded additional data
     - padded ciphertext
     - formatted length *)
  let log = 
    let log = MAC.loop MAC.log_0 aad acc r max_aad in
    (* This is not length-constant time, the lengths are assumed to 
       be public data *)  
    if not(UInt32.eq rem_aad 0ul) then poly1305_update log padded_aad acc r
    else log in
  let aad_ciphertext_log = 
    let log = poly1305_loop aad_log ciphertext acc r max in
    if not(UInt32.eq rem 0ul) then poly1305_update log padded_ciphertext acc r
    else log in
  length_bytes len_bytes len aad_len;
  let full_log = poly1305_update aad_ciphertext_log len_bytes acc r in
  (* Finish MAC *)
  poly1305_finish tag acc (Buffer.sub otk 16ul 16ul);
  pop_frame()

  
