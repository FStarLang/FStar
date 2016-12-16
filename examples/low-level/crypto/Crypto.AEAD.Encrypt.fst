module Crypto.AEAD.Encrypt
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant

module HH       = FStar.HyperHeap
module HS       = FStar.HyperStack
module MAC      = Crypto.Symmetric.MAC
module CMA      = Crypto.Symmetric.UF1CMA
module Plain    = Crypto.Plain
module Cipher   = Crypto.Symmetric.Cipher
module PRF      = Crypto.Symmetric.PRF
module Enxor    = Crypto.AEAD.EnxorDexor
module PRF_MAC     = Crypto.AEAD.PRF_MAC
module Encoding    = Crypto.AEAD.Encoding   
module EncodingWrapper = Crypto.AEAD.Wrappers.Encoding
module CMAWrapper = Crypto.AEAD.Wrappers.CMA

////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let encrypt_ensures  (#i:id) (st:aead_state i Writer)
		     (n: Cipher.iv (alg i))
		     (#aadlen:aadlen)
		     (aad: lbuffer (v aadlen))
		     (#plainlen: UInt32.t)
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h1:mem) = 
    enc_dec_liveness st aad plain cipher_tagged h1 /\
    (safeMac i ==>  (
       let aad = Buffer.as_seq h1 aad in
       let p = Plain.sel_plain h1 plainlen plain in
       let c = Buffer.as_seq h1 cipher_tagged in
       HS.sel h1 st.log == SeqProperties.snoc (HS.sel h0 st.log) (AEADEntry n aad (v plainlen) p c)))
       
val encrypt:
          i: id -> 
 	 st: aead_state i Writer ->
          n: Cipher.iv (alg i) ->
     aadlen: aadlen_32 ->
        aad: lbuffer (v aadlen) ->
   plainlen: txtlen_32 {safelen i (v plainlen) (otp_offset i)} ->
      plain: plainBuffer i (v plainlen) ->
 cipher_tag: lbuffer (v plainlen + v MAC.taglen) ->
        ST  unit
 (requires (fun h ->
	enc_dec_separation st aad plain cipher_tag /\
	enc_dec_liveness st aad plain cipher_tag h /\
	fresh_nonce_st n st h /\
	inv st h))
  (ensures (fun h0 _ h1 ->
	enc_dec_liveness st aad plain cipher_tag h1 /\
	inv st h1 /\
	encrypt_ensures st n aad plain cipher_tag h0 h1 /\
	HS.modifies_transitively (Set.as_set [st.log_region; Buffer.frameOf cipher_tag]) h0 h1))
	
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  assume (plainlen <> 0ul); //TODO: remove this; currently cannot encrypt empty plain texts
  let h_init = get() in
  push_frame(); 
  let h0 = get () in
  frame_inv_push st h_init h0; //inv st h0

  let cipher : lbuffer (v plainlen) = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  let x_0 = PRF.({iv = n; ctr = ctr_0 i}) in // PRF index to the first block

  //call prf_mac: get a mac key, ak
  let ak = PRF_MAC.prf_mac_enc st aad plain cipher_tagged st.ak x_0 in  // used for keying the one-time MAC
  let h1 = get () in

  //call enxor: fragment the plaintext, call the prf, and fill in the cipher text
  Enxor.enxor n st aad plain cipher_tagged;
  let h2 = get () in

  assume (PRF_MAC.ak_live st.prf.mac_rgn ak h2); //provable, but slow

  //call accumulate: encode the ciphertext and additional data for mac'ing 
  let acc = EncodingWrapper.accumulate_enc #(i, n) st ak aad plain cipher_tagged in
  
  let h3 = get () in
  admit()
  
  Buffer.lemma_reveal_modifies_0 h2 h3;
  //call mac: filling in the tag component of the out buffer
  mac_wrapper #(i,n) ak acc tag;
  admit()

(* (\* start: ideal and proof steps, to finish up, notably writing to the AEAD table  *\) *)
(*   finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak acc tag; *)
(* (\* end *\) *)

(*   let h5 = get () in   *)
(*   pop_frame(); //clean up any local allocation on our stack *)
(*   encrypt_ensures_push_pop i st n aadlen aad plainlen plain cipher_tagged h_init h0 h5 *)

