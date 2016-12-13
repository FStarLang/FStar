module Crypto.AEAD.Decrypt
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
module Dexor       = Crypto.AEAD.EnxorDexor
module PRF_MAC     = Crypto.AEAD.PRF_MAC
module Encoding    = Crypto.AEAD.Encoding   
module EncodingWrapper = Crypto.AEAD.Wrappers.Encoding
module CMAWrapper = Crypto.AEAD.Wrappers.CMA
module PRF_MAC    = Crypto.AEAD.PRF_MAC

////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:aead_state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   Crypto.AEAD.BufferUtils.decrypt_modifies (safeId i) st.log_region (as_buffer pb) h0 h1

let decrypt_ok (#i:id) (n:Cipher.iv (alg i)) (st:aead_state i Reader) 
	       (#aadlen:aadlen) (aad:lbuffer (v aadlen))
	       (#plainlen:txtlen_32)
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h1:mem) = 
  (enc_dec_liveness st aad plain cipher_tagged h1 /\
   verified /\ 
   safeId i) ==> (
   let aead_entries = HS.sel h1 st.log in 
   let aad = Buffer.as_seq h1 aad in
   let plain = Plain.sel_plain h1 plainlen plain in
   let cipher_tagged = Buffer.as_seq h1 cipher_tagged in 
   found_matching_entry n aead_entries #aadlen aad plain cipher_tagged)

val decrypt:
  i:id -> 
  st:aead_state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:aadlen ->
  aad:lbuffer (v aadlen) ->
  plainlen:txtlen_32 {safelen i (v plainlen) (otp_offset i)} ->
  plain:plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
  ST bool
  (requires (fun h ->
    enc_dec_separation st aad plain cipher_tagged /\
    enc_dec_liveness st aad plain cipher_tagged h /\
    inv st h))
  (ensures (fun h0 verified h1 ->
    enc_dec_liveness st aad plain cipher_tagged h1 /\
    inv st h1 /\
    decrypt_modifies st plain h0 h1 /\
    decrypt_ok n st aad plain cipher_tagged verified h1))
#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_inv_push st h_init h0;
  let cipher : lbuffer (v plainlen) = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  let x_0 = PRF.({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = PRF_MAC.prf_mac_dec st st.ak x_0 in   // used for keying the one-time MAC
  let h1 = get() in
(*   assert (prf_mac_modifies i st.prf h0 h1); *)
  assert(CMA.(MAC.norm h1 ak.r));
(* // First recompute and check the MAC *)
  let acc = EncodingWrapper.accumulate ak aad cipher in
  let h2 = get () in
  assert (safeId i ==> CMAWrapper.is_mac_for_iv st ak h2);
  admit()
  
  assume (inv st h2);
  let popt = CMAWrapper.verify st aad plain cipher_tagged ak acc h1 in
  admit()
  
(*   let h2 = ST.get() in *)
(*   assert (safeId i ==> accumulate_encoded aad #plainlen cipher acc h2); *)
(*   Buffer.lemma_reveal_modifies_0 h1 h2; *)
(*   let verified = verify_wrapper ak acc tag in *)
(*   let h3 = ST.get() in *)
(*   Buffer.lemma_reveal_modifies_0 h2 h3; *)
(*   frame_my_inv i st h0 h1 h2 h3; //my_inv st h3 *)
(*   frame_acc #(i, iv) ak #aadlen aad #plainlen cipher h1 acc h2 h3; *)
(*   // then, safeID i /\ stateful invariant ==> *)
(*   //    not verified ==> no entry in the AEAD table *)
(*   //    verified ==> exists Entry(iv ad l p c) in AEAD.log *)
(*   //                 and correct entries above x in the PRF table *)
(*   //                 with matching aad, cipher, and plain *)
(*   // *)
(*   // not sure what we need to prove for 1st level of PRF idealization *)
(*   // possibly that the PRF table with ctr=0 matches the Entry table. *)
(*   // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___)) *)
(*   let p = get_verified_plain st aad plain cipher_tagged ak acc verified in  *)
(*   if verified  *)
(*   then begin *)
(*     let y = PRF.incr i x in	    *)
(*     counter_dexor i st.prf y plainlen plainlen plain cipher p *)
(*   end; *)
(*   let h4 = get() in *)
(*   establish_post_condition st aad plain cipher_tagged p ak acc verified h2 h3 h4; *)
(*   pop_frame(); *)
(*   frame_myinv_pop st h4; *)
(*   frame_decrypt_ok iv st aad plain cipher_tagged verified h4; *)
(*   chain_modification i iv st aad plain cipher_tagged h_init h0 h1 h2 h3 h4; *)
(*   verified *)

