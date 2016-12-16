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

assume //NS: boring, this should be in the buffer library
val to_seq_temp: #a:Type -> b:Buffer.buffer a -> l:UInt32.t{v l <= Buffer.length b} -> ST (Seq.seq a)
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h1 b /\ r == Buffer.as_seq h1 b))

#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let ideal_ensures
	 (#i: id)
 	 (st: aead_state i Writer)
          (n: Cipher.iv (alg i))
    (#aadlen: aadlen_32)
        (aad: lbuffer (v aadlen))
  (#plainlen: txtlen_32)
      (plain: plainBuffer i (v plainlen))
  (cipher_tag: lbuffer (v plainlen + v MAC.taglen){safeMac i})
       (h0 h1: mem) = 
    enc_dec_liveness st aad plain cipher_tag h0 /\
    enc_dec_liveness st aad plain cipher_tag h1 /\
    HS.modifies (Set.as_set [st.log_region]) h0 h1 /\
    HS.modifies_ref st.log_region (TSet.singleton (HS.as_aref (st_ilog st))) h0 h1 /\ (
    let entry = AEADEntry n (Buffer.as_seq h0 aad) 
 			    (v plainlen)
			    (Plain.sel_plain h0 plainlen plain)
			    (Buffer.as_seq h0 cipher_tag) in
    let log = st_ilog st in 				      
    HS.sel h1 log == SeqProperties.snoc (HS.sel h0 log) entry)

val do_ideal:
	 #i: id -> 
 	 st: aead_state i Writer ->
          n: Cipher.iv (alg i) ->
    #aadlen: aadlen_32 ->
        aad: lbuffer (v aadlen) ->
  #plainlen: txtlen_32 ->
      plain: plainBuffer i (v plainlen) ->
 cipher_tag: lbuffer (v plainlen + v MAC.taglen){safeMac i} ->
         ST  unit
 (requires (fun h -> 
	    enc_dec_liveness st aad plain cipher_tag h))
 (ensures  (fun h0 _ h1 ->
	    ideal_ensures st n aad plain cipher_tag h0 h1))
let do_ideal #i st n #aadlen aad #plainlen plain cipher_tag =
    let ad = to_seq_temp aad aadlen in
    let p = Plain.load plainlen plain in 
    let c_tagged = to_seq_temp cipher_tag plainlen in
    let entry = AEADEntry n ad (v plainlen) p c_tagged in
    FStar.ST.recall (st_ilog st);
    st_ilog st := SeqProperties.snoc !(st_ilog st) entry


assume val reestablish_inv:
          i: id -> 
         st: aead_state i Writer ->
          n: Cipher.iv (alg i) ->
    #aadlen: aadlen_32 ->
        aad: lbuffer (v aadlen) ->
  #plainlen: txtlen_32 {safelen i (v plainlen) (otp_offset i)} ->
      plain: plainBuffer i (v plainlen) ->
 cipher_tag: lbuffer (v plainlen + v MAC.taglen) ->
         ak: CMA.state (i, n) -> 
        acc: CMA.accBuffer (i, n) ->
         h0: mem ->
         h1: mem ->
         h2: mem ->
         h3: mem ->       
         h4: mem ->               
      Lemma 
  (requires  (let cipher : lbuffer (v plainlen) = Buffer.sub cipher_tag 0ul plainlen in
              let x_1 = {iv=n; ctr=otp_offset i} in
              enc_dec_separation st aad plain cipher_tag  /\
              enc_dec_liveness st aad plain cipher_tag h0 /\
              enc_dec_liveness st aad plain cipher_tag h1 /\
              enc_dec_liveness st aad plain cipher_tag h2 /\
              enc_dec_liveness st aad plain cipher_tag h3 /\
	      HS.(is_stack_region h0.tip) /\ //TODO: need to add that the buffers of acc live in h0.tip
              inv st h0 /\
	      (safeMac i ==> is_mac_for_iv st ak h0) /\
              Enxor.enxor_invariant st.prf x_1 plainlen plainlen plain cipher h0 h1 /\
              Enxor.modifies_table_above_x_and_buffer st.prf x_1 cipher h0 h1 /\
              EncodingWrapper.accumulate_modifies_nothing h1 h2 /\
              CMAWrapper.mac_ensures i n st aad plain cipher_tag ak acc h2 h3 /\ (
              if safeMac i
              then ideal_ensures st n aad plain cipher_tag h3 h4
              else h3 == h4)))
  (ensures    (inv st h4))

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
  let h00 = get () in
  frame_inv_push st h_init h00; //inv st h0

  let cipher : lbuffer (v plainlen) = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  let x_0 = PRF.({iv = n; ctr = ctr_0 i}) in // PRF index to the first block

  //call prf_mac: get a mac key, ak
  let ak = PRF_MAC.prf_mac_enc st aad plain cipher_tagged st.ak x_0 in  // used for keying the one-time MAC
  let h0 = get () in
  let open CMA in 
  
  //call enxor: fragment the plaintext, call the prf, and fill in the cipher text
  Enxor.enxor n st aad plain cipher_tagged ak;
  let h1 = get () in

  (* assume (EncodingWrapper.ak_aad_cipher_separate ak aad cipher_tagged); //slow *)

  //call accumulate: encode the ciphertext and additional data for mac'ing
  let acc = EncodingWrapper.accumulate_enc #(i, n) st ak aad plain cipher_tagged in
  
  let h2 = get () in

  (* assume(verify_liveness ak tag h2); //slow *)

  //call mac: filling in the tag component of the out buffer
  CMAWrapper.mac #(i,n) st aad plain cipher_tagged ak acc h1;
  let h3 = get () in 
  
  if safeMac i 
  then do_ideal st n aad plain cipher_tagged;
  let h4 = get () in
  let x_1 = PRF.incr i x_0 in
  reestablish_inv i st n aad plain cipher_tagged ak acc h0 h1 h2 h3 h4;
  admit()
