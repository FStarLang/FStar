module Crypto.AEAD.Wrappers.Encoding 

// This file defines the encoding of additional data and ciphertext
// authenticated by the one-time MACs, and their injectivity properties. 

open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open FStar.Math.Lib
open FStar.Math.Lemmas
open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Cipher   = Crypto.Symmetric.Cipher
module PRF      = Crypto.Symmetric.PRF
module PRF_MAC  = Crypto.AEAD.PRF_MAC
open Crypto.AEAD.Encoding
open Crypto.AEAD.Invariant

////////////////////////////////////////////////////////////////////////////////
//AEAD.Encoding.accumulate wrapper
////////////////////////////////////////////////////////////////////////////////
let accumulate_liveness (#i: MAC.id) (st: CMA.state i) 
			(#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
			(#txtlen:txtlen_32) (cipher:lbuffer (v txtlen)) (h:mem) = 
  MAC.norm h CMA.(st.r) /\
  Buffer.live h aad /\ 
  Buffer.live h cipher

// modifies only fresh buffers on the current stack
let accumulate_modifies_nothing h0 h1 = 
  let open HS in
  modifies_one h0.tip h0 h1
  /\ Buffer.modifies_buf_0 h0.tip h0 h1
  /\ h0.tip=h1.tip

let fresh_sref (#a:Type0) h0 h1 (r:HS.reference a) = 
  ~ (h0 `HS.contains` r) /\
    HS.frameOf r == HS.(h1.tip) /\
    h1 `HS.contains` r

let accumulate_ensures (#i: MAC.id) (st: CMA.state i) 
		       (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		       (#txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
		       (h0:mem) (a:CMA.accBuffer i) (h1:mem) =
  let open HS in
  let open CMA in
  accumulate_liveness st aad cipher h1 /\
  fresh_sref h0 h1 (Buffer.content (MAC.as_buffer (abuf a))) /\
  CMA.acc_inv st a h1 /\
  (mac_log ==> 
    fresh_sref h0 h1 (CMA.alog a) /\
    HS.sel h1 (CMA.alog a) == encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher))

unfold let accumulate_ensures' (#i: MAC.id) (st: CMA.state i) 
		       (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		       (#txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
		       (h0:mem) (a:CMA.accBuffer i) (h1:mem) =
  let open HS in
  let open CMA in
  accumulate_liveness st aad cipher h1 /\
  fresh_sref h0 h1 (Buffer.content (MAC.as_buffer (abuf a))) /\
  CMA.acc_inv st a h1 /\
  (mac_log ==> 
    fresh_sref h0 h1 (CMA.alog a) /\
    HS.sel h1 (CMA.alog a) == encode_both (fst i) aadlen (Buffer.as_seq h1 aad) txtlen (Buffer.as_seq h1 cipher))

let ak_acc_tag_separate (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) =
    let open Crypto.Symmetric.UF1CMA in
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) ak.s tag /\
    Buffer.disjoint_2 (MAC.as_buffer ak.r) ak.s tag /\
    Buffer.disjoint ak.s tag

let ak_aad_cipher_separate (#i:CMA.id) (ak:CMA.state i) 
		    (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		    (#n:nat) (cipher:lbuffer n) =
    let open Crypto.Symmetric.UF1CMA in
    Buffer.disjoint_2 (MAC.as_buffer ak.r) aad cipher

let is_iv n (i:id) = UInt128.v n < pow2 (v (8ul *^ Cipher.ivlen (Cipher.algi i)))
let mac_id = i:MAC.id{is_iv (snd i) (fst i)}
let is_ak_for_iv (#i: mac_id) (#rw:rw) (aead_st:aead_state (fst i) rw) (ak:CMA.state i) (h:mem) =
    let j = fst i in
    let n = snd i in
    safeId j ==> is_mac_for_iv #j #rw #n aead_st ak h
    
val accumulate_enc 
	       (#i: mac_id) (#rw:rw) (aead_st:aead_state (fst i) rw)
	       (ak: CMA.state i) (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
	       (#txtlen:txtlen_32) (plain:plainBuffer (fst i) (v txtlen)) 
	       (cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
   : StackInline (CMA.accBuffer i)
      (requires (fun h0 -> 
	  enc_dec_separation aead_st aad plain cipher_tagged /\
	  enc_dec_liveness aead_st aad plain cipher_tagged h0 /\ 
	  ak_aad_cipher_separate ak aad cipher_tagged /\
	  PRF_MAC.ak_live PRF.(aead_st.prf.mac_rgn) ak h0 /\
	  (CMA.authId i ==> CMA.mac_is_unset i PRF.(aead_st.prf.mac_rgn) ak h0)))
	  (* is_ak_for_iv aead_st ak h0)) *)
      (ensures (fun h0 acc h1 ->  
	  let tag : lbuffer (v MAC.taglen) = Buffer.sub cipher_tagged txtlen MAC.taglen in
	  let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
      	  ak_acc_tag_separate ak acc tag /\
	  enc_dec_liveness aead_st aad plain cipher_tagged h1 /\ 
	  PRF_MAC.ak_live PRF.(aead_st.prf.mac_rgn) ak h1 /\
  	  (CMA.authId i ==> CMA.mac_is_unset i PRF.(aead_st.prf.mac_rgn) ak h1) /\
	  (* is_ak_for_iv aead_st ak h1 /\	   *)
	  accumulate_modifies_nothing h0 h1 /\
	  accumulate_ensures ak aad cipher h0 acc h1))
#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let accumulate_enc #i #rw aead_st ak #aadlen aad #txtlen plain cipher_tagged =	  
    let h0 = get () in
    let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
    let acc = accumulate ak aadlen aad txtlen cipher in
    let h1 = get () in
    assume (mac_log ==> fresh_sref h0 h1 (CMA.alog acc));
    assume (fresh_sref h0 h1 (Buffer.content (MAC.as_buffer (CMA.abuf acc))));
    FStar.Buffer.lemma_reveal_modifies_0 h0 h1;
    acc

let accumulate (#i: id) (#rw:rw) (#n:Cipher.iv (Cipher.algi i)) (aead_st:aead_state i rw)
	       (ak: CMA.state (i, n)) (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
	       (#txtlen:txtlen_32) (plain:plainBuffer i (v txtlen)) (cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
   : StackInline (CMA.accBuffer (i, n))
      (requires (fun h0 -> 
	  enc_dec_separation aead_st aad plain cipher_tagged /\
	  enc_dec_liveness aead_st aad plain cipher_tagged h0 /\ 
	  PRF_MAC.ak_live PRF.(aead_st.prf.mac_rgn) ak h0 /\
	  (safeId i ==> is_mac_for_iv aead_st ak h0) /\
	  inv aead_st h0))
      (ensures (fun h0 acc h1 ->  
	  let tag : lbuffer (v MAC.taglen) = Buffer.sub cipher_tagged txtlen MAC.taglen in
	  let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
      	  ak_acc_tag_separate ak acc tag /\
	  enc_dec_liveness aead_st aad plain cipher_tagged h1 /\ 
	  PRF_MAC.ak_live PRF.(aead_st.prf.mac_rgn) ak h1 /\
  	  (safeId i ==> is_mac_for_iv aead_st ak h1) /\
          inv aead_st h1 /\
	  accumulate_modifies_nothing h0 h1 /\
	  accumulate_ensures ak aad cipher h0 acc h1))
  = let h0 = get () in
    let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
    let acc = accumulate #(i, n) ak aadlen aad txtlen cipher in
    let h1 = get () in
    assert (Buffer.disjoint_2 (MAC.as_buffer (CMA.abuf acc)) (CMA.(ak.s)) cipher);
    assume (mac_log ==> fresh_sref h0 h1 (CMA.alog acc)); //NS: this goes away when Encoding.accumulate is restored
    assume (fresh_sref h0 h1 (Buffer.content (MAC.as_buffer (CMA.abuf acc))));
    FStar.Buffer.lemma_reveal_modifies_0 h0 h1;
    frame_inv_modifies_tip aead_st h0 h1;
    assert (accumulate_ensures' ak aad cipher h0 acc h1);
    assume (accumulate_ensures ak aad cipher h0 acc h1); //NS:weirdness, can prove something equivalent up to unfolding
    admit(); //TODO: need to sort this out once Encoding stabilizes
    acc

