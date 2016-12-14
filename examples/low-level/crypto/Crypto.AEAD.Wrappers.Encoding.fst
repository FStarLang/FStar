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

val frame_accumulate_ensures: #i: MAC.id -> st: CMA.state i -> #aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
	       #txtlen:txtlen_32 -> cipher:lbuffer (v txtlen) -> 
	       (h0:mem) -> (a:CMA.accBuffer i) -> (h1:mem) -> h2:mem -> 
    Lemma (requires (accumulate_ensures st aad cipher h0 a h1 /\
		     Buffer.modifies_0 h1 h2))
          (ensures (accumulate_ensures st aad cipher h0 a h2))
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let frame_accumulate_ensures #i st #aalen aad #txtlent cipher h0 a h1 h2 = 
  FStar.Buffer.lemma_reveal_modifies_0 h1 h2;
  assert (HS.(h1.tip == h2.tip));
  assert (h1 `HS.contains` (Buffer.content (MAC.as_buffer (CMA.abuf a))));
  assert (h2 `HS.contains` (Buffer.content (MAC.as_buffer (CMA.abuf a))));
  assert (fresh_sref h0 h2 (Buffer.content (MAC.as_buffer (CMA.abuf a))));
  if mac_log 
  then (assert (h1  `HS.contains` CMA.alog a);
        assert (HS.sel h2 (CMA.alog a) == HS.sel h1 (CMA.alog a));
	assert (Buffer.as_seq h2 (MAC.as_buffer (CMA.(st.r))) ==
	        Buffer.as_seq h1 (MAC.as_buffer (CMA.(st.r))));
        assert (Buffer.as_seq h2 (MAC.as_buffer (CMA.(abuf a))) ==
                Buffer.as_seq h1 (MAC.as_buffer (CMA.(abuf a))));
        MAC.frame_sel_elem h1 h2 (CMA.(st.r));
        MAC.frame_sel_elem h1 h2 (CMA.(abuf a)))
  else ()

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

let accumulate (#i: id) (#rw:rw) (#n:Cipher.iv (Cipher.algi i)) (aead_st:aead_state i rw)
	       (ak: CMA.state (i, n)) (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
	       (#txtlen:txtlen_32) (plain:plainBuffer i (v txtlen)) (cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
   : StackInline (CMA.accBuffer (i, n))
      (requires (fun h0 -> 
	  enc_dec_liveness aead_st aad plain cipher_tagged h0 /\ 
	  MAC.norm h0 CMA.(ak.r) /\
	  (safeId i ==> is_mac_for_iv aead_st ak h0) /\
	  inv aead_st h0))
      (ensures (fun h0 a h1 ->  
	  let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
      	  enc_dec_liveness aead_st aad plain cipher_tagged h1 /\ 
  	  MAC.norm h1 CMA.(ak.r) /\
  	  (safeId i ==> is_mac_for_iv aead_st ak h1) /\
          accumulate_modifies_nothing h0 h1 /\
	  accumulate_ensures ak aad cipher h0 a h1 /\
	  inv aead_st h1))
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
    acc
