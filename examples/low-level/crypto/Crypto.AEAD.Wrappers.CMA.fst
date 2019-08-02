(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Crypto.AEAD.Wrappers.CMA
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.HyperStack.ST
open FStar.Monotonic.RRef

open Crypto.Indexing
open Crypto.Symmetric.Bytes
open Crypto.Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Invariant
open Crypto.AEAD.Encoding

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain
module Invariant = Crypto.AEAD.Invariant
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module ST = FStar.HyperStack.ST
module CMA = Crypto.Symmetric.UF1CMA
module Seq = FStar.Seq
module MAC = Crypto.Symmetric.MAC
module EncodingWrapper = Crypto.AEAD.Wrappers.Encoding
module RR = FStar.Monotonic.RRef
module BufferUtils = Crypto.AEAD.BufferUtils

(*** UF1CMA.mac ***)
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

let mac_requires (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB) (h:mem) =
  let open CMA in
  let open HS in
  EncodingWrapper.ak_acc_tag_separate ak acc tag /\
  verify_liveness ak tag h /\ // liveness of ak.r not needed
  acc_inv ak acc h /\
  (mac_log ==> Buffer.frameOf tag <> (alog acc).id) /\ // also works if they're just disjoint
  (authId i ==> CMA.mac_is_unset i ak.region ak h) // implies MAC.norm m st.r; already in acc_inv

let mac_modifies 
        (i:id) (iv:Cipher.iv (Cipher.algi i))
	(tbuf:lbuffer (v MAC.taglen))
	(ak:CMA.state (i, iv))
	(acc:CMA.accBuffer (i, iv)) 
	(h0 h1:mem) = 
  let open FStar.Buffer in	  
  let abuf = MAC.as_buffer (CMA.abuf acc) in
  if safeMac i 
  then let log = RR.as_hsref CMA.(ilog ak.log) in
       CMA.pairwise_distinct (frameOf abuf) (frameOf tbuf) HS.(log.id) /\
       CMA.modifies_bufs_and_ref abuf tbuf log h0 h1
  else frameOf abuf <> frameOf tbuf /\
       HS.modifies (Set.as_set [frameOf abuf; frameOf tbuf]) h0 h1 /\
       modifies_buf_1 (frameOf abuf) abuf h0 h1 /\
       modifies_buf_1 (frameOf tbuf) tbuf h0 h1

let weaken_mac_modifies         
        (i:id) (iv:Cipher.iv (Cipher.algi i))
	(tbuf:lbuffer (v MAC.taglen))
	(ak:CMA.state (i, iv))
	(acc:CMA.accBuffer (i, iv)) 
	(h0 h1:mem)
   : Lemma (let abuf = MAC.as_buffer (CMA.abuf acc) in
	    Buffer.frameOf abuf = HS.(h0.tip) /\
	    mac_modifies i iv tbuf ak acc h0 h1 ==>
	    BufferUtils.mac_modifies CMA.(ak.region) abuf tbuf h0 h1)
   = ()	    


#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let mac_wrapper (#i:EncodingWrapper.mac_id) (ak:CMA.state i) (acc:CMA.accBuffer i) 
  (tag:MAC.tagB{CMA.pairwise_distinct (Buffer.frameOf (MAC.as_buffer (CMA.abuf acc))) (Buffer.frameOf tag) ak.CMA.region})
  : ST unit
  (requires (fun h0 -> mac_requires ak acc tag h0))
  (ensures (fun h0 _ h1 -> CMA.mac_ensures i ak acc tag h0 h1 /\
		        mac_modifies (fst i) (snd i) tag ak acc h0 h1))
  = let h0 = get () in
    CMA.mac #i ak acc tag;
    let h1 = get () in
    if not (CMA.authId i) then
      Buffer.lemma_reveal_modifies_2 (MAC.as_buffer (CMA.abuf acc)) tag h0 h1

#set-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_is_set_st 
        (#i:id)
        (iv:Cipher.iv (Cipher.algi i))
	(st:aead_state i Writer)
	(#aadlen:aadlen) (aad:lbuffer (v aadlen))
	(#txtlen:txtlen_32) (cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
	(h:mem) =
  Buffer.live h cipher_tagged /\
  Buffer.live h aad /\
  (safeMac i ==> (
     h `HS.contains` (PRF.itable i st.prf) /\ (
     let prf_table = HS.sel h (PRF.itable i st.prf) in
     let ad = Buffer.as_seq h aad in
     let cbuf = Buffer.sub cipher_tagged 0ul txtlen in
     let tbuf = Buffer.sub cipher_tagged txtlen MAC.taglen in
     let cipher : lbytes (v txtlen) = Buffer.as_seq h cbuf in
     let tag : MAC.tag = Buffer.as_seq h tbuf in
     mac_is_set prf_table iv ad (v txtlen) cipher tag h)))

let mac_ensures
        (i:id)
        (iv:Cipher.iv (Cipher.algi i))
	(st:aead_state i Writer)
	(#aadlen:aadlen) (aad:lbuffer (v aadlen))
	(#txtlen:txtlen_32) (plain:plainBuffer i (v txtlen))
	(cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
	(ak:CMA.state (i, iv))
	(acc:CMA.accBuffer (i, iv))
	(h0 h1:mem) =
  let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in	
  enc_dec_liveness st aad plain cipher_tagged h1 /\
  mac_modifies i iv tag ak acc h0 h1 /\
  (safeMac i ==> mac_is_set_st iv st aad cipher_tagged h1)
       

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
val frame_mac_is_set
        (i:id) (iv:Cipher.iv (alg i))
	(st:aead_state i Writer)
	(#aadlen:aadlen) (aad:lbuffer (v aadlen))
	(#txtlen:ok_len_32 i) (plain:plainBuffer i (v txtlen))
	(cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
	(ak:CMA.state (i, iv))
	(acc:CMA.accBuffer (i, iv))
	(h_init:mem)
	(h0:mem)
	(h1:mem)
   : Lemma 
  (requires (
     let open CMA in
     let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
     let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in
     HS.is_stack_region HS.(h0.tip) /\
     enc_dec_separation st aad plain cipher_tagged /\
     enc_dec_liveness st aad plain cipher_tagged h0 /\
     aead_liveness st h0 /\
     EncodingWrapper.ak_acc_tag_separate ak acc tag /\
     EncodingWrapper.accumulate_ensures ak aad cipher h_init acc h0 /\
     mac_modifies i iv tag ak acc h0 h1))
  (ensures (
       (safeMac i /\
        enc_dec_liveness st aad plain cipher_tagged h0 /\
        enc_dec_liveness st aad plain cipher_tagged h1 ==> (
       let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
       let prf = PRF.itable i st.prf in
       let tab0 = HS.sel h0 prf in
       let tab1 = HS.sel h1 prf in      
       let vs0 = HS.sel h0 (CMA.alog acc) in
       let vs1 = HS.sel h1 (CMA.alog acc) in
       let ad0 = Buffer.as_seq h0 aad in
       let ad1 = Buffer.as_seq h1 aad in
       let c0 = Buffer.as_seq h0 cipher in
       let c1 = Buffer.as_seq h1 cipher in
      tab0 == tab1 /\
      vs0 == vs1 /\
      ad0 == ad1 /\
      c0 == c1))))
let frame_mac_is_set i iv st #aadlen aad #txtlen plain cipher_tagged ak acc h_init h0 h1 = ()

val intro_mac_is_set 
        (#i:EncodingWrapper.mac_id)
	(st:aead_state (fst i) Writer)
	(#aadlen:aadlen) (aad:lbuffer (v aadlen))
	(#txtlen:ok_len_32 (fst i)) (plain:plainBuffer (fst i) (v txtlen))
	(cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
	(ak:CMA.state i)
	(acc:CMA.accBuffer i)
	(h_init:mem)
	(h0:mem)
	(h1:mem)
   : Lemma 
  (requires (
     let open CMA in
     let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
     let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in
     HS.is_stack_region HS.(h0.tip) /\
     enc_dec_separation st aad plain cipher_tagged /\
     enc_dec_liveness st aad plain cipher_tagged h0 /\
     enc_dec_liveness st aad plain cipher_tagged h1 /\
     aead_liveness st h0 /\
     EncodingWrapper.ak_acc_tag_separate ak acc tag /\
     EncodingWrapper.accumulate_ensures ak aad cipher h_init acc h0 /\
     verify_liveness ak tag h0 /\
     acc_inv ak acc h0 /\
     ak.region = PRF.(st.prf.mac_rgn) /\
     (CMA.authId i ==> is_mac_for_iv #(fst i) #Writer #(snd i) st ak h0) /\
     CMA.mac_ensures i ak acc tag h0 h1 /\
     mac_modifies (fst i) (snd i) tag ak acc h0 h1))
  (ensures (CMA.authId i ==> mac_is_set_st #(fst i) (snd i) st aad cipher_tagged h1))
let intro_mac_is_set #i st #aadlen aad #txtlen plain cipher_tagged ak acc h_init h0 h1 =
  let open CMA in
  let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
  let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in
  if CMA.authId i then begin
    frame_mac_is_set (fst i) (snd i) st aad plain cipher_tagged ak acc h_init h0 h1;
    let vs_1 = HS.sel h1 (alog acc) in
    let ad1 = Buffer.as_seq h1 aad in
    let c1 = Buffer.as_seq h1 cipher in
    let prf = PRF.itable (fst i) st.prf in
    let tab_1 = HS.sel h1 prf in
    let x_0 = {iv=snd i; ctr=PRF.ctr_0 (fst i)} in
    match PRF.find_mac tab_1 x_0 with
    | None -> ()
    | Some mac_range -> 
      assert (mac_range == ak);
      assert (vs_1 == encode_both (fst i) aadlen ad1 txtlen c1)
  end      

val mac (#i:EncodingWrapper.mac_id)
	(st:aead_state (fst i) Writer)
	(#aadlen:aadlen) (aad:lbuffer (v aadlen))
	(#txtlen:ok_len_32 (fst i)) (plain:plainBuffer (fst i) (v txtlen))
	(cipher_tagged:lbuffer (v txtlen + v MAC.taglen))
	(ak:CMA.state i)
	(acc:CMA.accBuffer i)
	(h_init:mem)
   : ST unit
   (requires (fun h0 ->
     let open CMA in
     let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
     let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in
     HS.is_stack_region HS.(h0.tip) /\
     enc_dec_separation st aad plain cipher_tagged /\
     enc_dec_liveness st aad plain cipher_tagged h0 /\
     EncodingWrapper.ak_acc_tag_separate ak acc tag /\
     EncodingWrapper.accumulate_ensures ak aad cipher h_init acc h0 /\
     verify_liveness ak tag h0 /\
     acc_inv ak acc h0 /\
     ak.region == PRF.(st.prf.mac_rgn) /\
     (CMA.authId i ==> 
       fresh_nonce_st (snd i) st h0 /\
       is_mac_for_iv #(fst i) #Writer #(snd i) st ak h0 /\
       CMA.mac_is_unset i PRF.(st.prf.mac_rgn) ak h0)))
   (ensures (fun h0 _ h1 ->
      (CMA.authId i ==> fresh_nonce_st (snd i) st h1) /\
      mac_ensures (fst i) (snd i) st aad plain cipher_tagged ak acc h0 h1))
let mac #i st #aadlen aad #txtlen plain cipher_tagged ak acc h_init =   
   let tag = Buffer.sub cipher_tagged txtlen MAC.taglen in
   let h0 = get () in
   recall_aead_liveness st;
   mac_wrapper ak acc tag; 
   let h1 = get () in
   //assume (enc_dec_liveness st aad plain cipher_tagged h1);
   intro_mac_is_set st aad plain cipher_tagged ak acc h_init h0 h1


#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
(*** UF1CMA.verify ***)

(*+ The main work of wrapping UF1CMA.verify is to 
    establish that when called with the AEAD.Invariant.inv, 
    if verify returns true for a particular encoded AD+cipher, 
    then in the ideal case, we can also return the plain text
    expected for the result of decryption **)

(*+ found_entry: 
      the entry in the aead table corresponding to nonce n
      contains the expected aad, plain and cipher text
 **)
let found_entry (#i:id) (n:Cipher.iv (Cipher.algi i)) (st:aead_state i Reader)
		(#aadlen:aadlen) (aad:lbuffer (v aadlen)) 
	        (#plainlen:txtlen_32)
		(cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		(q:maybe_plain i (v plainlen))
		(h:mem) =
    (Buffer.live h cipher_tagged /\
     Buffer.live h aad /\
     safeId i) ==> 		
    (let entries = HS.sel h (st_ilog st) in
     found_matching_entry n entries #aadlen
	 (Buffer.as_seq h aad)
	 (as_plain q)
	 (Buffer.as_seq h cipher_tagged))

(*+ verify_liveness: 
	 liveness pre-condition for UF1CMA.verify
  **)	
  
let verify_liveness (#i:CMA.id) (r:rid) (ak:CMA.state i) (tag:lbuffer (v MAC.taglen)) (h:mem) = 
  ak_live CMA.(ak.region) ak h /\
  Buffer.live h tag

(*+ verify_ok: 
	post-condition of verify
	
	Notably, if verify returnes true, then the mac log contains 
	the expected tag
  **)	
let verify_ok (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
	      (h:mem{verify_liveness CMA.(st.region) st tag h})
 	      (b:bool)  = 
    let open Crypto.Symmetric.UF1CMA in
    if mac_log then 
      let log = FStar.HyperStack.sel h (alog acc) in
      let r = MAC.sel_elem h st.r in
      let s = Buffer.as_seq h st.s in
      let m = MAC.mac log r s in
      let verified = Seq.eq m (MAC.sel_word h tag) in
      if authId i then
      	match m_sel h (ilog st.log) with
      	| _, Some(l',m') ->
      	  let correct = m = m' && Seq.eq log l' in
      	  b == (verified && correct)
      	| _, None -> b==false
      else b==verified
    else True

#set-options "--initial_ifuel 0 --max_ifuel 0"
let frame_verify_ok (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		    (h0:mem{verify_liveness CMA.(ak.region) ak tag h0})
		    (h1:mem{verify_liveness CMA.(ak.region) ak tag h1})
 		    (b:bool)
   : Lemma (requires (let open CMA in 
		      verify_ok ak acc tag h0 b /\
		      HS.is_eternal_region ak.region /\
		      HS.is_stack_region (Buffer.frameOf (MAC.as_buffer (abuf acc))) /\
		      CMA.acc_inv ak acc h0 /\
    		      EncodingWrapper.ak_acc_tag_separate ak acc tag /\
		      Buffer.modifies_1 (MAC.as_buffer (abuf acc)) h0 h1))
	   (ensures (verify_ok ak acc tag h1 b))
   = let open CMA in
     FStar.Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (abuf acc)) h0 h1;
     if mac_log then begin
      let log_0 = FStar.HyperStack.sel h0 (alog acc) in
      let log_1 = FStar.HyperStack.sel h1 (alog acc) in      
      assert (log_0 == log_1);
      let r0 = MAC.sel_elem h0 ak.r in
      let r1 = MAC.sel_elem h1 ak.r in      
      assert (MAC.live h0 ak.r);
      assert (Buffer.frameOf (MAC.as_buffer ak.r) == ak.region);
      MAC.frame_sel_elem h0 h1 ak.r;
      assert (r0 == r1)
     end
		 

(*+ accumulate_encoded:
      the post-condition of accumulate ... 
      just a wrapper around encode_both
 **)      
let accumulate_encoded (#i:CMA.id)
 		       (#aadlen:aadlen) (aad:lbuffer (v aadlen))
		       (#plainlen:txtlen_32) (cipher:lbuffer (v plainlen))
		       (a:CMA.accBuffer i) (h:mem) =
   Buffer.live h aad /\			 
   Buffer.live h cipher /\
   (mac_log ==> 
     h `HS.contains` (CMA.alog a) /\
     HS.sel h (CMA.alog a) 
     == encode_both (fst i) aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher))

let acc_inv_weak (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) h : Type0 =
  let open CMA in
  MAC.norm h ak.r /\ 
  (* MAC.norm h (abuf acc) /\ *)
  Buffer.disjoint (MAC.as_buffer ak.r) (MAC.as_buffer (abuf acc)) /\
  (mac_log ==> (
    HS.contains h (alog acc) /\
    Buffer.disjoint_ref_1 (MAC.as_buffer (CMA.abuf acc)) (CMA.alog acc) /\
    Buffer.disjoint_ref_1 (MAC.as_buffer ak.r)  (CMA.alog acc)))

let acc_ensures_weak (#i: MAC.id) (ak: CMA.state i) 
		     (#aadlen:aadlen_32) (aad:lbuffer (v aadlen))
		     (#txtlen:txtlen_32) (cipher:lbuffer (v txtlen))
		     (h0:mem) (acc:CMA.accBuffer i) (h1:mem) =
  let open HS in
  let open CMA in
  EncodingWrapper.fresh_sref h0 h1 (Buffer.content (MAC.as_buffer (abuf acc))) /\
  acc_inv_weak ak acc h1 /\
  accumulate_encoded aad cipher acc h1 /\
  (mac_log ==> EncodingWrapper.fresh_sref h0 h1 (CMA.alog acc))

val frame_accumulate_ensures: #i:CMA.id -> #rw:rw ->
			      aead_st:aead_state (fst i) rw -> 
			      ak:CMA.state i ->
			      #aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
			      #txtlen:txtlen_32 -> plain:plainBuffer (fst i) (v txtlen) ->
			      cipher_tagged:lbuffer (v txtlen + v MAC.taglen) ->
			      h0:mem -> acc:CMA.accBuffer i -> h1:mem -> h2:mem ->
    Lemma (requires (let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
		     enc_dec_separation aead_st aad plain cipher_tagged /\
		     EncodingWrapper.accumulate_ensures ak aad cipher h0 acc h1 /\
		     Buffer.modifies_1 (MAC.as_buffer (CMA.abuf acc)) h1 h2))
          (ensures (let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
		    acc_ensures_weak ak aad cipher h0 acc h2))
let frame_accumulate_ensures #i #rw aead_st ak #aadlen aad #txtlen plain cipher_tagged h0 acc h1 h2 =
  FStar.Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h1 h2;
  let cipher : lbuffer (v txtlen) = Buffer.sub cipher_tagged 0ul txtlen in
  assert (HS.(h1.tip == h2.tip));
  assert (h1 `HS.contains` (Buffer.content (MAC.as_buffer (CMA.abuf acc))));
  assert (h2 `HS.contains` (Buffer.content (MAC.as_buffer (CMA.abuf acc))));
  assert (Buffer.disjoint_2 (MAC.as_buffer (CMA.abuf acc)) aad cipher);
  assert (EncodingWrapper.fresh_sref h0 h2 (Buffer.content (MAC.as_buffer (CMA.abuf acc))));
  if mac_log 
  then (assert (h1  `HS.contains` CMA.alog acc);
        assert (HS.sel h2 (CMA.alog acc) == HS.sel h1 (CMA.alog acc));
	assert (Buffer.as_seq h2 (MAC.as_buffer CMA.(ak.r)) ==
	        Buffer.as_seq h1 (MAC.as_buffer CMA.(ak.r)));
        MAC.frame_sel_elem h1 h2 CMA.(ak.r))

(*+ intro_mac_is_used: 
	if verify returns successfully, then the mac is certainly used
 **)  
val intro_mac_is_used :  #i:id -> #n:Cipher.iv (alg i) -> st:aead_state i Reader ->
 			 #aadlen:aadlen -> aad:lbuffer (v aadlen) ->
			 #plainlen:ok_len_32 i ->
			 plain:Plain.plainBuffer i (v plainlen) ->
			 cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		         ak:CMA.state (i,n) ->
			 acc:CMA.accBuffer (i, n) ->
			 h:mem{safeId i} ->
			 Lemma (requires (let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
					  verify_liveness PRF.(st.prf.mac_rgn) ak tag h /\ 
					  is_mac_for_iv st ak h /\
				          verify_ok ak acc tag h true))
			       (ensures (let prf_table = HS.sel h (PRF.itable i st.prf) in
					 mac_is_used prf_table n h))
#set-options "--initial_ifuel 1 --max_ifuel 1"
let intro_mac_is_used #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc h = ()
#set-options "--initial_ifuel 0 --max_ifuel 0"

(*+ entry_exists_if_verify_ok:
	A key lemma from the invariant and verify succeeding

        It establishes that if verify succeeds on an encoded ad+cipher
	then there is a corresponding entry in the aead_table with the
	ad, cipher and some plaintext 
 **)	
val entry_exists_if_verify_ok : #i:id -> #n:Cipher.iv (alg i) -> (st:aead_state i Reader) ->
 			        #aadlen:aadlen -> aad:lbuffer (v aadlen) ->
			        #plainlen:txtlen_32 {safelen i (v plainlen) (otp_offset i)} ->
			       (plain:Plain.plainBuffer i (v plainlen)) ->
			       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			       (ak:CMA.state (i,n)) ->
			       (acc:CMA.accBuffer (i, n)) ->
			       (tag:lbuffer 16{tag == Buffer.sub cipher_tagged plainlen MAC.taglen}) ->
			       (h:mem{enc_dec_liveness st aad plain cipher_tagged h /\
				      verify_liveness PRF.(st.prf.mac_rgn) ak tag h /\ 
				      safeId i}) ->
   Lemma (requires (inv st h /\
		    acc_inv_weak ak acc h /\
		    accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
		    verify_ok ak acc tag h true /\
		    is_mac_for_iv st ak h))
         (ensures (match find_aead_entry n (HS.sel h (st_ilog st)) with
		   | None -> False
		   | Some (AEADEntry _ _ l p _) ->
		     l == v plainlen /\
		     found_entry n st aad cipher_tagged p h))
#reset-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let entry_exists_if_verify_ok #i #n st #aadlen aad #plainlen plain cipher_tagged_b ak acc tag_b h =
    let aead_entries = HS.sel h (st_ilog st) in
    let prf_table = HS.sel h (PRF.itable i st.prf) in
    let x0 = {iv = n; ctr=ctr_0 i} in
    let cipher_tagged = Buffer.as_seq h cipher_tagged_b in
    let cipher, _ = Seq.split cipher_tagged (v plainlen) in
    let tag = Buffer.as_seq h tag_b in
    intro_mac_is_used st aad plain cipher_tagged_b ak acc h;
    let aead_entry = find_refined_aead_entry n aead_entries prf_table h in 
    let Some ak' = PRF.find_mac prf_table x0 in
    assert (ak == ak');
    let AEADEntry nonce aad' plainlen' p' cipher_tagged' = aead_entry in
    let cipher', _ = Seq.split cipher_tagged' plainlen' in
    let mac_log = CMA.ilog (CMA.State?.log ak) in
    match m_sel h mac_log with
    | _, None           -> ()
    | _, Some (msg,tag') -> 
      lemma_encode_both_inj i aadlen plainlen (u (Seq.length aad')) (u plainlen')
			     (Buffer.as_seq h aad) cipher aad' cipher';
      assert (Seq.equal tag tag');
      assert (Seq.equal cipher cipher');
      assert (Seq.equal cipher_tagged' (Seq.append cipher' tag'));
      assert (Seq.equal cipher_tagged (Seq.append cipher tag))

(*+ get_verified_plain: 
       The main additional work of the UF1CMA.verify wrapper

       In case verify succeeds, we call this function in the ideal
       case to extract the plain text from the aead table and return
       it to decrypt, which in turn uses it to state and establish the
       invariant of counter_dexor
 **)
val get_verified_plain : #i:id -> #n:Cipher.iv (alg i) -> st:aead_state i Reader ->
 			 #aadlen:aadlen -> (aad:lbuffer (v aadlen)) ->
			 #plainlen:txtlen_32 {safelen i (v plainlen) (otp_offset i)} ->
			 plain:Plain.plainBuffer i (v plainlen) ->
			 cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		         ak:CMA.state (i,n) ->
			 acc:CMA.accBuffer (i, n) ->
			 verified:bool ->
      ST (maybe_plain i (v plainlen))
         (requires (fun h -> 
		    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
		    enc_dec_liveness st aad plain cipher_tagged h /\ 
		    (if safeId i && verified
		     then verify_liveness PRF.(st.prf.mac_rgn) ak tag h /\ 
		  	  is_mac_for_iv st ak h /\
			  inv st h /\
			  acc_inv_weak ak acc h /\
			  accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
			  verify_ok ak acc tag h true
	             else True)))
         (ensures (fun h0 p h1 -> 
		    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		    let x1 = {iv=n; ctr=otp_offset i} in
		    h0 == h1 /\
    		    enc_dec_liveness st aad plain cipher_tagged h1 /\ 
		    (if verified && safeId i
		     then prf_contains_all_otp_blocks x1 0 (as_plain p) 
							   (Buffer.as_seq h1 cipher) 
							   (HS.sel h1 (PRF.itable i st.prf)) /\
		          found_entry n st aad cipher_tagged p h1
		     else True)))
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let get_verified_plain #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc verified = 
  if safeId i && verified then
    let h = get () in
    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
    entry_exists_if_verify_ok st aad plain cipher_tagged ak acc tag h;
    let aead_entries = !(st_ilog st) in
    let Some (AEADEntry _nonce _ad _l p _c) = find_aead_entry n aead_entries in
    let _ : unit = 
      let prf_table = HS.sel h (PRF.itable i st.prf) in
      intro_mac_is_used st aad plain cipher_tagged ak acc h;
      let e = find_refined_aead_entry n aead_entries prf_table h in
      () in
    p
  else if safeId i then 
     Plain.load plainlen plain
  else ()

let verify_requires (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) (h0:mem) = 
    EncodingWrapper.ak_acc_tag_separate ak acc tag /\
    verify_liveness CMA.(ak.region) ak tag h0 /\
    CMA.acc_inv ak acc h0 /\
    (mac_log ==> m_contains CMA.(ilog ak.log) h0)

let verify_modifies (#i:CMA.id) (acc:CMA.accBuffer i) (h0:mem) (h1:mem) = 
    Buffer.modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h1
    
let verify_ensures (#i:CMA.id) (ak:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		   (h0:mem) (b:bool) (h1:mem) = 
    verify_modifies acc h0 h1 /\
    verify_liveness CMA.(ak.region) ak tag h1 /\
    verify_ok ak acc tag h1 b

val verify_wrapper: 
  #i:CMA.id -> 
  ak:CMA.state i -> 
  acc:CMA.accBuffer i -> 
  tag:lbuffer 16 -> Stack bool
  (requires (fun h0 -> verify_requires ak acc tag h0))
  (ensures (fun h0 b h1 -> verify_ensures ak acc tag h0 b h1))
let verify_wrapper #i ak acc tag = 
  let h0 = get () in 
  let b = CMA.verify #i ak acc tag in
  let h1 = get() in
  Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h1;
  assert (mac_log ==> m_sel h0 (CMA.(ilog ak.log)) == m_sel h1 (CMA.(ilog ak.log)));
  assert (Buffer.modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h1);
  assert (verify_liveness CMA.(ak.region) ak tag h1);
  frame_verify_ok ak acc tag h0 h1 b;
  b

val verify_ok_nonce_is_used: 
             #i:id -> #n:Cipher.iv (alg i) -> st:aead_state i Reader ->
	     #aadlen:aadlen -> (aad:lbuffer (v aadlen)) ->
 	     #plainlen:txtlen_32 {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
	     plain:Plain.plainBuffer i (v plainlen) ->
	     cipher_tagged:ctagbuf plainlen ->
	     ak:CMA.state (i,n) ->
	     acc:CMA.accBuffer (i, n) ->
	     h:mem{safeMac i} -> 
	Lemma (requires (let tag = ctag cipher_tagged in
			 is_mac_for_iv st ak h /\
			 inv st h /\
			 verify_liveness PRF.(st.prf.mac_rgn) ak tag h /\
			 verify_ok ak acc tag h true))
	      (ensures (~(fresh_nonce n (HS.sel h (st_ilog st)))))
let verify_ok_nonce_is_used #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc h = ()
        
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val verify : #i:id -> #n:Cipher.iv (alg i) -> st:aead_state i Reader ->
	     #aadlen:aadlen -> (aad:lbuffer (v aadlen)) ->
 	     #plainlen:txtlen_32 {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
	     plain:Plain.plainBuffer i (v plainlen) ->
	     cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
	     ak:CMA.state (i,n) ->
	     acc:CMA.accBuffer (i, n) -> h_init:mem ->
      Stack (option (maybe_plain i (v plainlen)))
            (requires (fun h -> 
		    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
		    HS.is_stack_region HS.(h.tip) /\
   		    enc_dec_separation st aad plain cipher_tagged /\ 
		    enc_dec_liveness st aad plain cipher_tagged h /\ 
		    EncodingWrapper.ak_acc_tag_separate ak acc tag /\
		    verify_liveness PRF.(st.prf.mac_rgn) ak tag h /\
		    EncodingWrapper.accumulate_ensures ak aad #plainlen cipher h_init acc h /\
		    inv st h /\
		    (safeMac i ==> is_mac_for_iv st ak h)))
            (ensures (fun h0 popt h1 -> 
		    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		    let x1 = {iv=n; ctr=otp_offset i} in
	            verify_modifies acc h0 h1 /\
    		    enc_dec_liveness st aad plain cipher_tagged h1 /\
    		    inv st h1 /\
    		    acc_ensures_weak ak aad #plainlen cipher h_init acc h1 /\
		    (safeMac i ==> 
			(match popt with 
			 | None -> True
			 | Some p ->
			   let aead_entries = HS.sel h1 (st_ilog st) in
			  ~ (fresh_nonce n aead_entries) /\
                            (safeId i ==> 
			       prf_contains_all_otp_blocks x1 0 
						    (as_plain p)
						    (Buffer.as_seq h1 cipher) 
						    (HS.sel h1 (PRF.itable i st.prf)) /\
  			       found_entry n st aad cipher_tagged p h1)))))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let verify #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc h_init = 
  let open CMA in
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
  if mac_log 
  then m_recall CMA.(ilog ak.log);
  let h0 = get () in
  let b = verify_wrapper ak acc tag in
  let h1 = get () in
  frame_accumulate_ensures #(i,n) st ak aad #plainlen plain cipher_tagged h_init acc h0 h1;
  frame_inv_modifies_1 (MAC.as_buffer (CMA.abuf acc)) st h0 h1;
  Buffer.lemma_reveal_modifies_1 (MAC.as_buffer (CMA.abuf acc)) h0 h1;
  if b 
  then let p = get_verified_plain st aad plain cipher_tagged ak acc true in
       if safeMac i 
       then verify_ok_nonce_is_used st aad plain cipher_tagged ak acc h1;
       Some p
  else None
