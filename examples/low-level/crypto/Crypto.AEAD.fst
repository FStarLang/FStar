module Crypto.AEAD

// Implements agile, conditionally secure Authenticated Encryption
// with Associated Data (AEAD) for TLS 1.2 and 1.3, given secure, 
// agile PRF cipher and UF-1CMA MAC. 

// For the security proof, we maintain a stateful invariant that
// precisely relates the contents of the AEAD log to the states of the
// PRF and the MACs.

// This file intends to match the spec of AEAD0.fst in mitls-fstar. 

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
(* open Crypto.AEAD.Wrappers *)

module HH       = FStar.HyperHeap
module HS       = FStar.HyperStack
module MAC      = Crypto.Symmetric.MAC
module CMA      = Crypto.Symmetric.UF1CMA
module Plain    = Crypto.Plain
module Cipher   = Crypto.Symmetric.Cipher
module PRF      = Crypto.Symmetric.PRF
module Enxor    = Crypto.AEAD.EnxorDexor
module Dexor    = Crypto.AEAD.EnxorDexor
module PRF_MAC  = Crypto.AEAD.PRF_MAC
module Encoding = Crypto.AEAD.Encoding   
	 
val gen: 
  i:id -> 
  rgn:eternal_region -> 
  ST (aead_state i Writer)
     (requires (fun _ -> True))
     (ensures  (fun h0 st h1 -> True))

(** ref_as_aead_log: A coercion from a conditional log to the ideal case *)
let ref_as_aead_log (#r:rgn) (#i:id) (x:rref r (aead_entries i){safeMac i})
  : aead_log r i
  = x

let gen i rgn = 
  let prf = PRF.gen rgn i in 
  if Flag.prf i then recall (PRF.itable i prf);
  let log : aead_log rgn i =
    if safeMac i 
    then ref_as_aead_log (ralloc rgn Seq.createEmpty)
    else () in
  let ak = if CMA.skeyed i then Some (PRF.prf_sk0 #i prf) else None in 
  AEADState #i #Writer #rgn log prf ak

val coerce: 
    i:id{~(prf i)} -> 
    rgn:eternal_region -> 
    key:lbuffer (v (PRF.keylen i)) -> 
    ST (aead_state i Writer)
       (requires (fun h -> Buffer.live h key))
       (ensures  (fun h0 st h1 -> True))
let coerce i rgn key = 
  let prf = PRF.coerce rgn i key in
  if Flag.prf i then recall (PRF.itable i prf);
  let log : aead_log rgn i = () in
  let ak = if CMA.skeyed i then Some (PRF.prf_sk0 #i prf) else None in 
  AEADState #i #Writer #rgn log prf ak

val genReader: #i:id -> st:aead_state i Writer -> ST (aead_state i Reader)
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let genReader #i st =
  AEADState #i #Reader #st.log_region st.log st.prf st.ak

val leak: #i:id{~(prf i)} -> st:aead_state i Writer -> ST (lbuffer (v (PRF.statelen i)))
  (requires (fun _ -> True))
  (ensures  (fun _ _ _ -> True))
let leak #i st = PRF.leak st.prf

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
  i: id -> st:aead_state i Writer ->
  n: Cipher.iv (alg i) ->
  aadlen: aadlen_32 ->
  aad: lbuffer (v aadlen) ->
  plainlen: txtlen_32 {plainlen <> 0ul /\ safelen i (v plainlen) (otp_offset i)} ->
  plain: plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
  ST unit
    (requires (fun h ->
	enc_dec_separation st aad plain cipher_tagged /\
	enc_dec_liveness st aad plain cipher_tagged h /\
	fresh_nonce_st n st h /\
	inv st h))
    (ensures (fun h0 _ h1 ->
	enc_dec_liveness st aad plain cipher_tagged h1 /\
	inv st h1 /\
	encrypt_ensures st n aad plain cipher_tagged h0 h1 /\
	HS.modifies_transitively (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged]) h0 h1))
let encrypt i st n aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame(); 
  let h0 = get () in
  frame_inv_push st h_init h0; //inv st h0

  let cipher : lbuffer (v plainlen) = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  let x_0 = PRF.({iv = n; ctr = ctr_0 i}) in // PRF index to the first block

  //call prf_mac: get a mac key, ak
  let ak = PRF_MAC.prf_mac_wrapper st st.ak x_0 in  // used for keying the one-time MAC
  let h1 = get () in
  assume (CMA.(MAC.norm h1 ak.r));

  assume (Enxor.enxor_liveness st.prf plain cipher h1); //THIS TAKES A LONG TIME TO PROVE
  //call enxor: fragment the plaintext, call the prf, and fill in the cipher text
  Enxor.enxor st.prf n plain cipher;
  let h2 = get () in
 
  assume (CMA.(MAC.norm h2 ak.r));
  assume (Buffer.live h2 aad);
  assume (Buffer.live h2 cipher); //these are provable, but a bit slow
  //call accumulate: encode the ciphertext and additional data for mac'ing 
  (* assume (HS.(is_stack_region h2.tip)); *)
  let acc = Crypto.AEAD.Encoding.accumulate ak aadlen aad plainlen cipher in
  let h3 = get () in
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

////////////////////////////////////////////////////////////////////////////////
//DECRYPT SIDE
////////////////////////////////////////////////////////////////////////////////



////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   Crypto.AEAD.BufferUtils.decrypt_modifies (safeId i) st.log_region (as_buffer pb) h0 h1

let decrypt_ok (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader) 
	       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h1:mem) = 
  Buffer.live h1 aad /\
  Buffer.live h1 cipher_tagged /\
  Plain.live h1 plain /\
  (safeId i /\ verified ==> 
   found_entry n st aad cipher_tagged (Plain.sel_plain h1 plainlen plain) h1)

let decrypt_when_auth (i:id) (n:Cipher.iv (alg i)) (st:state i Reader) (h0:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in
  CMA.authId (i, n) ==> Some? (find_mac (HS.sel h0 (itable i st.prf)) x0)

val establish_post_condition: #i:id -> #n:Cipher.iv (alg i) -> (st:state i Reader) -> 
			      #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
 			      #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			      (plain:plainBuffer i (v plainlen)) ->
			      (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			      (p:maybe_plain i (v plainlen)) ->
			      (ak:CMA.state (i, n)) ->
			      (acc:CMA.accBuffer (i, n)) ->
			      (verified:bool) -> (h2:mem) -> (h3:mem) -> (h4:mem) ->
   Lemma (requires (let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		     let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
		     let x = PRF.incr i ({iv=n; ctr=ctr_0 i}) in
		     decrypt_requires_live st aad plain cipher_tagged h3 /\
		     decrypt_requires_sep st aad plain cipher_tagged /\
		     verify_ensures ak acc tag h2 verified h3 /\
		     HS.(is_stack_region h3.tip) /\
		     (safeId i ==> is_mac_for_iv st ak h3) /\
		     (safeId i ==> accumulate_encoded aad #plainlen cipher acc h3) /\
		     my_inv st h3 /\
		     (if verified
		      then (safeId i ==> found_entry n st aad cipher_tagged p h3) /\
			   counter_dexor_ensures i st.prf x plainlen plain cipher p h3 h4
		      else h3 == h4)))
          (ensures (my_inv st h4 /\
		    decrypt_ok n st aad plain cipher_tagged verified h4))
let establish_post_condition #i #n st #aadlen aad #plainlen plain cipher_tagged p ak acc verified h2 h3 h4 =
  if not verified
  then ()
  else if safeId i || not (prf i)
  then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3 h4;
        if safeId i then begin
	   let entries = HS.sel h3 st.log in 
           let blocks = HS.sel h3 (PRF.(itable i st.prf)) in 
	   frame_refines i st.prf.mac_rgn entries blocks h3 h4;
	   decrypted_up_to_end plain p h4
	end)
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3) h4

let frame_myinv_pop (#i:id) (#r:rw) (st:state i r) (h:mem{HS.poppable h})
   : Lemma (requires (my_inv st h))
	   (ensures (my_inv st (HS.pop h)))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h (HS.pop h)

let frame_decrypt_ok (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader) 
	       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h:mem{HS.poppable h})
   : Lemma (requires (decrypt_requires_sep st aad plain cipher_tagged /\
		      decrypt_requires_live st aad plain cipher_tagged h /\
		      decrypt_ok n st aad plain cipher_tagged verified h))
	   (ensures (decrypt_ok n st aad plain cipher_tagged verified (HS.pop h)))
   = ()	   

#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let prf_mac_modifies (i:id) (t:PRF.state i) (h0:mem) (h1:mem) = 
  Crypto.AEAD.BufferUtils.prf_mac_modifies (safeId i) t.rgn h0 h1

let adapt_dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) (x:PRF.domain i) 
			 (pb:plainBuffer i (v len)) (h0:mem) (h1:mem)
     : Lemma (dexor_modifies t x pb h0 h1
	      ==> Crypto.AEAD.BufferUtils.dexor_modifies (safeId i) t.rgn (as_buffer pb) h0 h1)
     = FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer pb) h0) h1

val chain_modification: (i:id) -> (n:Cipher.iv (alg i)) -> (st:state i Reader) ->
		        #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
		        #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
		       (plain:plainBuffer i (v plainlen)) ->
		       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
		       (h_init:mem) -> (h0:mem) ->(h1:mem)-> (h2:mem) -> (h3:mem) -> (h4:mem) ->
     Lemma (requires
	    (let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
	    decrypt_requires_sep st aad plain cipher_tagged /\
	    decrypt_requires_live st aad plain cipher_tagged h_init /\
	    HS.fresh_frame h_init h0 /\
	    prf_mac_modifies i st.prf h0 h1 /\
	    Buffer.modifies_0 h1 h2 /\
	    Buffer.modifies_0 h2 h3 /\
	    (h3 == h4 \/ dexor_modifies st.prf x1 plain h3 h4)))
	    (ensures (HS.poppable h4 /\
		      decrypt_modifies st plain h_init (HS.pop h4)))
let chain_modification i n st #aadlen aad #plainlen plain cipher_tagged h_init h0 h1 h2 h3 h4 =
    let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
    adapt_dexor_modifies st.prf x1 plain h3 h4;
    Crypto.AEAD.BufferUtils.chain_modification (safeId i) st.log_region (as_buffer plain) h_init h0 h1 h2 h3 h4


val frame_my_inv: (i:id) -> (st:state i Reader) -> (h0:mem) ->(h1:mem)-> (h2:mem) -> (h3:mem) -> 
     Lemma (requires
	    (HS.is_eternal_region st.log_region /\
  	     HS.(st.log_region `is_in` h0.h) /\
 	     HS.(is_stack_region h0.tip) /\
 	     prf_mac_modifies i st.prf h0 h1 /\
	     (prf i ==> h1 `HS.contains` (PRF.itable i st.prf)) /\
	     (h0 == h1 \/ HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h1) /\
	     Buffer.modifies_0 h1 h2 /\
	     Buffer.modifies_0 h2 h3 /\
	     my_inv st h0))
	    (ensures (my_inv st h3))
let frame_my_inv i st h0 h1 h2 h3 = 
  FStar.Buffer.lemma_reveal_modifies_0 h1 h2;
  FStar.Buffer.lemma_reveal_modifies_0 h2 h3;
  if safeId i 
  then frame_refines i st.prf.mac_rgn (HS.sel h0 st.log) (HS.sel h0 (PRF.itable i st.prf)) h0 h3

val frame_acc: #i: MAC.id -> st: CMA.state i -> #aadlen:aadlen_32 -> aad:lbuffer (v aadlen) ->
	       #txtlen:txtlen_32 -> cipher:lbuffer (v txtlen) -> 
	       (h0:mem) -> (a:CMA.accBuffer i) -> (h1:mem) -> h2:mem -> 
    Lemma (requires (accumulate_ensures st aadlen aad txtlen cipher h0 a h1 /\	       
		     Buffer.modifies_0 h1 h2))
          (ensures (accumulate_ensures st aadlen aad txtlen cipher h0 a h2))
let frame_acc #i st #aalen aad #txtlent cipher h0 a h1 h2 = 
  FStar.Buffer.lemma_reveal_modifies_0 h0 h1;
  FStar.Buffer.lemma_reveal_modifies_0 h1 h2;
  FStar.Buffer.lemma_intro_modifies_0 h0 h2;
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

val decrypt:
  i:id -> st:state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:UInt32.t {aadlen <=^ aadmax} ->
  aad:lbuffer (v aadlen) ->
  plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
  plain:plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
  ST bool
  (requires (fun h ->
    decrypt_requires_sep st aad plain cipher_tagged /\
    decrypt_requires_live st aad plain cipher_tagged h /\
    inv st h))
  (ensures (fun h0 verified h1 ->
    inv st h1 /\
    decrypt_requires_live st aad plain cipher_tagged h1 /\
    decrypt_modifies st plain h0 h1 /\
    decrypt_ok n st aad plain cipher_tagged verified h1))
#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push st h_init h0;
  let x = PRF.({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = prf_mac_wrapper i st.prf st.ak x in   // used for keying the one-time MAC
  let h1 = get() in 
  assert (prf_mac_modifies i st.prf h0 h1);
  assert (safeId i ==> is_mac_for_iv st ak h1);
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  assert(CMA.(MAC.norm h1 ak.r));
// First recompute and check the MAC
  let acc = accumulate_wrapper ak aadlen aad plainlen cipher in
  let h2 = ST.get() in
  assert (safeId i ==> accumulate_encoded aad #plainlen cipher acc h2);
  Buffer.lemma_reveal_modifies_0 h1 h2;
  let verified = verify_wrapper ak acc tag in
  let h3 = ST.get() in
  Buffer.lemma_reveal_modifies_0 h2 h3;
  frame_my_inv i st h0 h1 h2 h3; //my_inv st h3
  frame_acc #(i, iv) ak #aadlen aad #plainlen cipher h1 acc h2 h3;
  // then, safeID i /\ stateful invariant ==>
  //    not verified ==> no entry in the AEAD table
  //    verified ==> exists Entry(iv ad l p c) in AEAD.log
  //                 and correct entries above x in the PRF table
  //                 with matching aad, cipher, and plain
  //
  // not sure what we need to prove for 1st level of PRF idealization
  // possibly that the PRF table with ctr=0 matches the Entry table.
  // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___))
  let p = get_verified_plain st aad plain cipher_tagged ak acc verified in 
  if verified 
  then begin
    let y = PRF.incr i x in	   
    counter_dexor i st.prf y plainlen plainlen plain cipher p
  end;
  let h4 = get() in
  establish_post_condition st aad plain cipher_tagged p ak acc verified h2 h3 h4;
  pop_frame();
  frame_myinv_pop st h4;
  frame_decrypt_ok iv st aad plain cipher_tagged verified h4;
  chain_modification i iv st aad plain cipher_tagged h_init h0 h1 h2 h3 h4;
  verified




// Overview of the stateful invariant:
//
// We allocate AEAD logs at the writer (complying with our `local modifier' discipline)
// We allocate all PRF tables in a global private region (to escape that discipline)

// Global state invariant: 
// for all ideal instances of AEAD, 
// - their regions and PRFs tables are pairwise disjoint; and
// - their PRF table contents correctly refines their AEAD logs,
//     (up to early decryptor allocations in initial state)

// This invariant depends only on AEAD-writer regions and the PRF region. 
//
// During AE encrypt, the invariant is eventually restored as we extend the AEAD log, 
// using a precise record of all entries added to the PRF table during encryption.
//
// During AE decrypt, the only interesting case is when early
// verification fails: the invariant is restored for an extended PRF
// state with an extra MAC in its initial state.
//
// For convenience, 'refines' relies on both the log and the table being ordered chronologically.

// TODO `Functional' correctness? (actually a witnessed, stable property)
// c = encryptT h i st nonce ad (real_or_zero i p) 
//
// Ideally, this depends on the (increasing) states of 
// both the PRF and its MACs, and may follow from the global invariant.
//
// Really, this depends on the functional correctness of PRF. 
// Needed: prf_read returning a ghost of the actual underlying block. 
//let sub s start len = Seq.slice start (start+len) s // more convenient? 
