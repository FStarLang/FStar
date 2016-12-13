module Crypto.AEAD.Wrappers.CMA
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
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
module CMA = Crypto.Symmetric.UF1CMA
module SeqProperties = FStar.SeqProperties
module MAC = Crypto.Symmetric.MAC
module EncodingWrapper = Crypto.AEAD.Wrappers.Encoding

(*** UF1CMA.mac ***)
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let mac_ensures (i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
		(h0:mem) (h1:mem) = 
    let open FStar.Buffer in
    let open Crypto.Symmetric.Bytes in
    let open Crypto.Symmetric.Poly1305 in
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 st.s /\ 
    MAC.live h0 st.r /\ 
    Buffer.live h1 tag /\
    CMA.acc_inv st acc h0 /\ (
    if mac_log then
      HS.modifies (Set.as_set [st.region; Buffer.frameOf tag]) h0 h1 /\
      Buffer.modifies_buf_1 (Buffer.frameOf tag) tag h0 h1 /\
      HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1 /\
      m_contains (ilog st.log) h1 /\ (
      let log = FStar.HyperStack.sel h1 (alog acc) in
      let a = MAC.sel_elem h1 (abuf acc) in
      let r = MAC.sel_elem h1 st.r in
      let s = Buffer.as_seq h1 st.s in
      let t = MAC.mac log r s in
      sel_word h1 tag === t /\
      m_sel h1 (ilog st.log) == Some(log,t))
    else Buffer.modifies_1 tag h0 h1)

let mac_wrapper (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:MAC.tagB)
  : ST unit
  (requires (fun h0 ->
    let open Crypto.Symmetric.UF1CMA in
    Buffer.live h0 tag /\ 
    Buffer.live h0 st.s /\
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag /\
    Buffer.disjoint (MAC.as_buffer st.r) tag /\
    Buffer.disjoint st.s tag /\ 
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (mac_log /\ authId i ==> m_sel h0 (ilog st.log) == None)))
  (ensures (fun h0 _ h1 -> mac_ensures i st acc tag h0 h1))
  = let open Crypto.Symmetric.UF1CMA in
    let h0 = get () in
    CMA.mac #i st acc tag;
    let h1 = get () in 
    if mac_log then begin
      (* Need to update UF1CMA to prove this (problem with the mods clause not working fully) *)
      assume (HS.modifies_ref st.region !{HS.as_ref (as_hsref (ilog st.log))} h0 h1) //NS: this goes away when UF1CMA is done
    end

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
    (let entries = HS.sel h st.log in 		
     found_matching_entry n entries #aadlen
	 (Buffer.as_seq h aad)
	 (as_plain q)
	 (Buffer.as_seq h cipher_tagged))

(*+ verify_liveness: 
	liveness pre-condition for calling UF1CMA.verify **)
let verify_liveness (#i:CMA.id) (st:CMA.state i) (tag:lbuffer 16) (h:mem) =
    Buffer.live h (CMA.(st.s)) /\
    Buffer.live h (CMA.(MAC.as_buffer st.r)) /\
    Buffer.live h tag

(*+ verify_ok: 
	post-condition of verify
	
	Notably, if verify returnes true, then the mac log contains 
	the expected tag
  **)	
let verify_ok (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		     (h:mem{verify_liveness st tag h}) (b:bool)  = 
    let open Crypto.Symmetric.UF1CMA in
    if mac_log then 
      let log = FStar.HyperStack.sel h (alog acc) in
      let r = MAC.sel_elem h st.r in
      let s = Buffer.as_seq h st.s in
      let m = MAC.mac log r s in
      let verified = Seq.eq m (MAC.sel_word h tag) in
      if authId i then
      	match m_sel h (ilog st.log) with
      	| Some(l',m') ->
      	  let correct = m = m' && Seq.eq log l' in
      	  b == (verified && correct)
      	| None -> b==false
      else b==verified
    else True

(*+ is_mac_for_iv:
	ak being indexed for (i, n)

	really corresponds to the ak being the stored mac in the prf table for n
 **)
let is_mac_for_iv (#i:id) (#n:Cipher.iv (alg i)) (st:aead_state i Reader{safeId i}) (ak:CMA.state (i, n)) (h:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in 
  match find_mac (HS.sel h (itable i st.prf)) x0 with 
  | Some mac -> ak == mac
  | _ -> False

(*+ accumulate_encoded:
      the post-condition of accumulate ... 
      just a wrapper around encode_both
 **)      
let accumulate_encoded (#i:CMA.id)
 		       (#aadlen:aadlen) (aad:lbuffer (v aadlen))
		       (#plainlen:txtlen_32) (cipher:lbuffer (v plainlen))
		       (a:CMA.accBuffer i) (h:mem{mac_log}) =
    Buffer.live h aad /\			 
    Buffer.live h cipher /\			     
    h `HS.contains` (CMA.alog a) /\
    HS.sel h (CMA.alog a) ==
    encode_both (fst i) aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher)

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
				      verify_liveness ak tag h /\ 
				      safeId i}) ->
   Lemma (requires (inv st h /\
		    CMA.acc_inv ak acc h /\
		    accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
		    verify_ok ak acc tag h true /\
		    is_mac_for_iv st ak h))
         (ensures (match find_aead_entry n (HS.sel h st.log) with
		   | None -> False
		   | Some (AEADEntry _ _ l p _) ->
		     l == v plainlen /\
		     found_entry n st aad cipher_tagged p h))
#reset-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 0 --max_fuel 0 --z3rlimit 400"
let entry_exists_if_verify_ok #i #n st #aadlen aad #plainlen plain cipher_tagged_b ak acc tag_b h =
    let aead_entries = HS.sel h st.log in
    let prf_table = HS.sel h (PRF.itable i st.prf) in
    let x0 = {iv = n; ctr=ctr_0 i} in
    let cipher_tagged = Buffer.as_seq h cipher_tagged_b in
    let cipher, _ = SeqProperties.split cipher_tagged (v plainlen) in
    let tag = Buffer.as_seq h tag_b in
    let aead_entry = find_refined_aead_entry n aead_entries prf_table h in 
    let Some ak' = PRF.find_mac prf_table x0 in
    assert (ak == ak');
    let AEADEntry nonce aad' plainlen' p' cipher_tagged' = aead_entry in
    let cipher', _ = SeqProperties.split cipher_tagged' plainlen' in
    let mac_log = CMA.ilog (CMA.State?.log ak) in
    match m_sel h mac_log with
    | None           -> ()
    | Some (msg,tag') -> 
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
		     then verify_liveness ak tag h /\ 
		  	  is_mac_for_iv st ak h /\
			  inv st h /\
			  CMA.acc_inv ak acc h /\
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
    let aead_entries = !st.log in 
    let Some (AEADEntry _nonce _ad _l p _c) = find_aead_entry n aead_entries in
    let _ : unit = 
      let prf_table = HS.sel h (PRF.itable i st.prf) in
      let e = find_refined_aead_entry n aead_entries prf_table h in
      () in
    p
  else if safeId i then 
     Plain.load plainlen plain
  else ()

let verify_separation (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) =
    let open Crypto.Symmetric.UF1CMA in
    Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) st.s tag /\
    Buffer.disjoint_2 (MAC.as_buffer st.r) st.s tag

let verify_requires (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) (h0:mem) = 
    let open Crypto.Symmetric.UF1CMA in
    verify_separation st acc tag /\
    verify_liveness st tag h0 /\
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0)(*  /\ *)
    (* (authId i ==> Some? (m_sel h0 (ilog st.log))) *)

let verify_ensures (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		   (h0:mem) (b:bool) (h1:mem) = 
    Buffer.modifies_0 h0 h1 /\
    verify_liveness st tag h1 /\
    verify_ok st acc tag h1 b

val verify_wrapper: 
  #i:CMA.id -> 
  st:CMA.state i -> 
  acc:CMA.accBuffer i -> 
  tag:lbuffer 16 -> Stack bool
  (requires (fun h0 -> verify_requires st acc tag h0))
  (ensures (fun h0 b h1 -> verify_ensures st acc tag h0 b h1))
#reset-options "--z3rlimit 40 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let verify_wrapper #i st acc tag = 
  let h0 = get () in 
  assume (CMA.authId i ==> Some? (m_sel h0 (CMA.(ilog st.log)))); //TODO: can't prove this in Plan A
  let b = CMA.verify #i st acc tag in
  let h1 = get() in
  Buffer.lemma_reveal_modifies_0 h0 h1;
  assert (mac_log ==> m_sel h0 (CMA.(ilog st.log)) == m_sel h1 (CMA.(ilog st.log)));
  b

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
		    enc_dec_liveness st aad plain cipher_tagged h /\ 
		    verify_separation ak acc tag /\
		    verify_liveness ak tag h /\
		    EncodingWrapper.accumulate_ensures ak aad #plainlen cipher h_init acc h /\
		    inv st h /\
		    (safeId i ==> is_mac_for_iv st ak h)))
            (ensures (fun h0 popt h1 -> 
		    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		    let x1 = {iv=n; ctr=otp_offset i} in
	            Buffer.modifies_0 h0 h1 /\
    		    enc_dec_liveness st aad plain cipher_tagged h1 /\
    		    EncodingWrapper.accumulate_ensures ak aad #plainlen cipher h_init acc h1 /\
		    (safeId i ==> 
			(match popt with 
			 | None -> True
			 | Some p ->
			   prf_contains_all_otp_blocks x1 0 
						    (as_plain p)
						    (Buffer.as_seq h1 cipher) 
						    (HS.sel h1 (PRF.itable i st.prf)) /\
  		           found_entry n st aad cipher_tagged p h1))))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let verify #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc h_init = 
  let open CMA in
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
  (* assume (Buffer.disjoint_2 (MAC.as_buffer (abuf acc)) ak.s tag /\ *)
  (* 	  Buffer.disjoint_2 (MAC.as_buffer ak.r) ak.s tag); *)
  if mac_log 
  then m_recall CMA.(ilog ak.log);
  let h0 = get () in
  let b = verify_wrapper ak acc tag in
  let h1 = get () in
  EncodingWrapper.frame_accumulate_ensures ak aad #plainlen cipher h_init acc h0 h1;
  frame_inv_modifies_0 st h0 h1;
  Buffer.lemma_reveal_modifies_0 h0 h1;
  if b 
  then let p = get_verified_plain st aad plain cipher_tagged ak acc true in
       Some p
  else None
