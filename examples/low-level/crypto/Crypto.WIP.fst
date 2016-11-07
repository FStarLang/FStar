module Crypto.WIP

// We implement ideal AEAD on top of ideal Chacha20 and ideal Poly1305. 
// We precisely relate AEAD's log to their underlying state.

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
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2
open Crypto.AEAD

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module CMA = Crypto.Symmetric.UF1CMA
module MAC = Crypto.Symmetric.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain

////////////////////////////////////////////////////////////////////////////////
let maybe_plain (i:id) (l:nat) = if safeId i then Plain.plain i l else unit
let filter_seq (#a:Type) (f:a -> Tot bool) (s:Seq.seq a) : Tot (Seq.seq a) = admit()

let iv_sub_table (#i:id) (#mac_rgn:rid) (tab:Seq.seq (PRF.entry mac_rgn i)) (nonce:Cipher.iv (alg i)) 
  : Tot (Seq.seq (PRF.entry mac_rgn i)) 
  = filter_seq (fun e -> PRF (Entry.x e).iv = nonce) tab
let as_plain (#i:id) (#l:nat) (m:maybe_plain i l{safeId i}) : plain i l = m

let decrypted_up_to (#i:id) (#len:u32) (completed:u32{completed <=^ len}) 
		    (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
		    (h:mem{Buffer.live h (as_buffer pb)}) =
  safeId i ==> 		    
    as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v completed))
    = as_bytes (Plain.slice (as_plain p) 0 (v completed))

let dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) (x:PRF.domain i) 
		   (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let dexor_of_prf_dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) 
				(x:PRF.domain i{ctr_0 i <^ x.ctr}) 
				(pb:plainBuffer i (v len)) (h0:mem) (h1:mem)
   : Lemma (requires (prf_dexor_modifies t x pb h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then ()
     else x_buffer_1_modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

let dexor_modifies_trans (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (y:PRF.domain i{y `above` x})
			 (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) (h2:mem)
   : Lemma (requires (dexor_modifies t x pb h0 h1 /\
		      dexor_modifies t y pb h1 h2))
	   (ensures (dexor_modifies t x pb h0 h2))
   = if not (prf i) || safeId i
     then ()
     else trans_modifies_table_above_x_and_buffer t x y (as_buffer pb) h0 h1 h2

let dexor_modifies_refl (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len)) (h0:mem)
   : Lemma (requires (Buffer.live h0 (as_buffer pb)))
	   (ensures (dexor_modifies t x pb h0 h0))
   = if not (prf i) || safeId i
     then ()
     else refl_modifies_table_above_x_and_buffer t x (as_buffer pb) h0

let dexor_modifies_widen (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len))
			 (from:u32{FStar.Buffer (v from + v (Plain.as_buffer pb).idx) < pow2 n})
			 (len:u32{FStar.Buffer (v len <= length (Plain.as_buffer pb) /\ v from + v len <= length (Plain.as_buffer pb))})
			 (h0:mem) (h1:mem)
   : Lemma (requires (Buffer.live h0 (Plain.as_buffer pb) /\ 
		      dexor_modifies t x (Plain.sub pb from len) h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer (Plain.sub pb from len)) h0 h1;
           Buffer.lemma_intro_modifies_1 (Plain.as_buffer pb) h0 h1)
     else ()

unfold let counter_dexor_requires (i:id) (t:PRF.state i) (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			   (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			   (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			   (plain:plainBuffer i (v len))
			   (cipher:lbuffer (v len))
			   (p:maybe_plain i (v len))
			   (h:mem) =
    let bp = as_buffer plain in
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    let completed_len = len -^ remaining_len in 
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn) /\
    Plain.live h plain /\
    Buffer.live h cipher /\
    (remaining_len <> 0ul ==> FStar.Mul ((v x.ctr - v (offset i)) * v (PRF.blocklen i) = v completed_len)) /\
    // if ciphertexts are authenticated, then the table already includes all we need
    (safeId i ==>
       decrypted_up_to completed_len plain p h /\
       Seq.equal (iv_sub_table (HS.sel h t.table) x.iv) 
		 (counterblocks i t.mac_rgn initial_domain (v len) 0 (v len) p (Buffer.as_seq h cipher)))

let counter_dexor_ensures (i:id) (t:PRF.state i) (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			   (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			   (plain:plainBuffer i (v len))
			   (cipher:lbuffer (v len))
			   (p:maybe_plain i (v len))
			   (h0:mem) (h1:mem) = 
    Plain.live h1 plain /\
    Buffer.live h1 cipher /\
    // in all cases, we extend the table only at x and its successors.
    dexor_modifies t x plain h0 h1 /\
    (safeId i ==> 
       decrypted_up_to len plain p h1 /\
       Seq.equal #(PRF.entry (PRF t.mac_rgn) i) (HS.sel h0 t.table) (HS.sel h1 t.table))

val counter_dexor:
  i:id -> t:PRF.state i -> x:PRF.domain i{PRF.ctr_0 i <^ x.ctr} -> 
  len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)} ->
  remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len} ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len) ->
  p:maybe_plain i (v len) ->
  ST unit (requires (fun h -> counter_dexor_requires i t x len remaining_len plain cipher p h))
 	  (ensures (fun h0 _ h1 -> counter_dexor_ensures i t x len plain cipher p h0 h1))
let rec counter_dexor i t x len remaining_len plain cipher p =
  let completed_len = len -^ remaining_len in
  let h0 = get () in
  if safeId i then ST.recall (itable i t);
  if remaining_len <> 0ul then
    begin // at least one more block
      
      let starting_pos = len -^ remaining_len in
      let l = min remaining_len (PRF.blocklen i) in
      let cipher_hd = Buffer.sub cipher starting_pos l in 
      let plain_hd = Plain.sub plain starting_pos l in 

      assume (contains_cipher_block t x l cipher_hd h0);
      prf_dexor i t x l cipher_hd plain_hd;
      
      let h1 = get() in 
      assume (decrypted_up_to (completed_len +^ l) plain p h1);
      
      let y = PRF.incr i x in
      counter_dexor i t y len (remaining_len -^ l) plain cipher p;

      let h2 = get () in
      dexor_of_prf_dexor_modifies t x plain_hd h0 h1;
      dexor_modifies_widen t x plain starting_pos l h0 h1;
      dexor_modifies_trans t x y plain h0 h1 h2;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h0) h1;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h1) h2
    end
   else dexor_modifies_refl t x plain h0

(*
      // no need to be so specific here --- details follow from the invariant
      let c = Buffer.as_seq h1 (Buffer.sub ciphertext 0ul plainlen) in
      let t: lbuffer 16 = Buffer.as_seq h1 (Buffer.sub ciphertext plainlen (Spec.taglen i)) in
      let a = Buffer.as_seq h1 aadtext in
      let l = field_encode i a c in (
      match PRF.find_0 (HS.sel h1 (PRF.State.table e.prf)) (PRF({iv=n; ctr=0ul})) with
      | Some mac ->
          let log = MAC.ilog (MAC.State.log mac) in
          m_contains log h1 /\ m_sel h1 log == Some (l,t)
      | None -> False))
*)
////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else let r = Buffer.frameOf (Plain.as_buffer pb) in 
         HS.modifies_transitively (as_set [st.log_region; r]) h0 h1 /\
         Buffer.modifies_buf_1 r (Plain.as_buffer pb) h0 h1

let decrypt_ok (i:id) (st:state i Reader) (n:Cipher.iv (alg i))
	       (aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h1:mem) = 
  Buffer.live h1 aad /\
  Buffer.live h1 cipher_tagged /\
  Plain.live h1 plain /\
  (if safeId i then 
    let found = find (HS.sel h1 st.log) n in
    if verified then
      let a = Buffer.as_seq h1 aad in
      let p = Plain.sel_plain h1 plainlen plain in
      let c = Buffer.as_seq h1 cipher_tagged in
      found == Some (Entry n a (v plainlen) p c)
    else
      found == None
  else True)    

let decrypt_requires_sep (i:id) (st:state i Reader) (n:Cipher.iv (alg i))
			 (aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
			 (plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) (plain:plainBuffer i (v plainlen))
			 (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
			 (h:mem) =
    Buffer.live h aad /\
    Plain.live h plain /\
    Buffer.live h cipher_tagged /\
    Buffer.disjoint aad cipher_tagged /\
    Buffer.disjoint (Plain.as_buffer plain) aad /\
    Buffer.disjoint (Plain.as_buffer plain) cipher_tagged /\
    HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region /\
    HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region /\
    HH.disjoint (Buffer.frameOf aad) st.log_region /\
    HS.is_eternal_region st.log_region /\
    HS.is_eternal_region (Buffer.frameOf cipher_tagged) /\
    HS.is_eternal_region (Buffer.frameOf (Plain.as_buffer plain)) /\
    HS.is_eternal_region (Buffer.frameOf aad) /\
    st.log_region <> HH.root /\
    Buffer.frameOf cipher_tagged <> HH.root /\
    Buffer.frameOf aad <> HH.root /\
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root /\
    st.log_region  `HS.is_in` (HS h.h)
    
let frame_myinv_push (#i:id) (#r:rw) (st:state i r) (h:mem) (h1:mem)
   : Lemma (requires (my_inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures (my_inv st h1))
   = if safeId i
     then frame_refines' i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h h1

let prf_mac_when_decrypting (i:id) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
			    (h0:mem) (mac:CMA.state (i,x.iv)) (h1:mem) (mac':CMA.state (i, x.iv)) =
  h0 == h1 /\
  mac == mac' /\ 
  CMA (MAC.norm h1 mac.r) /\
  CMA (Buffer.live h1 mac.s) /\
  CMA (mac_log ==> m_contains (ilog mac.log) h1) /\
  (CMA.authId (i, x.iv) ==> is_Some (m_sel h1 (CMA (ilog mac.log))))

let prf_mac_when_encrypting (i:id{prf i}) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
			    (h0:mem) (mac:CMA.state (i,x.iv)) (h1:mem) =
 let r = itable i t in
 let t0 = HS.sel h0 r in
 let t1 = HS.sel h1 r in
 match find_mac t1 x with 
 | Some mac' -> 
    mac == mac' /\ 
    t1 == SeqProperties.snoc t0 (PRF.Entry x mac) /\
    CMA.genPost0 (i,x.iv) t.mac_rgn h0 mac h1 /\
    HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\
    HS.modifies_ref t.rgn !{HS.as_ref r} h0 h1 /\
    HS.modifies_ref t.mac_rgn TSet.empty h0 h1
 | None -> False

let prf_mac_ensures (i:id) (t:PRF.state i) (k_0: CMA.akey t.mac_rgn i) (x:PRF.domain_mac i)
		    (h0:mem) (mac:CMA.state (i,x.iv)) (h1:mem) = 
    if prf i then
      let r = itable i t in
      let t0 = HS.sel h0 r in
      let t1 = HS.sel h1 r in
      (forall (y:domain i). y <> x ==> PRF.find t0 y == PRF.find t1 y)  /\ //at most modifies t at x
      (match find_mac t0 x with // already in the table? 
       | Some mac' -> 
         prf_mac_when_decrypting i t k_0 x h0 mac h1 mac'
       | None ->  // when encrypting, we get the stateful post of MAC.create             
         prf_mac_when_encrypting i t k_0 x h0 mac h1)
    else 
      CMA.genPost0 (i,x.iv) t.mac_rgn h0 mac h1 /\
      HS.modifies_transitively (Set.singleton t.rgn) h0 h1 /\ //allocates in t.rgn
      HS.modifies_ref t.rgn TSet.empty h0 h1  /\              //but nothing within it is modified
      HS.modifies_ref t.mac_rgn TSet.empty h0 h1

assume val prf_mac_wrapper: 
  i:id -> t:PRF.state i -> k_0: CMA.akey t.mac_rgn i -> x:PRF.domain_mac i -> ST (CMA.state (i,x.iv))
  (requires (fun h0 -> True))
  (ensures (fun h0 mac h1 -> prf_mac_ensures i t k_0 x h0 mac h1))

let decrypt_when_auth (i:id) (n:Cipher.iv (alg i)) (st:state i Reader) (h0:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in
  CMA.authId (i, n) ==> is_Some (find_mac (HS.sel h0 (itable i st.prf)) x0)

val decrypt:
  i:id -> st:state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:UInt32.t {aadlen <=^ aadmax} ->
  aad:lbuffer (v aadlen) ->
  plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
  plain:plainBuffer i (v plainlen) ->
  cipher_tagged:lbuffer (v plainlen + v MAC.taglen)
  -> ST bool
  (requires (fun h ->
    my_inv st h /\
    decrypt_requires_sep i st n aadlen aad plainlen plain cipher_tagged h /\
    decrypt_when_auth i n st h))
  (ensures (fun h0 verified h1 ->
    my_inv st h1 /\
    decrypt_modifies st plain h0 h1 /\
    decrypt_ok i st n aadlen aad plainlen plain cipher_tagged verified h1))

////////////////////////////////////////////////////////////////////////////////
//UF1CMA.verify
////////////////////////////////////////////////////////////////////////////////
let verify_liveness (#i:CMA.id) (st:CMA.state i) (tag:lbuffer 16) (h:mem) =
    Buffer.live h (CMA st.s) /\
    Buffer.live h (CMA (MAC.as_buffer st.r)) /\
    Buffer.live h tag
    
let verify_requires (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) (h0:mem) = 
    let open Crypto.Symmetric.UF1CMA in
    verify_liveness st tag h0 /\
    Buffer.disjoint_2 (MAC.as_buffer acc.a) st.s tag /\ 
    Buffer.disjoint_2 (MAC.as_buffer st.r) st.s tag /\
    acc_inv st acc h0 /\
    (mac_log ==> m_contains (ilog st.log) h0) /\
    (authId i ==> is_Some (m_sel h0 (ilog st.log)))
			     
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
	| None -> False
      else b==verified
    else True
		  
let verify_ensures (#i:CMA.id) (st:CMA.state i) (acc:CMA.accBuffer i) (tag:lbuffer 16) 
		   (h0:mem) (b:bool) (h1:mem) = 
    Buffer.modifies_0 h0 h1 /\
    verify_liveness st tag h1 /\
    verify_ok st acc tag h1 b

assume val verify_wrapper: 
  #i:CMA.id -> 
  st:CMA.state i -> 
  acc:CMA.accBuffer i -> 
  tag:lbuffer 16 -> Stack bool
  (requires (fun h0 -> verify_requires st acc tag h0))
  (ensures (fun h0 b h1 -> verify_ensures st acc tag h0 b h1))

let is_mac_for_iv (#i:id) (#n:Cipher.iv (alg i)) (st:state i Reader{safeId i}) (ak:CMA.state (i, n)) (h:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in 
  match find_mac (HS.sel h (itable i st.prf)) x0 with 
  | Some mac -> ak == mac
  | _ -> False

let decrypt_requires_live (#i:id) (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
 			  (#plainlen:UInt32.t) (plain:plainBuffer i (v plainlen))
 			  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) (h:mem) =
    Buffer.live h aad /\
    Plain.live h plain /\
    Buffer.live h cipher_tagged

let find_entry (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (entry i)) : option (entry i) = 
  SeqProperties.seq_find (fun e -> e.nonce = n) entries

let accumulate_encoded (#i:CMA.id)
 		       (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
		       (#plainlen:txtlen_32) (cipher:lbuffer (v plainlen))
		       (a:CMA.accBuffer i) (h:mem{mac_log}) =
    Buffer.live h aad /\			 
    Buffer.live h cipher /\			     
    h `HS.contains` (CMA.alog a) /\
    HS.sel h (CMA.alog a) ==
    encode_both (fst i) aadlen (Buffer.as_seq h aad) plainlen (Buffer.as_seq h cipher)

let prf_blocks rgn i = Seq.seq (PRF.entry rgn i)
let aead_entries i = Seq.seq (entry i)
let rec find_entry_blocks (#i:id) (#rgn:rid) 
			  (n:Cipher.iv (alg i){safeId i})
			  (entries:aead_entries i)
			  (prf_entries:prf_blocks rgn i)
			  (h:mem{refines h i rgn entries prf_entries /\
			         is_Some (find_mac prf_entries ({iv=n; ctr=ctr_0 i}))})
     : Pure (entry i * prf_blocks rgn i)
	    (requires True)
	    (ensures (fun (entry, blocks) ->
			let x0 = {iv=n; ctr=ctr_0 i} in
			refines_one_entry h entry blocks /\
			find_entry n entries == Some entry /\
			find_mac prf_entries x0 == Some (PRF.macRange rgn i x0 (Seq.index blocks 0).range)))
     = admit()

val entry_exists_if_verify_ok : #i:id -> #n:Cipher.iv (alg i) -> (st:state i Reader) ->
 			        #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
			        #plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			       (plain:Plain.plainBuffer i (v plainlen)) ->
			       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			       (ak:CMA.state (i,n)) ->
			       (acc:CMA.accBuffer (i, n)) ->
			       (tag:lbuffer 16{tag == Buffer.sub cipher_tagged plainlen MAC.taglen}) ->
			       (h:mem{verify_liveness ak tag h /\ 
				      decrypt_requires_live aad plain cipher_tagged h /\
				      safeId i}) ->
    Lemma (requires (my_inv st h /\
		     CMA.acc_inv ak acc h /\
		     accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
		     verify_ok ak acc tag h true /\
		     is_mac_for_iv st ak h))
          (ensures (my_inv st h /\
		    (let entries = HS.sel h st.log in 
		      match find_entry n entries with
		      | None -> False
		      | Some (Entry nonce ad l p c) ->
		        l == v plainlen /\
			ad == Buffer.as_seq h aad /\
			c  == Buffer.as_seq h cipher_tagged)))
let entry_exists_if_verify_ok #i #n st #aadlen aad #plainlen plain cipher_tagged_b ak acc tag_b h =
    let entries = HS.sel h st.log in
    let prf_table = HS.sel h (PRF.itable i st.prf) in
    let x0 = {iv = n; ctr=ctr_0 i} in
    let cipher_tagged = Buffer.as_seq h cipher_tagged_b in
    let cipher, _ = SeqProperties.split cipher_tagged (v plainlen) in
    let tag = Buffer.as_seq h tag_b in
    (* assert (ak == Some.v (find_mac prf_table x0)); //from is_mac_for_iv *)
    (* assert (refines h i st.prf.mac_rgn entries prf_table); //from my_inv *)
    let ( e, blocks ) = find_entry_blocks n entries prf_table h in
    let ak' = PRF.macRange st.prf.mac_rgn i x0 (Seq.index blocks 0).range in
    assert (ak == ak');
    let Entry nonce aad' plainlen' p' cipher_tagged' = e in
    let cipher', _ = SeqProperties.split cipher_tagged' plainlen' in
    let mac_log = CMA.ilog (CMA.State.log ak) in
    match m_sel h mac_log with
    | None           -> ()
    | Some (msg,tag') -> 
      lemma_encode_both_inj i aadlen plainlen (u (Seq.length aad')) (u plainlen')
			     (Buffer.as_seq h aad) cipher aad' cipher';
      assert (Seq.equal tag tag');
      assert (Seq.equal cipher cipher');
      assert (Seq.equal cipher_tagged' (Seq.append cipher' tag'));
      assert (Seq.equal cipher_tagged (Seq.append cipher tag))

////////////////////////////////////////////////////////////////////////////////
//end UF1CMA.verify
////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let decrypted_up_to' (#i:id) (#len:u32) (completed:u32{completed <=^ len}) 
		    (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
		    (h:mem{Buffer.live h (as_buffer pb)}) =
  safeId i ==> 		    
    Seq.equal (as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v completed)))
	      (as_bytes (Plain.slice (as_plain p) 0 (v completed)))

unfold let iv_sub_table_counterblocks (i:id) (t:PRF.state i) (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			       (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			       (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			       (plain:plainBuffer i (v len))
			       (cipher:lbuffer (v len))
			       (p:maybe_plain i (v len))
			       (h:mem) =
    let bp = as_buffer plain in
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    let completed_len = len -^ remaining_len in 
    (safeId i /\ h `HS.contains` (PRF.itable i t) /\ Buffer.live h cipher ==>
       Seq.equal (iv_sub_table (HS.sel h (PRF.itable i t)) x.iv)
		 (counterblocks i t.mac_rgn initial_domain (v len) 0 (v len) p (Buffer.as_seq h cipher)))

let found_entry (#i:id) (n:Cipher.iv (alg i)) (st:state i Reader)
		(#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen)) 
	        (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)})
		(cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		(q:maybe_plain i (v plainlen))
		(h:mem) =
    Buffer.live h cipher_tagged /\
    Buffer.live h aad /\
    safeId i ==> 		
    (let entries = HS.sel h st.log in 		
     match find_entry n entries with
     | None -> False
     | Some (Entry nonce ad l p c) ->
         nonce == n /\
	 ad == Buffer.as_seq h aad /\
	 l  == v plainlen /\
	 c  == Buffer.as_seq h cipher_tagged /\ 
	 p  == as_plain q )

let decrypt_ok' (i:id) (st:state i Reader) (n:Cipher.iv (alg i))
	       (aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
	       (plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (verified:bool) (h1:mem) = 
  Buffer.live h1 aad /\
  Buffer.live h1 cipher_tagged /\
  Plain.live h1 plain /\
  (safeId i /\ verified ==> 
   found_entry #i n st aad cipher_tagged (Plain.sel_plain h1 plainlen plain) h1)


let decrypted_up_to_end (#i:id) (#len:u32) (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
			(h:mem{Buffer.live h (as_buffer pb)})
    : Lemma (requires (decrypted_up_to len pb p h))
	    (ensures (safeId i ==> Plain.sel_plain h len pb == as_plain p))
    = if safeId i then begin
	assert (Seq.equal (Plain.as_bytes (Plain.sel_plain h len pb))
			(Plain.as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v len))));
        assert (Seq.equal (Plain.as_bytes (as_plain p))
	   		  (Plain.as_bytes (Plain.slice (as_plain p) 0 (v len))))
      end

val establish_post_condition: (i:id) -> (st:state i Reader) -> (n:Cipher.iv (alg i)) ->
			     (aadlen:UInt32.t {aadlen <=^ aadmax}) -> (aad:lbuffer (v aadlen)) ->
			     (plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) ->
			     (plain:plainBuffer i (v plainlen)) ->
			     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			     (p:maybe_plain i (v plainlen)) ->
			     (ak:CMA.state (i, n)) ->
			     (acc:CMA.accBuffer (i, n)) ->
			     (verified:bool) -> (h2:mem) -> (h3:mem) -> (h4:mem) ->
   Lemma (requires (let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		     let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
		     let x = PRF.incr i ({iv=n; ctr=ctr_0 i}) in
		     decrypt_requires_sep i st n aadlen aad plainlen plain cipher_tagged h2 /\
		     verify_ensures ak acc tag h2 verified h3 /\
		     HS (is_stack_region h3.tip) /\
		     (safeId i ==> is_mac_for_iv st ak h3) /\
		     (safeId i ==> accumulate_encoded aad #plainlen cipher acc h3) /\
		     my_inv st h3 /\
		     (if verified
		      then (safeId i ==> found_entry n st aad cipher_tagged p h3) /\
			   (* *)
			   counter_dexor_ensures i st.prf x plainlen plain cipher p h3 h4
		      else h3 == h4)))
          (ensures (my_inv st h4 /\
		    decrypt_ok' i st n aadlen aad plainlen plain cipher_tagged verified h4))
let establish_post_condition i st n aadlen aad plainlen plain cipher_tagged p ak acc verified h2 h3 h4 =
  if not verified
  then ()
  else if safeId i || not (prf i)
  then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3 h4;
        if safeId i then begin
	   let entries = HS.sel h3 st.log in 
           let blocks = HS.sel h3 (PRF (itable i st.prf)) in 
	   frame_refines i st.prf.mac_rgn entries blocks h3 h4;
	   decrypted_up_to_end plain p h4
	end)
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3) h4

let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  assume (plainlen <> 0ul); //TODO:add this to the pre-condition
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push st h_init h0;
  let x = PRF({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  //assert (CMA.authId (i, iv) ==> is_Some (find_mac (HS.sel h0 (PRF.itable i st.prf)) x));
  let ak = prf_mac_wrapper i st.prf st.ak x in   // used for keying the one-time MAC
  let h1 = get() in 
  assert (safeId i ==> is_mac_for_iv st ak h1);
  (* assert (CMA.authId (i, iv) ==> is_Some (m_sel h1 (CMA (ilog ak.log)))); *)
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in
  assume(CMA(MAC.norm h1 ak.r));
  // First recompute and check the MAC
  let acc = accumulate_wrapper ak aadlen aad plainlen cipher in
  let h2 = ST.get() in
  assert (safeId i ==> accumulate_encoded aad #plainlen cipher acc h2);
  Buffer.lemma_reveal_modifies_0 h1 h2;
  let verified = verify_wrapper ak acc tag in
  let h3 = ST.get() in
  assume (my_inv st h3); //should get these from framing
  assume (CMA.acc_inv ak acc h3);
  assume (safeId i ==> is_mac_for_iv st ak h3);
  assume (safeId i ==> accumulate_encoded aad #plainlen cipher acc h3);
  // then, safeID i /\ stateful invariant ==>
  //    not verified ==> no entry in the AEAD table
  //    verified ==> exists Entry(iv ad l p c) in AEAD.log
  //                 and correct entries above x in the PRF table
  //                 with matching aad, cipher, and plain
  //
  // not sure what we need to prove for 1st level of PRF idealization
  // possibly that the PRF table with ctr=0 matches the Entry table.
  // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___))
  if verified 
  then begin
    let p : maybe_plain i (v plainlen) = 
	   if safeId i
	   then let _ = entry_exists_if_verify_ok st aad plain cipher_tagged ak acc tag h3 in
	        let entries = !st.log in 
	        let (Some (Entry _nonce _ad _l p _c)) = find_entry iv entries in
		p
	   else () in 
     let y = PRF.incr i x in	   
     assert (decrypted_up_to' 0ul plain p h3); //TODO: revise decrypt_up_to to use Seq.equal and remove this
     assume (iv_sub_table_counterblocks i st.prf y plainlen plainlen plain cipher p h3);
     counter_dexor i st.prf y plainlen plainlen plain cipher p
  end;
  establish_post_condition verified h3 h4
  pop_frame();

  verified
