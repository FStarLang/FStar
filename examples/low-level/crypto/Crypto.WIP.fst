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
    Seq.equal (as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v completed)))
	      (as_bytes (Plain.slice (as_plain p) 0 (v completed)))

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

let prf_blocks rgn i = Seq.seq (PRF.entry rgn i)
let aead_entries i = Seq.seq (entry i)

let rec contains_all_cipher_blocks (#i:id) (#r:rid)
				   (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
				   (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
				   (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
				   (cipher:lbytes (v len))
				   (blocks:prf_blocks r i)
				   : GTot Type0 (decreases (v remaining_len))
   = if not (safeId i) || remaining_len = 0ul then 
       True
     else let starting_pos = len -^ remaining_len in
	  let l = min remaining_len (PRF.blocklen i) in
	  let cipher_hd = Seq.slice cipher (v starting_pos) (v starting_pos + v l) in
	  contains_cipher_block (v l) x cipher_hd blocks /\
	  contains_all_cipher_blocks (PRF.incr i x) len (remaining_len -^ l) cipher blocks

#reset-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let counter_dexor_sep (#i:id) (#len:u32)
		      (t:PRF.state i) 
		      (plain:plainBuffer i (v len))
		      (cipher:lbuffer (v len)) = 
    let bp = as_buffer plain in		      
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn)

let counter_dexor_live (#i:id) (#len:u32)
		       (t:PRF.state i) 
 		       (plain:plainBuffer i (v len))
		       (cipher:lbuffer (v len)) (h:mem) =
    Plain.live h plain /\
    Buffer.live h cipher /\
    (prf i ==> h `HS.contains` (itable i t))

let contains_all_cipher_blocks' (#i:id)
 				(x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
				(len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
				(remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
				(cipher:lbuffer (v len))
				(t:PRF.state i)
				(h:mem)
   = safeId i /\ Buffer.live h cipher ==> 				
     contains_all_cipher_blocks x len remaining_len (Buffer.as_seq h cipher) (HS.sel h (PRF.itable i t))
     
let frame_contains_all_cipher_blocks (i:id) 
				     (x_init:PRF.domain i{PRF.ctr_0 i <^ x_init.ctr})
     				     (x:PRF.domain i{x `above` x_init})
				     (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
				     (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
				     (t:PRF.state i) 
				     (pb:plainBuffer i (v len))
				     (cipher: lbuffer (v len))
				     (h0:mem)
    				     (h1:mem)
   : Lemma (requires (counter_dexor_sep t pb cipher  /\
		      counter_dexor_live t pb cipher h0 /\
		      contains_all_cipher_blocks' x len remaining_len cipher t h0 /\
                      prf_dexor_modifies t x_init pb h0 h1))
          (ensures (counter_dexor_live t pb cipher h1 /\
		    contains_all_cipher_blocks' x len remaining_len cipher t h1))
   = FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer pb) h0) h1

let invert_contains_all_cipher_blocks (i:id) 
				      (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
				      (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
				      (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <> 0ul /\ remaining_len <=^ len})
				      (t:PRF.state i) 
 				      (cipher: lbuffer (v len))
				      (h:mem{Buffer.live h cipher})
   : Lemma (requires (contains_all_cipher_blocks' x len remaining_len cipher t h))
 	   (ensures (let starting_pos = len -^ remaining_len in
	             let l = min remaining_len (PRF.blocklen i) in
		     let cipher_hd = Buffer.sub cipher starting_pos l in 
		     safeId i ==> (
		       let blocks = HS.sel h (PRF.itable i t) in
		       let c = Buffer.as_seq h cipher_hd in
		       PRF.contains_cipher_block (v l) x c blocks /\
		       contains_all_cipher_blocks' (PRF.incr i x) len (remaining_len -^ l) cipher t h)))
   = ()
   
#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let counter_dexor_requires (i:id) (t:PRF.state i) (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			   (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
			   (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len})
			   (plain:plainBuffer i (v len))
			   (cipher:lbuffer (v len))
			   (p:maybe_plain i (v len))
			   (h:mem) =
    let bp = as_buffer plain in
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    let completed_len = len -^ remaining_len in 
    counter_dexor_sep t plain cipher /\
    counter_dexor_live t plain cipher h /\
    (remaining_len <> 0ul ==> FStar.Mul ((v x.ctr - v (offset i)) * v (PRF.blocklen i) = v completed_len)) /\
    // if ciphertexts are authenticated, then the table already includes all we need
    contains_all_cipher_blocks' x len remaining_len cipher t h /\
    (safeId i ==> decrypted_up_to completed_len plain p h)
       
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
       Seq.equal (HS.sel h0 (PRF.itable i t)) (HS.sel h1 (PRF.itable i t)))

val counter_dexor:
  i:id -> t:PRF.state i -> x:PRF.domain i{PRF.ctr_0 i <^ x.ctr} -> 
  len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)} ->
  remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len} ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len) ->
  p:maybe_plain i (v len) ->
  ST unit (requires (fun h -> counter_dexor_requires i t x len remaining_len plain cipher p h))
 	  (ensures (fun h0 _ h1 -> counter_dexor_ensures i t x len plain cipher p h0 h1))
#reset-options "--z3timeout 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
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

      invert_contains_all_cipher_blocks i x len remaining_len t cipher h0;
      prf_dexor i t x l cipher_hd plain_hd;
      
      let h1 = get() in 
      let y = PRF.incr i x in
      frame_contains_all_cipher_blocks i x y len (remaining_len -^ l) t plain cipher h0 h1;
      assume (decrypted_up_to (completed_len +^ l) plain p h1);

      counter_dexor i t y len (remaining_len -^ l) plain cipher p;

      let h2 = get () in
      dexor_of_prf_dexor_modifies t x plain_hd h0 h1;
      dexor_modifies_widen t x plain starting_pos l h0 h1;
      dexor_modifies_trans t x y plain h0 h1 h2;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h0) h1;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h1) h2
    end
   else dexor_modifies_refl t x plain h0
////////////////////////////////////////////////////////////////////////////////
//prf_mac
////////////////////////////////////////////////////////////////////////////////
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

////////////////////////////////////////////////////////////////////////////////
//end prf_mac
////////////////////////////////////////////////////////////////////////////////

//TODO: remove this; Crypto.AED.frame_myinv_push is identical now
let frame_myinv_push (#i:id) (#r:rw) (st:state i r) (h:mem) (h1:mem)
   : Lemma (requires (my_inv st h /\ 
		      HS.fresh_frame h h1))
	   (ensures (my_inv st h1))
   = if safeId i
     then frame_refines' i st.prf.mac_rgn (HS.sel h st.log) (HS.sel h (PRF.itable i st.prf)) h h1

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

////////////////////////////////////////////////////////////////////////////////
//decrypt
////////////////////////////////////////////////////////////////////////////////
let decrypt_modifies (#i:id) (#len:u32) (st:state i Reader) (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else let r = Buffer.frameOf (Plain.as_buffer pb) in 
         HS.modifies_transitively (as_set [st.log_region; r]) h0 h1 /\
         Buffer.modifies_buf_1 r (Plain.as_buffer pb) h0 h1

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

let decrypt_requires_live (#i:id) (st:state i Reader) 
			  (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
 			  (#plainlen:UInt32.t) (plain:plainBuffer i (v plainlen))
 			  (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) (h:mem) =
    Buffer.live h aad /\
    Plain.live h plain /\
    Buffer.live h cipher_tagged /\
    st.log_region `HS.is_in` (HS h.h) /\
    (prf i ==> h `HS.contains` (PRF.itable i st.prf))
    
let decrypt_requires_sep (#i:id) (st:state i Reader) 
			 (#aadlen:UInt32.t {aadlen <=^ aadmax}) (aad:lbuffer (v aadlen))
			 (#plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)}) 
			 (plain:plainBuffer i (v plainlen))
			 (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) =
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
    Buffer.frameOf (Plain.as_buffer plain) <> HH.root

let decrypt_when_auth (i:id) (n:Cipher.iv (alg i)) (st:state i Reader) (h0:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in
  CMA.authId (i, n) ==> is_Some (find_mac (HS.sel h0 (itable i st.prf)) x0)

let is_mac_for_iv (#i:id) (#n:Cipher.iv (alg i)) (st:state i Reader{safeId i}) (ak:CMA.state (i, n)) (h:mem) = 
  let x0 = {iv=n; ctr=ctr_0 i} in 
  match find_mac (HS.sel h (itable i st.prf)) x0 with 
  | Some mac -> ak == mac
  | _ -> False

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
			(* let Entry nonce ad l p c = entry in *)
			(* contains_all_cipher_blocks *)
			refines_one_entry h entry blocks /\
			find_entry n entries == Some entry /\
			find_mac prf_entries x0 == Some (PRF.macRange rgn i x0 (Seq.index blocks 0).range)))
     = Crypto.AEAD.Lemmas.Part2.find_entry_blocks i rgn n entries prf_entries h //TODO: duplicate ... remove the indirection


val intro_contains_all_cipher_blocks: (i:id{safeId i}) ->
				      (n:Cipher.iv (alg i)) ->
				      (st:state i Reader) ->
		      		      #aadlen:UInt32.t {aadlen <=^ aadmax} ->
				      (aad:lbuffer (v aadlen)) ->
				      #plainlen:UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
				      (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
				      (q:maybe_plain i (v plainlen)) ->
				      (entry:entry i) ->
				      (blocks: prf_blocks st.prf.mac_rgn i) ->
				      (h:mem{Buffer.live h cipher_tagged}) ->
     Lemma (requires (let aead_entries = HS.sel h st.log in 
		      let prf_entries = HS.sel h (PRF.itable i st.prf) in 
		      let x0 = {iv=n; ctr=ctr_0 i} in
		      refines_one_entry h entry blocks /\
		      find_entry n aead_entries == Some entry /\
		      found_entry n st aad cipher_tagged q h /\
		      (forall (y:domain i{y `above` x0}). PRF.find prf_entries y == PRF.find blocks y)))
           (ensures (let x1 = {iv=n; ctr=ctr_0 i +^ 1ul} in
		     let cipher = Buffer.sub cipher_tagged 0ul plainlen in
		     contains_all_cipher_blocks i x1 plainlen plainlen st.prf cipher h))
#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 1 --max_fuel 1"

let contains_cipher_block' (#i:id) (#r:rid) (#l:nat)
			   (x:domain i{ctr_0 i <^ x.ctr})
			   (cipher:lbytes l)
			   (blocks:prf_blocks r i)
  = if safeId i then
      match find_otp blocks x with
      | Some (OTP l' p c) -> l == v l' /\ c ==  cipher
      | None -> False 
    else True


let rec contains_all_cipher_blocks' (i:id{safeId i})
				    (rgn:region)
				    (x:PRF.domain i{PRF.ctr_0 i <^ ctr x})
				    (len:nat)
				    (from_pos:nat)
				    (to_pos:nat{from_pos <= to_pos /\ to_pos <= len /\ safelen i (to_pos - from_pos) (ctr x)})
				    (cipher:lbytes len)
				    (blocks:prf_blocks rgn i) 
   : GTot Type0 (decreases (to_pos - from_pos)) 
   = 
   let remaining = to_pos - from_pos in 
   if remaining = 0 then 
     True
   else let l = minNat remaining (v (PRF.blocklen i)) in
        let cipher_hd = Seq.slice cipher from_pos (from_pos + l) in
	contains_cipher_block' #i #rgn #l x cipher_hd blocks /\
	contains_all_cipher_blocks' i rgn (PRF.incr i x) len (from_pos + l) to_pos cipher blocks

(* let intro_contains_all_cipher_blocks_from_prime (i:id)  *)
(* 				   (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr}) *)
(* 				   (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)}) *)
(* 				   (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len}) *)
(* 				   (t:PRF.state i)  *)
(* 				   (cipher: lbuffer (v len)) *)
(* 				   (h:mem{Buffer.live h cipher}) *)
(*     : Lemma (requires (let c = Buffer.as_seq h cipher in *)
(* 		       safeId i  ==> ( *)
(* 		       let blocks = HS.sel h (PRF.itable i t) in *)
(* 		       contains_all_cipher_blocks' i t.mac_rgn x (v len) (v (len -^ remaining_len)) (v len) c blocks))) *)
(*             (ensures (contains_all_cipher_blocks i x len remaining_len t cipher h)) *)
(*     = admit() *)
    
		       
(* 				    (rgn:region) *)
(* 				    (x:PRF.domain i{PRF.ctr_0 i <^ ctr x}) *)
(* 				    (len:nat) *)
(* 				    (from_pos:nat) *)
(* 				    (to_pos:nat{from_pos <= to_pos /\ to_pos <= len /\ safelen i (to_pos - from_pos) (ctr x)}) *)
(* 				    (cipher:lbytes len) *)
(* 				    (blocks:prf_blocks rgn i)  *)
(* 				   : GTot Type0 (decreases (v remaining_len)) *)

(* let contains_all_cipher_blocks_remove_prime *)
   
				      
				    
(*   Tot (Seq.seq (PRF.entry rgn i)) // each entry e {PRF(e.x.id = x.iv /\ e.x.ctr >= ctr x)} *)

(* 					(x:PRF.domain i{PRF.ctr_0 i <^ x.ctr}) *)
(* 					(len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)}) *)
(* 					(remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len}) *)
(* 					(t:PRF.state i)  *)
(* 					(cipher: lbuffer (v len)) *)
(* 					(h:mem{Buffer.live h cipher}) *)
(* 				   : GTot Type0 (decreases (v remaining_len)) *)
(*    = if remaining_len = 0ul then  *)
(*        True *)
(*      else let starting_pos = len -^ remaining_len in *)
(* 	  let l = min remaining_len (PRF.blocklen i) in *)
(* 	  let cipher_hd = Buffer.sub cipher starting_pos l in  *)
(* 	  contains_cipher_block t x l cipher_hd h /\ *)
(* 	  contains_all_cipher_blocks i (PRF.incr i x) len (remaining_len -^ l) t cipher h *)


(* let intro_contains_all_cipher_blocks i n st #aadlen aad #plainlen cipher_tagged q entry blocks h = *)
(*   let Entry nonce ad l p c = entry in *)
(*   assume (Buffer.live h aad); *)
(*   assume (Buffer.live h cipher_tagged); *)
(*   assert (nonce == n);  *)
(*   assert (c == Buffer.as_seq h cipher_tagged); *)
(*   let cipher = Buffer.sub cipher_tagged 0ul plainlen in  *)
(*   let c' = Buffer.as_seq h cipher in *)
(*     (\* assert(Seq.equal c' (Seq.slice c 0 (v plainlen))); *\) *)
(*   let x_1 = {iv=n; ctr=ctr_0 i +^ 1ul} in *)
(*   let blocks_tl = SeqProperties.tail blocks in *)
(*   assert (blocks_tl == counterblocks i st.prf.mac_rgn x_1 (v plainlen) 0 (v plainlen) p c'); *)
(*   let l_1 = min plainlen (PRF.blocklen i) in *)
(*   let p_1 = Plain.slice p 0 (v l_1) in *)
(*   let c_1 = Seq.slice c' 0 (v l_1) in *)
(*   (\* assert (SeqProperties.head blocks_tl == PRF.Entry x_1 (PRF.OTP l_1 p_1 c_1)); *\) *)
(*   match find_otp blocks_tl x_1 with  *)
(*   | None -> () *)
(*   | Some (OTP l_1' p_1' c_1') ->  *)
(*     assert (l_1 == l_1' /\ p_1 == p_1' /\ c_1 == c_1'); *)
(*     admit() *)
  
  
(*   admit() *)
  
(*   let Entry nonce *)
(*   admit(); () *)
  


val entry_exists_if_verify_ok : #i:id -> #n:Cipher.iv (alg i) -> (st:state i Reader) ->
 			        #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
			        #plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			       (plain:Plain.plainBuffer i (v plainlen)) ->
			       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) ->
			       (ak:CMA.state (i,n)) ->
			       (acc:CMA.accBuffer (i, n)) ->
			       (tag:lbuffer 16{tag == Buffer.sub cipher_tagged plainlen MAC.taglen}) ->
			       (h:mem{verify_liveness ak tag h /\ 
				      decrypt_requires_live st aad plain cipher_tagged h /\
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
		     | Some (Entry _ _ l p _) ->
		       l == v plainlen /\
		       found_entry n st aad cipher_tagged p h)))
let entry_exists_if_verify_ok #i #n st #aadlen aad #plainlen plain cipher_tagged_b ak acc tag_b h =
    let entries = HS.sel h st.log in
    let prf_table = HS.sel h (PRF.itable i st.prf) in
    let x0 = {iv = n; ctr=ctr_0 i} in
    let cipher_tagged = Buffer.as_seq h cipher_tagged_b in
    let cipher, _ = SeqProperties.split cipher_tagged (v plainlen) in
    let tag = Buffer.as_seq h tag_b in
    let ( e, blocks ) = Crypto.AEAD.Lemmas.Part2.find_entry_blocks n entries prf_table h in
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

val get_verified_plain : #i:id -> #n:Cipher.iv (alg i) -> st:state i Reader ->
 			 #aadlen:UInt32.t {aadlen <=^ aadmax} -> (aad:lbuffer (v aadlen)) ->
			 #plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
			 plain:Plain.plainBuffer i (v plainlen) ->
			 cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		         ak:CMA.state (i,n) ->
			 acc:CMA.accBuffer (i, n) ->
			 verified:bool ->
      ST (maybe_plain i (v plainlen))
         (requires (fun h -> 
		    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
	            decrypt_requires_live st aad plain cipher_tagged h /\ 
		    (if safeId i && verified
		     then verify_liveness ak tag h /\ 
		  	  is_mac_for_iv st ak h /\
			  my_inv st h /\
			  CMA.acc_inv ak acc h /\
			  accumulate_encoded aad #plainlen (Buffer.sub cipher_tagged 0ul plainlen) acc h /\
			  verify_ok ak acc tag h true
	             else True)))
         (ensures (fun h0 p h1 -> 
		    h0 == h1 /\
		    (safeId i /\ verified ==> found_entry n st aad cipher_tagged p h1)))
let get_verified_plain #i #n st #aadlen aad #plainlen plain cipher_tagged ak acc verified = 
  if safeId i && verified then
    let h = get () in
    let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in 
    entry_exists_if_verify_ok st aad plain cipher_tagged ak acc tag h;
    let entries = !st.log in 
    let (Some (Entry _nonce _ad _l p _c)) = find_entry n entries in
    p
  else if safeId i then 
     Plain.load plainlen plain
  else ()


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
		     HS (is_stack_region h3.tip) /\
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
           let blocks = HS.sel h3 (PRF (itable i st.prf)) in 
	   frame_refines i st.prf.mac_rgn entries blocks h3 h4;
	   decrypted_up_to_end plain p h4
	end)
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h3) h4

////////////////////////////////////////////////////////////////////////////////
//end UF1CMA.verify
////////////////////////////////////////////////////////////////////////////////
#reset-options "--z3timeout 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
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
    my_inv st h /\
    decrypt_when_auth i n st h))
  (ensures (fun h0 verified h1 ->
    my_inv st h1 /\
    decrypt_requires_live st aad plain cipher_tagged h1 /\
    decrypt_modifies st plain h0 h1 /\
    decrypt_ok n st aad plain cipher_tagged verified h1))


  
let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  let h_init = get() in
  push_frame();
  let h0 = get () in
  frame_myinv_push st h_init h0;
  let x = PRF({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  //assert (CMA.authId (i, iv) ==> is_Some (find_mac (HS.sel h0 (PRF.itable i st.prf)) x));
  let ak = prf_mac_wrapper i st.prf st.ak x in   // used for keying the one-time MAC
  let h1 = get() in 
  assert (safeId i ==> is_mac_for_iv st ak h1);
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
  let p = get_verified_plain st aad plain cipher_tagged ak acc verified in 
  if verified 
  then begin
    let y = PRF.incr i x in	   
    assume (contains_all_cipher_blocks i y plainlen plainlen st.prf cipher h3);
    counter_dexor i st.prf y plainlen plainlen plain cipher p
  end;
  let h4 = get() in
  establish_post_condition st aad plain cipher_tagged p ak acc verified h2 h3 h4;
  assert (my_inv st h4);
  assert (decrypt_ok iv st aad plain cipher_tagged verified h4);
  assume false;
  pop_frame();
  verified
