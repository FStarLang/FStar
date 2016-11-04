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
open Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant
open Crypto.AEAD.Lemmas
open Crypto.AEAD.Lemmas.Part2
open Crypto.AEAD

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF


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
val counter_dexor:
  i:id -> t:PRF.state i -> x:PRF.domain i{PRF.ctr_0 i <^ x.ctr} -> 
  len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)} ->
  remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len} ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len)
  { let bp = as_buffer plain in
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF t.rgn) /\
    Buffer.frameOf cipher <> (PRF t.rgn)
  } ->
  p:maybe_plain i (v len) ->
  ST unit
  (requires (fun h ->
    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
    let completed_len = len -^ remaining_len in 
    Plain.live h plain /\
    Buffer.live h cipher /\
    (remaining_len <> 0ul ==> FStar.Mul ((v x.ctr - v (offset i)) * v (PRF.blocklen i) = v completed_len)) /\
    // if ciphertexts are authenticated, then the table already includes all we need
    (safeId i ==>
      (let expected = counterblocks i t.mac_rgn initial_domain (v len) 0 (v len) p (Buffer.as_seq h cipher) in
       decrypted_up_to completed_len plain p h /\
       Seq.equal (iv_sub_table (HS.sel h t.table) x.iv) expected))
    ))
  (ensures (fun h0 _ h1 ->
    Plain.live h1 plain /\
    Buffer.live h1 cipher /\
    // in all cases, we extend the table only at x and its successors.
    dexor_modifies t x plain h0 h1 /\
    (safeId i ==> 
       decrypted_up_to len plain p h1 /\
       Seq.equal #(PRF.entry (PRF t.mac_rgn) i) (HS.sel h0 t.table) (HS.sel h1 t.table))))

let contains_cipher_block (#i:id) 
			  (t:PRF.state i) 
			  (x:PRF.domain i{ctr_0 i <^ x.ctr})
			  (l:u32{ l <=^ blocklen i})
			  (cipher:lbuffer (v l))
			  (h:mem{Buffer.live h cipher})
  = if safeId i then 
      match find_otp (HS.sel h (itable i t)) x with
      | Some (OTP l' p c) -> l == l' /\ c == sel_bytes h l cipher
      | None -> False 
    else True

unfold let prf_dexor_requires (i:id) (t:PRF.state i) (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			      (l:u32 {l <=^ blocklen i})
     			      (cipher:lbuffer (v l)) 
			      (plain:plainBuffer i (v l))
			      (h0:mem) = 
   Buffer.disjoint (as_buffer plain) cipher /\
   Buffer.frameOf (as_buffer plain) <> t.rgn /\
   Buffer.frameOf cipher <> t.rgn /\
   Plain.live h0 plain /\ 
   Buffer.live h0 cipher /\ 
   contains_cipher_block t x l cipher h0 

let prf_dexor_ensures (i:id) (t:PRF.state i) (x:domain i{ctr_0 i <^ x.ctr}) 
		      (l:u32 {l <=^ blocklen i})
     		      (cipher:lbuffer (v l)) 
		      (plain:plainBuffer i (v l))
		      (h0:mem) (h1:mem) = 
   let pb = as_buffer plain in 
   Plain.live h1 plain /\ 
   Buffer.live h1 cipher /\
   dexor_modifies t x plain h0 h1 /\
   (safeId i ==>
     (let r = PRF.itable i t in
      match find_otp (HS.sel h1 r) x with
      | Some (OTP l' p c) -> l == l' /\ p == sel_plain h1 l plain /\ Buffer.modifies_1 pb h0 h1
      | None -> False ))

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

assume val prf_dexor: 
  i:id -> t:PRF.state i -> x:domain i{ctr_0 i <^ x.ctr} -> l:u32 {l <=^ blocklen i} -> 
  cipher:lbuffer (v l) -> plain:plainBuffer i (v l) -> ST unit
  (requires (fun h0 -> prf_dexor_requires i t x l cipher plain h0))
  (ensures (fun h0 _ h1 -> prf_dexor_ensures i t x l cipher plain h0 h1))

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

val decrypt:
  i:id -> e:state i Reader ->
  n:Cipher.iv (alg i) ->
  aadlen:UInt32.t {aadlen <=^ aadmax} ->
  aadtext:lbuffer (v aadlen) ->
  plainlen:UInt32.t {safelen i (v plainlen) (PRF.ctr_0 i +^ 1ul)} ->
  plaintext:plainBuffer i (v plainlen) ->
  ciphertext:lbuffer (v plainlen + v MAC.taglen)
  { Buffer.disjoint aadtext ciphertext /\
    Buffer.disjoint_2 (Plain.as_buffer plaintext) aadtext ciphertext }
  -> STL bool
  (requires (fun h ->
    inv h #i #Reader e /\
    Buffer.live h aadtext /\
    Buffer.live h ciphertext /\
    Plain.live h plaintext ))
  (ensures (fun h0 verified h1 ->
    inv h1 #i #Reader e /\
    Buffer.live h1 aadtext /\
    Buffer.live h1 ciphertext /\
    Plain.live h1 plaintext /\
    Buffer.modifies_1 (Plain.as_buffer plaintext) h0 h1 /\
    (safeId i ==> (
        let found = find (HS.sel h1 e.log) n in
        if verified then
          let a = Buffer.as_seq h1 aadtext in
          let p = Plain.sel_plain h1 plainlen plaintext in
          let c = Buffer.as_seq h1 ciphertext in
          found == Some (Entry n a (v plainlen) p c)
        else
          found == None /\ h0 == h1 ))))


let decrypt i st iv aadlen aad plainlen plain cipher_tagged =
  push_frame();
  let x = PRF({iv = iv; ctr = ctr_0 i}) in // PRF index to the first block
  let ak = PRF.prf_mac i st.prf st.ak x in   // used for keying the one-time MAC
  let cipher = Buffer.sub cipher_tagged 0ul plainlen in
  let tag = Buffer.sub cipher_tagged plainlen MAC.taglen in

  // First recompute and check the MAC
  let h0 = ST.get() in
  assume(
    CMA(MAC.live h0 ak.r /\ MAC.norm h0 ak.r) /\
    Buffer.live h0 aad /\ Buffer.live h0 cipher);

  let acc = accumulate ak aadlen aad plainlen cipher in

  let h1 = ST.get() in
  assert(mac_log ==>  FStar.HyperStack.sel h1 (CMA.alog acc) == encode_both i aadlen (Buffer.as_seq h1 aad) plainlen (Buffer.as_seq h1 cipher));
  assume false; //NS:11/03
  let verified = CMA.verify ak acc tag in

  // let h1 = ST.get() in
  // assert(mac_log /\ MAC.authId (i,iv) ==> (verified == (HS.sel h1 (MAC(ilog ak)) = Some (l,tag))));

  // then, safeID i /\ stateful invariant ==>
  //    not verified ==> no entry in the AEAD table
  //    verified ==> exists Entry(iv ad l p c) in AEAD.log
  //                 and correct entries above x in the PRF table
  //                 with matching aad, cipher, and plain
  //
  // not sure what we need to prove for 1st level of PRF idealization
  // possibly that the PRF table with ctr=0 matches the Entry table.
  // (PRF[iv,ctr=0].MAC.log =  Some(l,t) iff Entry(iv,___))

  assume false; //16-10-16
  if verified then counter_dexor i st.prf (PRF.incr i x) plainlen plain cipher;
  pop_frame();
  verified
