module Crypto.AEAD.Encrypt.Aux
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

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain
module Invariant = Crypto.AEAD.Invariant
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module CMA = Crypto.Symmetric.UF1CMA
module Seq = FStar.Seq


#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
val extend_refines_aux: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) ->
		       (aadlen: UInt32.t {aadlen <=^ aadmax}) ->
		       (aad: lbuffer (v aadlen)) ->
                       (len:nat{len<>0}) -> (plain:plainBuffer i len) -> (cipher:lbuffer (len + v MAC.taglen)) ->
		       (h0:mem) ->
                       (h1:mem{Buffer.live h1 aad /\ Plain.live h1 plain /\ Buffer.live h1 cipher}) ->
    Lemma (requires ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
		      Seq.length table_1 > Seq.length blocks_0 /\ (
		      let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in

     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = Seq.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      pre_refines_one_entry i st nonce len plain cipher h0 h1 /\
		      inv h0 st /\
		      refines_one_entry #_ #i h1 entry blocks_1 /\
      		      HS.modifies_ref mac_rgn TSet.empty h0 h1 /\
		      HS.live_region h1 mac_rgn))))
		      
          (ensures ( safeId i ==> (
		      let mac_rgn = st.prf.mac_rgn in
      		      let entries_0 = HS.sel h0 st.log in 
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     		      let p = Plain.sel_plain h1 (u len) plain in
		      let c_tagged = Buffer.as_seq h1 cipher in
	              let c, tag = Seq.split c_tagged len in
		      let ad = Buffer.as_seq h1 aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      refines h1 i mac_rgn (Seq.snoc entries_0 entry) table_1)))
let extend_refines_aux i st nonce aadlen aad len plain cipher h0 h1 = 
  if safeId i then
     let mac_rgn = st.prf.mac_rgn in
     let entries_0 = HS.sel h0 st.log in 
     let blocks_0 = HS.sel h0 (PRF.itable i st.prf) in
     let table_1 = HS.sel h1 (PRF.itable i st.prf) in
     let blocks_1 = Seq.slice table_1 (Seq.length blocks_0) (Seq.length table_1) in
     let p = Plain.sel_plain h1 (u len) plain in
     let c_tagged = Buffer.as_seq h1 cipher in
     let c, tag = Seq.split c_tagged len in
     let ad = Buffer.as_seq h1 aad in
     let entry = Entry nonce ad len p c_tagged in
     extend_refines h0 i mac_rgn entries_0 blocks_0 entry blocks_1 h1

#reset-options "--z3rlimit 400 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let encrypt_ensures' (regions:Set.set HH.rid)
		     (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) = 
     Buffer.live h5 aad /\
     Buffer.live h5 cipher_tagged /\
     Plain.live h5 plain /\
     my_inv st h5 /\
     HS.modifies_transitively regions h0 h5 /\ (
     safeId i ==>  (
       let aad = Buffer.as_seq h5 aad in
       let p = Plain.sel_plain h5 plainlen plain in
       let c = Buffer.as_seq h5 cipher_tagged in
       HS.sel h5 st.log == Seq.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c)))

let encrypt_ensures_tip (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) =
  encrypt_ensures' (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS.(h5.tip)])
    i st n aadlen aad plainlen plain cipher_tagged h0 h5

let encrypt_ensures  (i:id) (st:state i Writer)
		     (n: Cipher.iv (alg i))
 		     (aadlen: UInt32.t {aadlen <=^ aadmax})
		     (aad: lbuffer (v aadlen))
		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		     (plain: plainBuffer i (v plainlen))
		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		     (h0:mem) (h5:mem) =
  encrypt_ensures' (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged])
    i st n aadlen aad plainlen plain cipher_tagged h0 h5

val finish_after_mac: h0:mem -> h3:mem -> i:id -> st:state i Writer -> 
		      n: Cipher.iv (alg i) ->
		      aadlen: UInt32.t {aadlen <=^ aadmax} -> 
		      aad: lbuffer (v aadlen) -> 
		      plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)} -> 
		      plain: plainBuffer i (v plainlen) -> 
		      cipher_tagged:lbuffer (v plainlen + v MAC.taglen) ->
		      ak:CMA.state (i, n) -> acc:CMA.accBuffer (i, n) -> tag:MAC.tagB -> ST unit
  (requires (fun h4 -> 
    let cipher = Buffer.sub cipher_tagged 0ul plainlen in
    let x0 = {iv=n; ctr=ctr_0 i} in
    HS.(h0.tip = h4.tip) /\
    HH.disjoint (HS.(h4.tip)) st.log_region /\
    HH.disjoint (HS.(h4.tip)) (Buffer.frameOf cipher_tagged) /\
    HS.modifies_transitively (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS.(h4.tip)]) h0 h3 /\
    HS.modifies_ref st.prf.mac_rgn TSet.empty h0 h3 /\
    (prf i ==> none_above ({iv=n; ctr=ctr_0 i}) st.prf h0) /\ // The nonce must be fresh!
    pre_refines_one_entry i st n (v plainlen) plain cipher_tagged h0 h3 /\
    mac_ensures (i, n) ak acc tag h3 h4 /\
    (my_inv st h0) /\
    (CMA.(ak.region = st.prf.mac_rgn)) /\
    (safeId i ==> ~ (m_contains (CMA.(ilog ak.log)) h0)) /\
    (prf i ==> HS.frameOf (PRF.itable i st.prf) <> Buffer.frameOf cipher_tagged) /\
    (Buffer.disjoint (Plain.as_buffer plain) cipher_tagged) /\
    (Buffer.disjoint aad cipher_tagged) /\
    (HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) st.log_region) /\
    (HH.disjoint (Buffer.frameOf cipher_tagged) st.log_region) /\  
    (Buffer.live h3 cipher_tagged) /\
    (Plain.live h3 plain) /\
    (Buffer.live h3 aad) /\
    (tag == Buffer.sub cipher_tagged plainlen MAC.taglen) /\
    (mac_log ==> 
      (h3 `HS.contains` CMA.alog acc) /\
      (HS.frameOf (CMA.alog acc) = HS.(h3.tip)) /\
      FStar.HyperStack.sel h3 (CMA.alog acc) ==
      encode_both i aadlen (Buffer.as_seq h3 aad) plainlen (Buffer.as_seq h3 cipher)) /\ //from accumulate
    (safeId i ==>
	HS.modifies_ref st.log_region (TSet.singleton (FStar.Heap.Ref (HS.as_ref (PRF.itable i st.prf)))) h0 h3 /\ (
	let tab = HS.sel h3 (PRF.itable i st.prf) in
	match PRF.find_mac tab x0 with
	| None -> False
	| Some mac_st -> mac_st == ak))))
   (ensures (fun _ _ h5 -> 
              encrypt_ensures_tip i st n aadlen aad plainlen plain cipher_tagged h0 h5))

#reset-options "--z3rlimit 1000 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let finish_after_mac h0 h3 i st n aadlen aad plainlen plain cipher_tagged ak acc tag = 
  if prf i then recall (itable i st.prf);
  if safeId i then recall st.log;
  let h4 = get () in
  if safeId i 
  then begin
    intro_mac_refines i st n aad plain cipher_tagged h4;
    modifies_fresh_empty i n st.prf.mac_rgn ak h0 h3 h4;
    frame_pre_refines i st n (v plainlen) plain cipher_tagged h0 h3 h4;
    pre_refines_to_refines i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
    extend_refines_aux i st n aadlen aad (v plainlen) plain cipher_tagged h0 h4;
    refines_to_inv i st n aadlen aad plainlen plain cipher_tagged
  end
  else FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 tag h3) h4

let encrypt_ensures_push_pop (i:id) (st:state i Writer)
		    (n: Cipher.iv (alg i))
		    (aadlen: UInt32.t {aadlen <=^ aadmax})
		    (aad: lbuffer (v aadlen))
		    (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)})
		    (plain: plainBuffer i (v plainlen))
		    (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
		    (h:mem) (h0:mem) (h5:mem)
   : Lemma (requires (let open FStar.HyperStack in
		      fresh_frame h h0 /\
		      HH.disjoint st.log_region h0.tip /\
		      HH.disjoint (Buffer.frameOf (Plain.as_buffer plain)) h0.tip /\
     		      HH.disjoint (Buffer.frameOf aad) h0.tip /\
      		      HH.disjoint (Buffer.frameOf cipher_tagged) h0.tip /\
		      encrypt_ensures_tip i st n aadlen aad plainlen plain cipher_tagged h0 h5))
	   (ensures (HS.poppable h5 /\
		     encrypt_ensures i st n aadlen aad plainlen plain cipher_tagged h (HS.pop h5)))
   = if safeId i
     then frame_refines i st.prf.mac_rgn (HS.sel h5 st.log) (HS.sel h5 (PRF.itable i st.prf)) h5 (HS.pop h5)


     (* Buffer.live h5 aad /\ *)
     (* Buffer.live h5 cipher_tagged /\ *)
     (* Plain.live h5 plain /\ *)
     (* my_inv st h5 /\ *)
     (* HS.modifies_transitively regions h0 h5 /\ ( *)
     (* safeId i ==>  ( *)
     (*   let aad = Buffer.as_seq h5 aad in *)
     (*   let p = Plain.sel_plain h5 plainlen plain in *)
     (*   let c = Buffer.as_seq h5 cipher_tagged in *)
     (*   HS.sel h5 st.log == Seq.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c))) *)

(* let encrypt_ensures_tip (i:id) (st:state i Writer) *)
(* 		     (n: Cipher.iv (alg i)) *)
(*  		     (aadlen: UInt32.t {aadlen <=^ aadmax}) *)
(* 		     (aad: lbuffer (v aadlen)) *)
(* 		     (plainlen: UInt32.t {plainlen <> 0ul /\ safelen i (v plainlen) (ctr_0 i +^ 1ul)}) *)
(* 		     (plain: plainBuffer i (v plainlen)) *)
(* 		     (cipher_tagged:lbuffer (v plainlen + v MAC.taglen)) *)
(* 		     (h0:mem) (h5:mem) = *)
(*   encrypt_ensures' (Set.as_set [st.log_region; Buffer.frameOf cipher_tagged; HS.(h5.tip)]) *)
(*     i st n aadlen aad plainlen plain cipher_tagged h0 h5 *)



(*+ contains_all_blocks x plain cipher prf_table: 
          fragments plain and cipher into blocks, 
	    starting from position x onwards,
	    ignoring the blocks from [otp_offset i .. x)
	  and states that each of them is present in the prf_table

    NOTE: this duplicates a lot of the structure of counterblocks
	  perhaps it should be restated in terms of counterblocks 
 **)
(* let rec contains_all_blocks (#i:id) (#r:rid) *)
(*   		 	    (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr}) *)
(* 			    (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)}) *)
(* 			    (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <=^ len}) *)
(* 			    (plain:maybe_plain i (v len)) *)
(* 			    (cipher:lbytes (v len)) *)
(* 			    (blocks:prf_table r i) *)
(*    : GTot Type0 (decreases (v remaining_len)) *)
(*    = if not (safeId i) || remaining_len = 0ul then  *)
(*        True *)
(*      else let starting_pos = len -^ remaining_len in *)
(* 	  let l = min remaining_len (PRF.blocklen i) in *)
(* 	  let plain_hd = Plain.slice (as_plain plain) (v starting_pos) (v starting_pos + v l) in *)
(* 	  let cipher_hd = Seq.slice cipher (v starting_pos) (v starting_pos + v l) in *)
(* 	  contains_cipher_block (v l) x cipher_hd blocks /\ *)
(* 	  contains_plain_block x plain_hd blocks /\ *)
(* 	  contains_all_blocks (PRF.incr i x) len (remaining_len -^ l) plain cipher blocks *)
