(* This module includes several lemmas to work with the 
   invariants defined in Crypto.AEAD.Invariant *)
module Crypto.AEAD.Lemmas
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

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module MAC = Crypto.Symmetric.MAC
module CMA = Crypto.Symmetric.UF1CMA

module Plain = Crypto.Plain
module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

////////////////////////////////////////////////////////////////////////////////
// Some generic sequence lemmas, easy but boring ... assumed for now
////////////////////////////////////////////////////////////////////////////////
let find_snoc (#a:Type) (s:Seq.seq a) (x:a) (f:a -> Tot bool)
  : Lemma (let res = SeqProperties.find_l f (SeqProperties.snoc s x) in
	   match res with 
	   | None -> SeqProperties.find_l f s == None /\ not (f x)
	   | Some y -> res == SeqProperties.find_l f s \/ (f x /\ x==y))
  = admit() //NS: boring

let find_is_some (#i:id) (#rgn:rid) (b:prf_blocks rgn i) (x:domain i)
  : Lemma (requires (is_Some (find b x)))
          (ensures (Seq.length b <> 0))
  = admit() //NS: boring

let find_blocks_append_l (#i:id) (#rgn:rid) (b:prf_blocks rgn i) (b':prf_blocks rgn i) (x:domain i) 
  : Lemma (requires (is_Some (find b x)))
          (ensures (find (Seq.append b b') x == find b x))
  = admit() //NS: boring

let find_append (#i:id) (#r:rid) (d:domain i) (s1:Seq.seq (PRF.entry r i)) (s2:Seq.seq (PRF.entry r i)) 
   : Lemma (requires (is_None (find s1 d)))
           (ensures (find (Seq.append s1 s2) d == find s2 d))
   = admit() //NS: boring

#set-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 2 --max_fuel 2"
let find_singleton (#rgn:region) (#i:id) (e:PRF.entry rgn i) (x:PRF.domain i) 
    : Lemma (if is_entry_domain x e then PRF.find (Seq.create 1 e) x == Some e.range
	     else PRF.find (Seq.create 1 e) x == None)
    = ()	     

#reset-options "--initial_ifuel 0 --max_ifuel 0 --initial_fuel 2 --max_fuel 2"
assume //NS: boring, this should be in the buffer library
val to_seq_temp: #a:Type -> b:Buffer.buffer a -> l:UInt32.t{v l <= Buffer.length b} -> ST (Seq.seq a)
  (requires (fun h -> Buffer.live h b))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h1 b /\ r == Buffer.as_seq h1 b))
////////////////////////////////////////////////////////////////////////////////

//Basic framing for the main predicate of the invariant
let frame_refines_one_entry (h:mem) (i:id{safeId i}) (mac_rgn:region) 
			    (e:entry i) (blocks:Seq.seq (PRF.entry mac_rgn i))
			    (h':mem)
   : Lemma (requires refines_one_entry h e blocks /\			    
		     HH.modifies_rref mac_rgn TSet.empty (HS h.h) (HS h'.h) /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines_one_entry h' e blocks)
   = let PRF.Entry x rng = Seq.index blocks 0 in
     let m = PRF.macRange mac_rgn i x rng in
     let mac_log = CMA.ilog (CMA.State.log m) in
     assert (m_sel h mac_log = m_sel h' mac_log);
     assert (m_contains mac_log h') //this include HS.live_region, which is not derivable from modifies_ref along

#reset-options "--z3timeout 400 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec frame_refines (i:id{safeId i}) (mac_rgn:region) 
		      (entries:Seq.seq (entry i)) (blocks:Seq.seq (PRF.entry mac_rgn i))
		      (h:mem) (h':mem)
   : Lemma (requires refines h i mac_rgn entries blocks /\
   		     HH.modifies_rref mac_rgn TSet.empty (HS h.h) (HS h'.h) /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines h' i mac_rgn entries blocks)
	   (decreases (Seq.length entries))
   = if Seq.length entries = 0 then 
       ()
     else let e = SeqProperties.head entries in
          let b = num_blocks e in 
         (let blocks_for_e = Seq.slice blocks 0 (b + 1) in
       	  let entries_tl = SeqProperties.tail entries in
          let blocks_tl = Seq.slice blocks (b+1) (Seq.length blocks) in
	  frame_refines i mac_rgn entries_tl blocks_tl h h';
	  frame_refines_one_entry h i mac_rgn e blocks_for_e h')

////////////////////////////////////////////////////////////////////////////////
//A weaker version of the invariant, as it is broken and re-established
////////////////////////////////////////////////////////////////////////////////
let u (n:FStar.UInt.uint_t 32) = uint_to_t n

unfold let pre_refines_one_entry (i:id) (st:state i Writer) (nonce:Cipher.iv (alg i))
				   (len:nat{len<>0}) (plainb:plainBuffer i len) (cipherb:lbuffer (len + v MAC.taglen))
				   (h0:mem) (h1:mem) =
  Buffer.live h1 cipherb /\ 
  Plain.live h1 plainb /\ (
  safeId i /\ prf i ==> (
  let table_0 = HS.sel h0 (PRF.itable i st.prf) in
  let table_1 = HS.sel h1 (PRF.itable i st.prf) in
  let plain = Plain.sel_plain h1 (u len) plainb in
  let c_tagged = Buffer.as_seq h1 cipherb in
  h1 `HS.contains` (PRF.itable i st.prf) /\
  Seq.length table_1 >= Seq.length table_0 /\ (
  let blocks = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in
  let b = num_blocks' i len in
  Seq.equal table_1 (Seq.append table_0 blocks) /\
  b + 1 = Seq.length blocks /\
  (let PRF.Entry x e = Seq.index blocks 0 in
   PRF (x.iv = nonce) /\
   PRF (x.ctr = ctr_0 i) /\  (
   let xors = Seq.slice blocks 1 (b+1) in 
   let cipher, tag = SeqProperties.split c_tagged len in
   safelen i len (ctr_0 i +^ 1ul) /\
   Seq.equal xors (counterblocks i st.prf.mac_rgn (PRF.incr i x) len 0 len plain cipher))))))

val frame_pre_refines: (i:id) -> (st:state i Writer) -> (nonce:Cipher.iv (alg i)) -> 
		      (len:nat{len<>0}) ->  (plainb:plainBuffer i len) -> (cipherb:lbuffer (len + v MAC.taglen)) -> 
		      (h0:mem) -> (h1:mem) -> (h2:mem)
   ->  Lemma (requires (let tagB = Buffer.sub cipherb (u len) MAC.taglen in
		      pre_refines_one_entry i st nonce len plainb cipherb h0 h1 /\
		      Buffer.disjoint (Plain.as_buffer plainb) cipherb /\
		      Buffer.frameOf (Plain.as_buffer plainb) <> st.prf.mac_rgn /\
		      (prf i ==> HS.frameOf (PRF.itable i st.prf) <> Buffer.frameOf cipherb) /\
	              Buffer.live h2 cipherb /\ 
		      Plain.live h2 plainb /\ 
		      (if mac_log
		       then HS.modifies (Set.as_set [st.prf.mac_rgn; Buffer.frameOf cipherb]) h1 h2  /\
			    Buffer.modifies_buf_1 (Buffer.frameOf cipherb) tagB h1 h2
		       else Buffer.modifies_1 tagB h1 h2)))
           (ensures pre_refines_one_entry i st nonce len plainb cipherb h0 h2)
#set-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1"
let frame_pre_refines i st nonce len plainb cipherb h0 h1 h2 = 
  let tagB = Buffer.sub cipherb (u len) MAC.taglen in
  FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 tagB h1) h2;
  if safeId i && prf i
  then let cipher = Buffer.sub cipherb 0ul (u len) in //necessary to trigger
       let table_0 = HS.sel h0 (PRF.itable i st.prf) in
       let table_1 = HS.sel h1 (PRF.itable i st.prf) in
       let table_2 = HS.sel h2 (PRF.itable i st.prf) in
       assert (pre_refines_one_entry i st nonce len plainb cipherb h0 h2)
  
let frame_pre_refines_0 (i:id) (st:state i Writer) (nonce:Cipher.iv (alg i))
		       (len:nat{len<>0}) (plainb:plainBuffer i len) (cipherb:lbuffer (len + v MAC.taglen))
		       (h0:mem) (h1:mem) (h2:mem)
   : Lemma (requires (let tagB = Buffer.sub cipherb (u len) MAC.taglen in
		      pre_refines_one_entry i st nonce len plainb cipherb h0 h1 /\
		      Buffer.disjoint (Plain.as_buffer plainb) cipherb /\
		      (prf i ==> HS.frameOf (PRF.itable i st.prf) <> Buffer.frameOf cipherb) /\
		      Buffer.modifies_0 h1 h2))
           (ensures pre_refines_one_entry i st nonce len plainb cipherb h0 h2)
   = let tagB = Buffer.sub cipherb (u len) MAC.taglen in
     Buffer.lemma_reveal_modifies_0 h1 h2;
     let cipher = Buffer.sub cipherb 0ul (u len) in //necessary to trigger
     ()

val counterblocks_len: #i:id{safeId i} -> 
			     (rgn:region) -> 
			     (x:domain i{ctr_0 i <^ x.ctr}) ->
			     (len:nat{len <> 0}) ->
			     (from_pos:nat{from_pos <= len /\ safelen i (len - from_pos) x.ctr}) ->
			     (plain:Plain.plain i len) ->
			     (cipher:lbytes len) ->
    Lemma (requires True)
  	  (ensures
	     (Seq.length (counterblocks i rgn x len from_pos len plain cipher) =
			 (num_blocks' i (len - from_pos))))
          (decreases (len - from_pos))
let rec counterblocks_len #i rgn x len from_pos plain cipher = 
  if from_pos = len
  then ()
  else let blockl = v (Cipher(blocklen (cipherAlg_of_id i))) in 
       let remaining = len - from_pos in 
       let l0 = minNat remaining blockl in 
       counterblocks_len #i rgn (PRF.incr i x) len (from_pos + l0) plain cipher
  
let intro_refines_one_entry_no_tag
                            (#i:id) (st:state i Writer) (nonce: Cipher.iv (alg i))
                            (len:nat{len<>0}) (plain:plainBuffer i len) (cipher:lbuffer (len + v MAC.taglen))
                            (h0:mem) (h1:mem) (h2:mem{Buffer.live h2 cipher /\ Plain.live h2 plain})
   : Lemma (requires (safeId i /\ prf i ==> 
		     (let mac_rgn = st.prf.mac_rgn in
		      let p = Plain.sel_plain h2 (u len) plain in
		      let c_tagged = Buffer.as_seq h2 cipher in
		      let table_0 = HS.sel h0 (PRF.itable i st.prf) in
		      let table_1 = HS.sel h1 (PRF.itable i st.prf) in
		      let table_2 = HS.sel h2 (PRF.itable i st.prf) in
		      let x_0 = {iv=nonce; ctr=ctr_0 i} in
	              let c, _ = SeqProperties.split c_tagged len in
	              h2 `HS.contains` (PRF.itable i st.prf) /\
		      (exists mac. Seq.equal table_1 (SeqProperties.snoc table_0 (PRF (Entry x_0 mac)))) /\
		      safelen i len (ctr_0 i +^ 1ul) /\
		      table_2 == (Seq.append table_1 (counterblocks i mac_rgn (PRF.incr i x_0) len 0 len p c)))))
	    (ensures (pre_refines_one_entry i st nonce len plain cipher h0 h2))
   = if safeId i && prf i 
     then let mac_rgn = st.prf.mac_rgn in
	  let p = Plain.sel_plain h2 (u len) plain in
	  let c_tagged = Buffer.as_seq h2 cipher in
	  let initial_domain = PRF.incr i ({iv=nonce; ctr=ctr_0 i}) in
	  let c, _ = SeqProperties.split c_tagged len in
	  counterblocks_len #i mac_rgn initial_domain len 0 p c

let mac_refines (i:id) 
		(st:state i Writer) (nonce: Cipher.iv (alg i))
		(#aadlen: UInt32.t {aadlen <=^ aadmax}) (aad: lbuffer (v aadlen))
                (#len:nat{len<>0}) (plain:plainBuffer i len) (cipher:lbuffer (len + v MAC.taglen))
   		(h:mem{Buffer.live h aad /\ Plain.live h plain /\ Buffer.live h cipher})
   = let mac_rgn = st.prf.mac_rgn in
     let p = Plain.sel_plain h (u len) plain in
     let c, tag = SeqProperties.split (Buffer.as_seq h cipher) len in
     let ad = Buffer.as_seq h aad in
     let x0 : PRF.domain i = {iv=nonce; ctr=ctr_0 i} in
     x0.ctr = ctr_0 i /\
     safelen i len (PRF.ctr_0 i +^ 1ul) /\
     (safeId i /\ prf i ==> 
      (let tab = HS.sel h (PRF.itable i st.prf) in
       match PRF.find_mac tab x0 with 
       | None -> False
       | Some m -> 
         let mac_log = CMA.ilog (CMA.State.log m) in
	 m_contains mac_log h /\ (
	 match m_sel h (CMA.ilog (CMA.State.log m)) with
	 | None           -> False
	 | Some (msg,tag') -> msg = encode_both i (uint_to_t (Seq.length ad)) ad (u len) c /\
	                     tag = tag')))

let intro_mac_refines (i:id) (st:state i Writer) (nonce: Cipher.iv (alg i))
		      (#aadlen: UInt32.t {aadlen <=^ aadmax}) (aad: lbuffer (v aadlen))
                      (#len:nat{len<>0}) (plain:plainBuffer i len) (cipher:lbuffer (len + v MAC.taglen))
   		      (h:mem{Buffer.live h aad /\ Plain.live h plain /\ Buffer.live h cipher})
   : Lemma (requires (let x0 : PRF.domain i = {iv=nonce; ctr=ctr_0 i} in
		      let mac_rgn = st.prf.mac_rgn in
		      let p = Plain.sel_plain h (u len) plain in
		      let c, _ = SeqProperties.split (Buffer.as_seq h cipher) len in
		      let tagB = Buffer.sub cipher (u len) MAC.taglen in
		      let ad = Buffer.as_seq h aad in
		      let x0 : PRF.domain i = {iv=nonce; ctr=ctr_0 i} in
	              safelen i len (PRF.ctr_0 i +^ 1ul) /\
	              (safeId i /\ prf i ==> 
		      (let tab = HS.sel h (PRF.itable i st.prf) in
		       let l : CMA.text = encode_both i (u (Seq.length ad)) ad (u len) c in
		       match PRF.find_mac tab x0 with 
		       | None -> False
		       | Some mac_st -> 
			 m_contains (CMA (ilog mac_st.log)) h /\
		         m_sel h (CMA (ilog mac_st.log)) == Some (l, Buffer.as_seq h tagB)))))
           (ensures mac_refines i st nonce aad plain cipher h)
  = ()
 
#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let all_above_counterblocks (i:id)
                       (rgn:region)
                       (x:PRF.domain i{ctr_0 i <^ ctr x})
                       (l:nat)
                       (from_pos:nat)
                       (to_pos:nat{from_pos <= to_pos /\ to_pos <= l /\ safelen i (to_pos - from_pos) (ctr x)})
                       (plain:Plain.plain i l)
                       (cipher:lbytes l)
   : Lemma (safeId i ==> (counterblocks i rgn x l from_pos to_pos plain cipher) `all_above` x)
   = admit() //easy, should do it

#set-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let find_cons_hd (#a:Type) (x:a) (tl:Seq.seq a) (f:(a -> Tot bool))
  : Lemma (requires (f x))
         (ensures (SeqProperties.find_l f (SeqProperties.cons x tl) == Some x))
  = ()

let contains_intro_2 (#a:Type) (s:Seq.seq a) (x:a) (k:nat)
  : Lemma (k < Seq.length s /\ Seq.index s k == x
           ==>
          s `SeqProperties.contains` x)
  = SeqProperties.contains_intro s k x
  
#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let find_mac_counterblocks_none (#rgn:region) (#i:id) (nonce:Cipher.iv (alg i))
                                (s:Seq.seq (PRF.entry rgn i))
    : Lemma (requires (s `all_above` (PRF.incr i ({iv=nonce; ctr=ctr_0 i}))))
            (ensures (find_mac s ({iv=nonce; ctr=ctr_0 i}) == None))
    = admit() //easy, should do it

val pre_refines_to_refines: (i:id) -> (st:state i Writer) -> (nonce: Cipher.iv (alg i)) ->
			    (aadlen: UInt32.t {aadlen <=^ aadmax})  ->
			    (aad: lbuffer (v aadlen)) ->
                            (len:nat{len<>0}) -> (plain:plainBuffer i len) -> (cipher:lbuffer (len + v MAC.taglen)) ->
			    (h0:mem) ->
                            (h:mem{Buffer.live h aad /\ Plain.live h plain /\ Buffer.live h cipher}) 
   -> Lemma (requires (let mac_rgn = st.prf.mac_rgn in
     		      let p = Plain.sel_plain h (u len) plain in
		      let c_tagged = Buffer.as_seq h cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h aad in
  		      safeId i ==> 
			(none_above ({iv=nonce; ctr=ctr_0 i}) st.prf h0 /\
   			 pre_refines_one_entry i st nonce len plain cipher h0 h /\
			 mac_refines i st nonce aad plain cipher h)))
            (ensures (let mac_rgn = st.prf.mac_rgn in
     		      let p = Plain.sel_plain h (u len) plain in
		      let c_tagged = Buffer.as_seq h cipher in
	              let c, tag = SeqProperties.split c_tagged len in
		      let ad = Buffer.as_seq h aad in
  		      let entry = Entry nonce ad len p c_tagged in
		      safeId i ==>  (
			pre_refines_one_entry i st nonce len plain cipher h0 h /\ (
			  let table_0 = HS.sel h0 (PRF.itable i st.prf) in
			  let table_1 = HS.sel h (PRF.itable i st.prf) in
 			  let blocks = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in
			  refines_one_entry #mac_rgn #i h entry blocks))))
#reset-options "--z3timeout 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"
let pre_refines_to_refines i st nonce aadlen aad len plain cipher h0 h
    = if safeId i
      then let table_0 = HS.sel h0 (PRF.itable i st.prf) in
      	   let idom = {iv=nonce; ctr=ctr_0 i} in
	   assert (PRF.find table_0 idom == None);
	   let table_1 = HS.sel h (PRF.itable i st.prf) in
  	   let prefix = Seq.slice table_1 0 (Seq.length table_0) in 
	   assert (Seq.equal prefix table_0);
	   assert (is_None (find prefix idom));
 	   let blocks = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in
	   let p = Plain.sel_plain h (u len) plain in
	   let c_tagged = Buffer.as_seq h cipher in
           let c, tag = SeqProperties.split c_tagged len in
	   let hd = Seq.index blocks 0 in
	   let PRF.Entry x e = hd in
	   let cbs = counterblocks i st.prf.mac_rgn (PRF.incr i idom) len 0 len p c in
	   assert (x = idom);
	   assert (Seq.equal blocks (SeqProperties.cons hd cbs));
           all_above_counterblocks i st.prf.mac_rgn (PRF.incr i idom) len 0 len p c;
	   find_mac_counterblocks_none #st.prf.mac_rgn #i nonce cbs;
	   assert (PRF.is_entry_domain idom hd);
      	   find_cons_hd hd cbs (PRF.is_entry_domain idom);
	   find_append idom prefix blocks


(* this version causes a crash *)
(* let intro_refines_one_entry (#mac_rgn:region) (#i:id{safeId i) (st:state i Writer) (n: Cipher.iv (alg i)) *)
(*                             (aadlen: UInt32.t {aadlen <=^ aadmax}) (aad: lbuffer (v aadlen)) *)
(*                             (l:nat) (plain:plainBuffer i l) (cipher:lbuffer (l + v MAC.taglen)) *)
(*                             (h0:mem) (h1:mem{Buffer.live h1 aad /\ Buffer.live h1 cipher /\ Plain.live h1 plain}) *)
(*    : Lemma (let aad = Buffer.as_seq h1 aad in *)
(*             let p = Plain.sel_plain h1 (u l) plain in *)
(*             let c = Buffer.as_seq h1 cipher in *)
(*             let entry = Entry n aad l p c in *)
(*             let table_0 = HS.sel h0 st.prf in *)
(*             let table_1 = HS.sel h1 st.prf in *)
(*             Seq.length table_1 >= Seq.length table_0 /\ *)
(*             (let blocks = Seq.slice table_1 (Seq.length table_0) (Seq.length table_1) in *)
(*             refines_one_entry h1 entry blocks)) *)

(* 	    HS.sel h1 st.log == SeqProperties.snoc (HS.sel h0 st.log) (Entry n aad (v plainlen) p c))) *)
(* let 			     *)

(*** Some basic sanity checks 
     on the `refines` invariant ***)

(* 1. empty refines empty *)
private let refines_empty (h:mem) (i:id{safeId i}) (rgn:region) 
  : Lemma (refines h i rgn Seq.createEmpty Seq.createEmpty)
  = ()

(* block_lengths: used only for the statement of the next lemma *)
private let rec block_lengths (#i:id{safeId i}) (entries:Seq.seq (entry i)) 
  : Tot nat (decreases (Seq.length entries))
  = if Seq.length entries = 0 then
      0
    else let e = SeqProperties.head entries in
	 num_blocks e + 1 + block_lengths (SeqProperties.tail entries)

#set-options "--z3timeout 20 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
(* 2. refines sums block lengths *)
private let rec refines_length (#rgn:region) (#i:id{safeId i}) (h:mem) 
		       (entries:Seq.seq (entry i)) (blocks:Seq.seq (PRF.entry rgn i))
   : Lemma (requires (refines h i rgn entries blocks))
	   (ensures (block_lengths entries = Seq.length blocks))
  	   (decreases (Seq.length entries))
   = if Seq.length entries = 0 then 
       ()
     else let hd = SeqProperties.head entries in
	  let entries_tl = SeqProperties.tail entries in
	  let b = num_blocks hd in
	  let blocks_tail = Seq.slice blocks (b + 1) (Seq.length blocks) in
	  refines_length h entries_tl blocks_tail

(*** Extending `refines` by adding one block ***)

#set-options "--z3timeout 100 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 0"
(* refines_one_entry can be lifted refines sums block lengths *)
private let refines_singleton (h:mem) (i:id{safeId i}) (rgn:region) (e:entry i) (blocks_for_e:Seq.seq (PRF.entry rgn i))
  : Lemma (requires (refines_one_entry h e blocks_for_e))
	  (ensures (refines h i rgn (Seq.create 1 e) blocks_for_e))
  = let b = num_blocks e in 
    cut (Seq.equal (Seq.slice blocks_for_e 0 (b + 1)) blocks_for_e)

#reset-options "--z3timeout 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec extend_refines (h:mem) (i:id{safeId i}) (mac_rgn:region) 
		    (entries:Seq.seq (entry i))
		    (blocks:Seq.seq (PRF.entry mac_rgn i))
		    (e:entry i)
		    (blocks_for_e:Seq.seq (PRF.entry mac_rgn i))
   		    (h':mem)
  : Lemma (requires refines h i mac_rgn entries blocks /\
		    refines_one_entry h' e blocks_for_e /\
		    HS.modifies_ref mac_rgn TSet.empty h h' /\
		    HS.live_region h' mac_rgn)
	  (ensures (refines h' i mac_rgn (SeqProperties.snoc entries e) (Seq.append blocks blocks_for_e)))
	  (decreases (Seq.length entries))
  = if Seq.length entries = 0 then
      (refines_singleton h' i mac_rgn e blocks_for_e;
       cut (Seq.equal (SeqProperties.snoc entries e) (Seq.create 1 e));
       cut (Seq.equal (Seq.append blocks blocks_for_e) blocks_for_e))
    else let hd = SeqProperties.head entries in
	 let entries_tl = SeqProperties.tail entries in
	 let b = num_blocks hd in
	 let blocks_hd = Seq.slice blocks 0 (b + 1) in
	 let blocks_tl = Seq.slice blocks (b + 1) (Seq.length blocks) in
	 assert (refines h i mac_rgn entries_tl blocks_tl);
	 frame_refines_one_entry h i mac_rgn hd blocks_hd h';
	 extend_refines h i mac_rgn entries_tl blocks_tl e blocks_for_e h';
	 assert (refines h' i mac_rgn (SeqProperties.snoc entries_tl e) (Seq.append blocks_tl blocks_for_e));
	 cut (Seq.equal (SeqProperties.snoc entries e) (SeqProperties.cons hd (SeqProperties.snoc entries_tl e)));
	 cut (SeqProperties.head (SeqProperties.snoc entries e) == hd);
	 cut (Seq.equal (SeqProperties.tail (SeqProperties.snoc entries e)) (SeqProperties.snoc entries_tl e));
	 let blocks_hd = Seq.slice blocks 0 (b + 1) in
	 let ext_blocks = Seq.append blocks blocks_for_e in
	 cut (Seq.equal ext_blocks
    			(Seq.append blocks_hd (Seq.append blocks_tl blocks_for_e)));
	 cut (Seq.equal (Seq.slice ext_blocks 0 (b + 1)) blocks_hd);
	 cut (Seq.equal (Seq.slice ext_blocks (b + 1) (Seq.length ext_blocks)) 
			(Seq.append blocks_tl blocks_for_e))

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let counterblocks_emp   (i:id)
			(rgn:region)
			(x:PRF.domain i{ctr_0 i <^ ctr x })
			(l:nat)
			(to_pos:nat{to_pos <= l /\ safelen i 0 (ctr x)})
			(plain:Plain.plain i l)
			(cipher:lbytes l)
   : Lemma (safeId i ==> counterblocks i rgn x l to_pos to_pos plain cipher == Seq.createEmpty)
   = ()

#set-options "--z3timeout 100"

let lemma_cons_snoc (#a:Type) (hd:a) (s:Seq.seq a) (tl:a)
  : Lemma (requires True)
	  (ensures (Seq.equal (SeqProperties.cons hd (SeqProperties.snoc s tl))
		 	      (SeqProperties.snoc (SeqProperties.cons hd s) tl)))
  = ()	  

#reset-options "--z3timeout 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val counterblocks_snoc: #i:id{safeId i} -> (rgn:region) -> (x:domain i{ctr_0 i <^ x.ctr}) -> (k:nat{v x.ctr <= k}) ->
			 (len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)})  ->
			 (next:nat{0 < next /\ next <= v (PRF.blocklen i)}) ->
			 (completed_len:nat{ completed_len + next <= len /\ 
					   FStar.Mul ((k - v (offset i)) * v (PRF.blocklen i) = completed_len)}) ->
			 (plain:Plain.plain i len) ->
			 (cipher:lbytes len) ->
     Lemma (requires True)
	   (ensures
	     (let open FStar.Mul in
	      let plain_last = Plain.slice plain completed_len (completed_len + next) in
	      let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	      let from = (v x.ctr - (v (offset i))) * v (PRF.blocklen i) in
	      Seq.equal (counterblocks i rgn x len from (completed_len + next) plain cipher)
			(SeqProperties.snoc (counterblocks i rgn x len from completed_len plain cipher)
							   (PRF.Entry ({x with ctr=UInt32.uint_to_t k}) (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last)))))
	   (decreases (completed_len - v x.ctr))
let rec counterblocks_snoc #i rgn x k len next completed_len plain cipher =
   let open FStar.Mul in
   let from_pos = (v x.ctr - (v (offset i))) * v (PRF.blocklen i) in
     (* let from_pos = (v x.ctr - 1) * v (PRF.blocklen i) in *)
   let to_pos = completed_len + next in
   if completed_len - from_pos = 0
   then counterblocks_emp i rgn (PRF.incr i x) len to_pos plain cipher
   else   let y = PRF.incr i x in
	  let remaining = to_pos - from_pos in 
	  let l0 = minNat remaining (v (PRF.blocklen i)) in
	  let plain_hd = Plain.slice plain from_pos (from_pos + l0) in
	  let cipher_hd = Seq.slice cipher from_pos (from_pos + l0) in
	  let plain_last = Plain.slice plain completed_len (completed_len + next) in
	  let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	  let head = PRF.Entry x (PRF.OTP (UInt32.uint_to_t l0) plain_hd cipher_hd) in
	  let recursive_call = counterblocks i rgn y len (from_pos + l0) to_pos plain cipher in
	  let middle = counterblocks i rgn y len (from_pos + l0) completed_len plain cipher in
	  let last_entry = PRF.Entry ({x with ctr=UInt32.uint_to_t k}) (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last) in
	  assert (counterblocks i rgn x len from_pos to_pos plain cipher ==
		  SeqProperties.cons head recursive_call);
	  counterblocks_snoc rgn y k len next completed_len plain cipher;
	  assert (recursive_call == SeqProperties.snoc middle last_entry);
          lemma_cons_snoc head middle last_entry

#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

val counterblocks_slice: #i:id{safeId i} -> 
			     (rgn:region) -> 
			     (x:domain i{ctr_0 i <^ x.ctr}) ->
			     (len:nat{len <> 0}) ->
			     (from_pos:nat) ->
			     (to_pos:nat{from_pos <= to_pos /\ to_pos <= len /\ safelen i (to_pos - from_pos) x.ctr}) ->
			     (plain:Plain.plain i len) ->
			     (cipher:lbytes len) ->
    Lemma (requires True)
	   (ensures
	     (Seq.equal (counterblocks i rgn x len from_pos to_pos plain cipher)
	 	        (counterblocks i rgn x (to_pos - from_pos) 0 (to_pos - from_pos)
					       (Plain.slice plain from_pos to_pos) 
 					       (Seq.slice cipher from_pos to_pos))))
           (decreases (to_pos - from_pos))						 

(* The general proof idea *)
(*
  let from' = from + l
  cb from to p
  = slice p from from'          @ cb from' to p                           //unfolding
  =      ''      ''             @ cb 0 (to - from') (slice p from' to)    //IH1
  =      ''      ''             @ cb 0 (to - from') (slice (slice p from to) l (to - from)) //slice-slice-1
  =      ''      ''             @ cb l (to - from) (slice p from to)      //IH2 (backwards)
  = slice (slice p from to) 0 l @     ''                ''                //slice-slice-2
  = cb 0 (to - from) (slice p from to)                                    //folding
*)
let rec counterblocks_slice #i rgn x len from_pos to_pos plain cipher 
   = let remaining = to_pos - from_pos in 
     if remaining = 0
     then ()
     else let l = minNat remaining (v (PRF.blocklen i)) in
	  let y = PRF.incr i x in
	  let from_pos' = from_pos + l in
	  let ih1 = counterblocks_slice rgn y len from_pos' to_pos plain cipher in
  	  let ih2 = counterblocks_slice rgn y (to_pos - from_pos) l (to_pos - from_pos) (Plain.slice plain from_pos to_pos) (Seq.slice cipher from_pos to_pos) in
	  //slice-slice-1
	  assert (Seq.equal (as_bytes #i #(to_pos - from_pos') (Plain.slice plain from_pos' to_pos))
			    (as_bytes #i #(to_pos - from_pos') (Plain.slice (Plain.slice plain from_pos to_pos) l (to_pos - from_pos))));
	  assert (Seq.equal (Seq.slice cipher from_pos' to_pos)
			    (Seq.slice (Seq.slice cipher from_pos to_pos) l (to_pos - from_pos)));
	  //slice-slice-2
          assert (Seq.equal (as_bytes #i #l (Plain.slice (Plain.slice plain from_pos to_pos) 0 l))
			    (as_bytes #i #l (Plain.slice plain from_pos from_pos')));
          assert (Seq.equal (Seq.slice (Seq.slice cipher from_pos to_pos) 0 l)
			    (Seq.slice cipher from_pos from_pos'))

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100"
val frame_counterblocks_snoc: i:id{safeId i} -> (t:PRF.state i) -> (x:domain i{ctr_0 i <^ x.ctr}) -> k:nat{v x.ctr <= k} ->
			     len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)} -> 
			     (completed_len:nat{completed_len < len /\
				              FStar.Mul ((k - v (offset i)) * v (PRF.blocklen i) = completed_len)}) ->
			     (plain:plainBuffer i len) -> 
			     (cipher:lbuffer len) ->
			     (h0:mem{Plain.live h0 plain /\ 
				     Buffer.live h0 cipher}) ->
			     (h1:mem{Plain.live h1 plain /\ 
				     Buffer.live h1 cipher}) ->
   Lemma (requires (let remaining_len = len - completed_len in
		    let l = minNat remaining_len (v (PRF.blocklen i)) in
		    let plain_hd = Plain.sub plain (u completed_len) (u l) in
		    let cipher_hd = Buffer.sub cipher (u completed_len) (u l) in
	            modifies_x_buffer_1 t x cipher_hd h0 h1 /\
		    Buffer.disjoint (as_buffer plain) cipher /\
		    Buffer.frameOf (as_buffer plain) <> t.rgn /\
		    Buffer.frameOf cipher <> t.rgn /\
		    safelen i completed_len (ctr_0 i +^ 1ul)))
          (ensures (let open FStar.Mul in 
		    let p0 = Plain.sel_plain h0 (u len) plain in
		    let c0 = Buffer.as_seq h0 cipher in
	    	    let p = Plain.sel_plain h1 (u len) plain in
		    let c = Buffer.as_seq h1 cipher in
		    let remaining_len = len - completed_len in
		    let next = minNat remaining_len (v (PRF.blocklen i)) in
		    let initial_x = {x with ctr=ctr_0 i +^ 1ul} in
		    let initial_blocks = counterblocks i t.mac_rgn initial_x len 0 completed_len p0 c0 in
		    let final_blocks = counterblocks i t.mac_rgn initial_x len 0 (completed_len + next) p c in
	     	    let plain_last = Plain.slice p completed_len (completed_len + next) in
		    let cipher_last = Seq.slice c completed_len (completed_len + next) in
		    let last_entry = PRF.Entry ({x with ctr=UInt32.uint_to_t k})
	 				       (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last) in
		    final_blocks == SeqProperties.snoc initial_blocks last_entry))
(* #set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100" *)
let frame_counterblocks_snoc i t x k len completed_len plain cipher h0 h1 = 
  let open FStar.Mul in
  let remaining_len = len - completed_len in
  let next = minNat remaining_len (v (PRF.blocklen i)) in
  let p0 = Plain.sel_plain h0 (u len) plain in
  let p = Plain.sel_plain h1 (u len) plain in
  let c0 = Buffer.as_seq h0 cipher in
  let c = Buffer.as_seq h1 cipher in
  let cipher_hd = Buffer.sub cipher (u completed_len) (u next) in
  let cipher_pre = Buffer.sub cipher (u 0) (u completed_len) in
  assert (Buffer.disjoint cipher_hd cipher_pre);
  let c0_prefix = Seq.slice c0 0 completed_len in
  let c_prefix = Seq.slice c 0 completed_len in
  assert (Seq.equal c0_prefix c_prefix);
  assert (Seq.equal (as_bytes p) (as_bytes p0));
  assert (p == p0); 
  let initial_x = {x with ctr=ctr_0 i +^ 1ul} in
  counterblocks_snoc  #i t.mac_rgn initial_x k len next completed_len p c;
  counterblocks_slice #i t.mac_rgn initial_x len 0 completed_len p c;
  counterblocks_slice #i t.mac_rgn initial_x len 0 completed_len p0 c0

#set-options "--initial_ifuel 1 --max_ifuel 1 --initial_fuel 2 --max_fuel 2"
let invert_contains_plain_and_cipher_block   (#i:id) (#r:rid) (#l:u32{l <=^ PRF.blocklen i})
					     (x:domain i{safeId i /\ ctr_0 i <^ x.ctr})
					     (plain:plain i (v l))
					     (cipher:lbytes (v l))
					     (b:PRF.entry r i)
    : Lemma (requires (contains_plain_block x plain (Seq.create 1 b) /\
		       contains_cipher_block (v l) x cipher (Seq.create 1 b)))
            (ensures (b == PRF.Entry #r #i x (PRF.OTP l plain cipher)))
    = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 400"
val extending_counter_blocks: #i:id -> (t:PRF.state i) -> (x:domain i{ctr_0 i <^ x.ctr}) ->
			     len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)} -> 
			     (completed_len:nat{completed_len < len /\
				              FStar.Mul ((v x.ctr - v (offset i)) * v (PRF.blocklen i) = completed_len)}) ->
			     (plain:plainBuffer i len) -> 
			     (cipher:lbuffer len) ->
			     (h0:mem{Plain.live h0 plain /\ 
				     Buffer.live h0 cipher}) ->
			     (h1:mem{Plain.live h1 plain /\ 
				     Buffer.live h1 cipher}) ->
			     (h_init:mem) ->
   Lemma (requires (let remaining_len = len - completed_len in
		    let l = minNat remaining_len (v (PRF.blocklen i)) in
		    let plain_hd = Plain.sub plain (u completed_len) (u l) in
		    let cipher_hd = Buffer.sub cipher (u completed_len) (u l) in
		    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
	            modifies_x_buffer_1 t x cipher_hd h0 h1 /\
		    Buffer.disjoint (as_buffer plain) cipher /\
		    Buffer.frameOf (as_buffer plain) <> t.rgn /\
		    Buffer.frameOf cipher <> t.rgn /\
		    safelen i completed_len (ctr_0 i +^ 1ul) /\
		    none_above x t h0 /\
		    (safeId i ==> 
		       (let r = itable i t in
			let blocks_1 = HS.sel h1 (PRF.itable i t) in
		        h0 `HS.contains` r /\
			HS.sel h0 t.table == 
			  Seq.append (HS.sel h_init t.table)
				     (counterblocks i t.mac_rgn initial_domain
						 len 0 completed_len
						 (Plain.sel_plain h0 (u len) plain)
						 (Buffer.as_seq h0 cipher)) /\
                        contains_plain_block x (sel_plain h1 (u l) plain_hd) blocks_1 /\
			contains_cipher_block l x (sel_bytes h1 (u l) cipher_hd) blocks_1))))
          (ensures (let remaining_len = len - completed_len in
		    let l = minNat remaining_len (v (PRF.blocklen i)) in
		    let completed_len' = completed_len + l in
    		    let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
		    safeId i ==>
		      Seq.equal (HS.sel h1 t.table)
				(Seq.append (HS.sel h_init t.table) 
					    (counterblocks i t.mac_rgn initial_domain
						 len 0 completed_len'
						 (Plain.sel_plain h1 (u len) plain)
						 (Buffer.as_seq h1 cipher)))))

(* Here's the general proof strategy:

1. exists suffix.
       HS.sel h1 t.table = Seq.snoc (HS.sel h0.table) suffix /\
       suffix.domain = x
   
   //from modifies_x_buffer_1, none_above
       
2. suffix = last_entry  
     where last_entry = Entry x (OTP len plain_last cipher_last)

  //from find_otp ... 
  
3. let  init = HS.sel h_init t.table
   
   snoc (Seq.append init (counterblocks ...)) last_entry
   = Seq.append init (snoc (counterblocks ..) last_entry)  //by a standard snoc/append lemma
   = Seq.append init final_blocks                          //by frame_counterblocks_snoc
*)
let extending_counter_blocks #i t x len completed_len plain cipher h0 h1 h_init
  = if safeId i
    then begin
	 let r = itable i t in 
	 let r0 = HS.sel h0 r in
	 let r1 = HS.sel h1 r in 
 	 let suffix = SeqProperties.last r1 in
	 assert (Seq.equal r1 (SeqProperties.snoc r0 suffix));
	 assert (PRF.find r0 x == None);
	 find_append x r0 (Seq.create 1 suffix);
	 find_singleton suffix x;
	 assert (PRF.find r1 x == Some suffix.range);    
	 let p = Plain.sel_plain h1 (u len) plain in
	 let c = Buffer.as_seq h1 cipher in
	 let remaining_len = len - completed_len in
	 let next = minNat remaining_len (v (PRF.blocklen i)) in
	 let plain_last = Plain.slice p completed_len (completed_len + next) in
	 let cipher_last = Seq.slice c completed_len (completed_len + next) in
	 let last_entry = PRF.Entry #t.mac_rgn #i x (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last) in
	 let plain_last' =
	     Plain.sel_plain h1 (u next) (Plain.sub plain (u completed_len) (u next)) in
         let cipher_last' =
	     sel_bytes h1 (u next) (Buffer.sub cipher (u completed_len) (u next)) in
	 assert (Seq.equal (Plain.as_bytes #i #next plain_last) (Plain.as_bytes #i #next plain_last'));
	 assert (Seq.equal cipher_last cipher_last');
	 invert_contains_plain_and_cipher_block #i #t.mac_rgn #(u next) x plain_last cipher_last suffix;
	 assert (suffix == last_entry);
	 frame_counterblocks_snoc i t x (v x.ctr) len completed_len plain cipher h0 h1
    end

