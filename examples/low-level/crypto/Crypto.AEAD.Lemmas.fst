(* This module includes several lemmas to work with the 
   invariants defined in Crypto.AEAD.Invariant *)
module Crypto.AEAD.Lemmas
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open FStar.Monotonic.RRef

open Crypto.Symmetric.Bytes
open Plain
open Flag

open Crypto.Symmetric.PRF
open Crypto.AEAD.Encoding 
open Crypto.AEAD.Invariant

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

module Spec = Crypto.Symmetric.Poly1305.Spec
module MAC = Crypto.Symmetric.Poly1305.MAC

module Cipher = Crypto.Symmetric.Cipher
module PRF = Crypto.Symmetric.PRF

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

let frame_refines_one_entry (h:mem) (i:id{safeId i}) (mac_rgn:region) 
			    (e:entry i) (blocks:Seq.seq (PRF.entry mac_rgn i))
			    (h':mem)
   : Lemma (requires refines_one_entry h e blocks /\			    
		     HS.modifies_ref mac_rgn TSet.empty h h' /\
		     HS.live_region h' mac_rgn)
	   (ensures  refines_one_entry h' e blocks)
   = let PRF.Entry x rng = Seq.index blocks 0 in
     let m = PRF.macRange mac_rgn i x rng in
     let mac_log = MAC.ilog (MAC.State.log m) in
     assert (m_sel h mac_log = m_sel h' mac_log);
     assert (m_contains mac_log h') //this include HS.live_region, which is not derivable from modifies_ref along
     
#set-options "--z3timeout 100 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
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
let counterblocks_emp   (i:id {safeId i})
			(rgn:region)
			(x:PRF.domain i{ctr x >^ 0ul})
			(l:nat)
			(to_pos:nat{to_pos <= l /\ safelen i 0 (ctr x)})
			(plain:Plain.plain i l)
			(cipher:lbytes l)
   : Lemma (counterblocks i rgn x l to_pos to_pos plain cipher == Seq.createEmpty)
   = ()

#set-options "--z3timeout 100"

let lemma_cons_snoc (#a:Type) (hd:a) (s:Seq.seq a) (tl:a)
  : Lemma (requires True)
	  (ensures (Seq.equal (SeqProperties.cons hd (SeqProperties.snoc s tl))
		 	      (SeqProperties.snoc (SeqProperties.cons hd s) tl)))
  = ()	  
  
let rec counterblocks_snoc (#i:id{safeId i}) (rgn:region) (x:domain i{x.ctr <> 0ul}) (k:nat{v x.ctr <= k})
			 (len:nat{len <> 0 /\ safelen i len 1ul}) 
			 (next:nat{0 < next /\ next <= v (PRF.blocklen i)})
			 (completed_len:nat{ completed_len + next <= len /\ 
					   FStar.Mul ((k - 1) * v (PRF.blocklen i) = completed_len)})
			 (plain:Plain.plain i len)
			 (cipher:lbytes len)
   : Lemma (requires True)
	   (ensures
	     (let open FStar.Mul in
	      let plain_last = Plain.slice plain completed_len (completed_len + next) in
	      let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	      let from = (v x.ctr - 1) * v (PRF.blocklen i) in
	      Seq.equal (counterblocks i rgn x len from (completed_len + next) plain cipher)
			(SeqProperties.snoc (counterblocks i rgn x len from completed_len plain cipher)
							   (PRF.Entry ({x with ctr=UInt32.uint_to_t k}) (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last)))))
	   (decreases (completed_len - v x.ctr))
   = let open FStar.Mul in
     let from_pos = (v x.ctr - 1) * v (PRF.blocklen i) in
     let to_pos = completed_len + next in
     if completed_len - from_pos = 0
     then counterblocks_emp i rgn (PRF.incr i x) len to_pos plain cipher
     else let y = PRF.incr i x in
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

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let u (n:FStar.UInt.uint_t 32) = uint_to_t n

#set-options "--z3timeout 100"
let rec counterblocks_slice (#i:id{safeId i}) (rgn:region) (x:domain i{x.ctr <> 0ul})
			 (len:nat{len <> 0})// /\ safelen i len 1ul}) 
			 (completed_len:nat{completed_len <= len /\ safelen i completed_len x.ctr})
			 (plain:Plain.plain i len)
			 (cipher:lbytes len)
   : Lemma (requires True)
	   (ensures
	     (Seq.equal (counterblocks i rgn x len 0 completed_len plain cipher)
	 	        (counterblocks i rgn x completed_len 0 completed_len 
					     (Plain.slice plain 0 completed_len) 
 					     (Seq.slice cipher 0 completed_len))))
   = admit()

val frame_counterblocks_snoc: i:id{safeId i} -> (t:PRF.state i) -> (x:domain i{x.ctr <> 0ul}) -> k:nat{v x.ctr <= k} ->
			     len:nat{len <> 0 /\ safelen i len 1ul} -> 
			     (completed_len:nat{completed_len < len /\
				              FStar.Mul ((k - 1) * v (PRF.blocklen i) = completed_len)}) ->
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
		    safelen i completed_len 1ul))
          (ensures (let p0 = Plain.sel_plain h0 (u len) plain in
		    let c0 = Buffer.as_seq h0 cipher in
	    	    let p = Plain.sel_plain h1 (u len) plain in
		    let c = Buffer.as_seq h1 cipher in
		    let remaining_len = len - completed_len in
		    let next = minNat remaining_len (v (PRF.blocklen i)) in
		    let initial_x = {x with ctr=1ul} in
		    let initial_blocks = counterblocks i t.mac_rgn initial_x len 0 completed_len p0 c0 in
		    let final_blocks = counterblocks i t.mac_rgn initial_x len 0 (completed_len + next) p c in
	     	    let plain_last = Plain.slice p completed_len (completed_len + next) in
		    let cipher_last = Seq.slice c completed_len (completed_len + next) in
		    let last_entry = PRF.Entry ({x with ctr=UInt32.uint_to_t k})
	 				       (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last) in
		    final_blocks == SeqProperties.snoc initial_blocks last_entry))
let frame_counterblocks_snoc i t x k len completed_len plain cipher h0 h1 = 
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
  let initial_x = {x with ctr=1ul} in
  let initial_blocks = counterblocks i t.mac_rgn initial_x len 0 completed_len p0 c0 in
  let final_blocks = counterblocks i t.mac_rgn initial_x len 0 (completed_len + next) p c in
  counterblocks_snoc  #i t.mac_rgn initial_x k len next completed_len p c;
  counterblocks_slice #i t.mac_rgn initial_x len completed_len p c;
  counterblocks_slice #i t.mac_rgn initial_x len completed_len p0 c0


val extending_counter_blocks: #i:id -> (t:PRF.state i) -> (x:domain i{x.ctr <> 0ul}) ->
			     len:nat{len <> 0 /\ safelen i len 1ul} -> 
			     (completed_len:nat{completed_len < len /\
				              FStar.Mul ((v x.ctr - 1) * v (PRF.blocklen i) = completed_len)}) ->
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
	            modifies_x_buffer_1 t x cipher_hd h0 h1 /\
		    Buffer.disjoint (as_buffer plain) cipher /\
		    Buffer.frameOf (as_buffer plain) <> t.rgn /\
		    Buffer.frameOf cipher <> t.rgn /\
		    safelen i completed_len 1ul /\
		    none_above x t h0 /\
		    (safeId i ==> 
		       (let r = itable i t in
		        h0 `HS.contains` r /\
			HS.sel h0 t.table == 
			  Seq.append (HS.sel h_init t.table)
				     (counterblocks i t.mac_rgn ({x with ctr=1ul}) 
						 len 0 completed_len
						 (Plain.sel_plain h0 (u len) plain)
						 (Buffer.as_seq h0 cipher)) /\
	                ( match find_otp #t.mac_rgn #i (HS.sel h1 t.table) x with
			  | Some (OTP l' p c) -> u l = l' /\ p == sel_plain h1 (u l) plain_hd /\ c == sel_bytes h1 (u l) cipher_hd
			  | None   -> False )))))
          (ensures (let remaining_len = len - completed_len in
		    let l = minNat remaining_len (v (PRF.blocklen i)) in
		    let completed_len' = completed_len + l in
		    safeId i ==>
		      Seq.equal (HS.sel h1 t.table)
				(Seq.append (HS.sel h_init t.table) 
					    (counterblocks i t.mac_rgn ({x with ctr=1ul}) 
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
	 assert (suffix == last_entry);
	 frame_counterblocks_snoc i t x (v x.ctr) len completed_len plain cipher h0 h1
    end

