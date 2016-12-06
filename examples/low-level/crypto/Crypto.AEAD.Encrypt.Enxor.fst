module Crypto.AEAD.Encrypt.Enxor

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
open Crypto.AEAD.Invariant

module PRF = Crypto.Symmetric.PRF
module Plain = Crypto.Plain
module Invariant = Crypto.AEAD.Invariant
module HH = FStar.HyperHeap
module HS = FStar.HyperStack
module CMA = Crypto.Symmetric.UF1CMA
module SeqProperties = FStar.SeqProperties

(*** THE WRITE EFFECT OF COUNTER_ENXOR ***)
let modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i)
				      (x:PRF.domain i) (b:lbuffer l)
				      (h0:HS.mem) (h1:HS.mem) =
  Buffer.live h1 b /\
  (if prf i then
    let r = PRF.itable i t in
    let rb = Buffer.frameOf b in
    let rgns = Set.union (Set.singleton #HH.rid t.rgn) (Set.singleton #HH.rid rb) in
    let contents0 = HS.sel h0 r in
    let contents1 = HS.sel h1 r in
    HS.modifies rgns h0 h1 /\
    HS.modifies_ref t.rgn (TSet.singleton (FStar.Heap.Ref (HS.as_ref r))) h0 h1 /\
    Buffer.modifies_buf_1 rb b h0 h1 /\
    Seq.length contents0 <= Seq.length contents1 /\
    Seq.equal (Seq.slice contents1 0 (Seq.length contents0)) contents0 /\
    all_above x (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1))
  else
    Buffer.modifies_1 b h0 h1)

let refl_modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i) 
			     (x:PRF.domain i{x.ctr <> 0ul}) 
			     (c:lbuffer l)
			     (h:mem)
    : Lemma (requires (Buffer.live h c))
	    (ensures (modifies_table_above_x_and_buffer t x c h h))
    = if prf i then 
	let r = itable i t in
	let c0 = HS.sel h r in
	let emp = Seq.slice c0 (Seq.length c0) (Seq.length c0) in
	cut (Seq.equal Seq.createEmpty emp);
	FStar.Classical.forall_intro (SeqProperties.contains_elim emp)
      else ()

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let trans_modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i) 
			     (x_0:PRF.domain i{x_0.ctr <> 0ul}) (x_1:PRF.domain i{x_1 `above` x_0})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (modifies_table_above_x_and_buffer t x_0 c h_0 h_1 /\ 
		       modifies_table_above_x_and_buffer t x_1 c h_1 h_2))
	    (ensures (modifies_table_above_x_and_buffer t x_0 c h_0 h_2))
    = if prf i then
        let r = itable i t in 
        let c0 = HS.sel h_0 r in
	let c1 = HS.sel h_1 r in
	let c2 = HS.sel h_2 r in
	let diff_01 = Seq.slice c1 (Seq.length c0) (Seq.length c1) in
	let diff_12 = Seq.slice c2 (Seq.length c1) (Seq.length c2) in
	let diff_02 = Seq.slice c2 (Seq.length c0) (Seq.length c2) in
	assert (Seq.equal diff_02 (Seq.append diff_01 diff_12));
	FStar.Classical.forall_intro (SeqProperties.append_contains_equiv diff_01 diff_12)
      else ()

let x_buffer_1_modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i) 
			     (x:PRF.domain i{ctr_0 i <^ x.ctr})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem)
    : Lemma (requires (modifies_x_buffer_1 t x c h_0 h_1))
	    (ensures  (modifies_table_above_x_and_buffer t x c h_0 h_1))
    = if prf i then
        let r = itable i t in
        let c0 = HS.sel h_0 r in
      	let c1 = HS.sel h_1 r in
	let diff = Seq.slice c1 (Seq.length c0) (Seq.length c1) in
	FStar.Classical.forall_intro (SeqProperties.contains_elim diff)
      else ()
  
val prf_enxor_leaves_none_strictly_above_x: #i:id -> 
					   t:PRF.state i ->
					   x:domain i{ctr_0 i <^ x.ctr} ->
					   len:u32 ->
  					   remaining_len:u32{safelen i (v remaining_len) x.ctr /\ remaining_len <> 0ul /\ remaining_len <=^ len} ->
					   c:lbuffer (v len) ->
					   h_0:mem ->
					   h_1:mem ->
     Lemma (requires none_above_if_authId x t h_0 /\
		     modifies_x_buffer_1 t x c h_0 h_1 /\ 
		     Buffer.frameOf c <> t.rgn)
           (ensures none_above_if_authId (PRF.incr i x) t h_1)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let prf_enxor_leaves_none_strictly_above_x #i t x len remaining_len c h_0 h_1
    = if CMA.authId (i, PRF.(x.iv)) then
	let r = itable i t in
	let t_0 = HS.sel h_0 r in 
	let t_1 = HS.sel h_1 r in
	let ex = Seq.index t_1 (Seq.length t_0) in
	assert (PRF.is_entry_domain x ex);
	assert (Seq.equal t_1 (SeqProperties.snoc t_0 ex));
	let rgn = t.mac_rgn in
	assert (find t_0 x == None);
	SeqProperties.find_snoc t_0 ex (PRF.is_entry_domain x);
	assert (Some? (find t_1 x));
	assert (find t_1 x == Some ex.range);
	let y = PRF.incr i x in
	let aux (z:domain i{z `above` y}) 
	  : Lemma (find t_1 z == None) 
	  = SeqProperties.find_snoc t_0 ex (PRF.is_entry_domain z) in
	FStar.Classical.forall_intro aux
      else ()

#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val counterblocks_snoc: #i:id{safeId i} -> (rgn:region) -> (x:domain i{ctr_0 i <^ x.ctr}) -> (k:nat{v x.ctr <= k}) ->
			 (len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)})  ->
			 (next:nat{0 < next /\ next <= v (PRF.blocklen i)}) ->
			 (completed_len:nat{ completed_len + next <= len /\ 
					   FStar.Mul.((k - v (otp_offset i)) * v (PRF.blocklen i) = completed_len)}) ->
			 (plain:Plain.plain i len) ->
			 (cipher:lbytes len) ->
     Lemma (requires True)
	   (ensures
	     (let open FStar.Mul in
	      let plain_last = Plain.slice plain completed_len (completed_len + next) in
	      let cipher_last = Seq.slice cipher completed_len (completed_len + next) in
	      let from = (v x.ctr - (v (otp_offset i))) * v (PRF.blocklen i) in
	      Seq.equal (counterblocks i rgn x len from (completed_len + next) plain cipher)
			(SeqProperties.snoc (counterblocks i rgn x len from completed_len plain cipher)
							   (PRF.Entry ({x with ctr=UInt32.uint_to_t k}) 
							              (PRF.OTP (UInt32.uint_to_t next) plain_last cipher_last)))))
	   (decreases (completed_len - v x.ctr))
#reset-options "--z3rlimit 400 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
let rec counterblocks_snoc #i rgn x k len next completed_len plain cipher =
   let open FStar.Mul in
   let from_pos = (v x.ctr - (v (otp_offset i))) * v (PRF.blocklen i) in
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
          SeqProperties.lemma_cons_snoc head middle last_entry //REVIEW: THIS PROOF TAKES A WHILE ...optimize

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
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
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

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
val frame_counterblocks_snoc: i:id{safeId i} -> (t:PRF.state i) -> (x:domain i{ctr_0 i <^ x.ctr}) -> k:nat{v x.ctr <= k} ->
			     len:nat{len <> 0 /\ safelen i len (ctr_0 i +^ 1ul)} -> 
			     (completed_len:nat{completed_len < len /\
				              FStar.Mul.((k - v (otp_offset i)) * v (PRF.blocklen i) = completed_len)}) ->
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
				              FStar.Mul.((v x.ctr - v (otp_offset i)) * v (PRF.blocklen i) = completed_len)}) ->
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
		    (safeId i ==> 
		       (let r = itable i t in
			let blocks_1 = HS.sel h1 (PRF.itable i t) in
			none_above_if_authId x t h0 /\
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

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 400"
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

(*** THE MAIN FUNCTION PROVIDED:
     counter_enxor ***)
let enxor_separation (#i:id) 
		     (t:PRF.state i)
		     (#len:u32)
		     (plain:plainBuffer i (v len))
		     (cipher:lbuffer (v len)) =
    let bp = as_buffer plain in
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF.(t.rgn)) /\
    Buffer.frameOf cipher <> (PRF.(t.rgn))

let enxor_liveness (#i:id) 
		   (t:PRF.state i)
		   (#len:u32) 
		   (plain:plainBuffer i (v len))   
		   (cipher:lbuffer (v len))
		   (h:mem) =
    Plain.live h plain /\
    Buffer.live h cipher /\
    (safeId i
      ==> (let r = itable i t in
	   h `HS.contains` r))

let enxor_dexor_lengths_ok (#i:id)
			   (x:PRF.domain i)
			   (len:u32)
			   (remaining_len:u32) = 
    len <> 0ul /\ 
    remaining_len <=^ len /\
    (let completed_len = len -^ remaining_len in			   
     PRF.ctr_0 i <^ x.ctr /\
     safelen i (v len) (PRF.ctr_0 i +^ 1ul) /\
     safelen i (v remaining_len) PRF.(x.ctr) /\ 
     (remaining_len <> 0ul ==> 
       FStar.Mul.((v x.ctr - v (otp_offset i)) * v (PRF.blocklen i) = v completed_len)))

let enxor_invariant (#i:id) (t:PRF.state i) (x:PRF.domain i)
		    (len:u32) (remaining_len:u32)
		    (plain:plainBuffer i (v len))
		    (cipher:lbuffer (v len))
		    (h_init:mem) (h:mem) = 
  enxor_liveness t plain cipher h /\
  enxor_dexor_lengths_ok x len remaining_len /\
  (safeId i
      ==> (let prf_table = HS.sel h (itable i t) in
           let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
           let completed_len = len -^ remaining_len in
	   Seq.equal prf_table
    		     (Seq.append (HS.sel h_init t.table)
    				 (counterblocks i t.mac_rgn initial_domain
    				      (v len) 0 (v completed_len)
    				      (Plain.sel_plain h len plain)
    				      (Buffer.as_seq h cipher)))))

(** counter_enxor:
      COUNTER_MODE LOOP from Chacha20
      XOR-based encryption and decryption (just swap ciphertext and plaintext)
      prf i    ==> writing at most at indexes x and above (same iv, higher ctr) at the end of the PRF table.
      safeId i ==> appending *exactly* "counterblocks i x l plain cipher" at the end of the PRF table
 **)
val counter_enxor:
  #i:id ->
  t:PRF.state i ->
  x:PRF.domain i ->
  len:u32 ->
  remaining_len:u32 ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len) ->
  h_init:mem ->
  // Not Stack, as we modify the heap-based ideal table (and don't know where the buffers are
  ST unit
  (requires (fun h ->
    enxor_separation t plain cipher /\
    enxor_liveness t plain cipher h /\
    enxor_dexor_lengths_ok x len remaining_len /\
    // if ciphertexts are authenticated, then fresh blocks are available
    none_above_if_authId x t h /\
    enxor_invariant t x len remaining_len plain cipher h_init h))
  (ensures (fun h0 _ h1 ->
    enxor_liveness t plain cipher h1 /\
    enxor_dexor_lengths_ok x len remaining_len /\
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x cipher h0 h1 /\
    enxor_invariant t x len 0ul plain cipher h_init h1))
#set-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec counter_enxor #i t x len remaining_len plain cipher h_init =
  let completed_len = len -^ remaining_len in
  let h0 = get () in
  if safeId i then ST.recall (itable i t);
  if remaining_len <> 0ul then
    begin // at least one more block
      let starting_pos = len -^ remaining_len in
      let l = min remaining_len (PRF.blocklen i) in
      let cipher_hd = Buffer.sub cipher starting_pos l in
      let plain_hd = Plain.sub plain starting_pos l in
      PRF.prf_enxor i t x l cipher_hd plain_hd;
      let h1 = get () in
      x_buffer_1_modifies_table_above_x_and_buffer t x cipher h0 h1;
      prf_enxor_leaves_none_strictly_above_x t x len remaining_len cipher h0 h1;
      extending_counter_blocks t x (v len) (v completed_len) plain cipher h0 h1 h_init;
      let y = PRF.incr i x in
      counter_enxor t y len (remaining_len -^ l) plain cipher h_init;
      let h2 = get () in
      trans_modifies_table_above_x_and_buffer t x y cipher h0 h1 h2
    end
  else refl_modifies_table_above_x_and_buffer t x cipher h0
  
