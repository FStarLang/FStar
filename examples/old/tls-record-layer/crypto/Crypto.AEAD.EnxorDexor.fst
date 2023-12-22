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
module Crypto.AEAD.EnxorDexor
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
open Crypto.AEAD.Encrypt.Invariant

module Cipher        = Crypto.Symmetric.Cipher
module PRF           = Crypto.Symmetric.PRF
module Plain         = Crypto.Plain
module Invariant     = Crypto.AEAD.Invariant
module HH            = FStar.HyperHeap
module HS            = FStar.HyperStack
module ST            = FStar.HyperStack.ST
module CMA           = Crypto.Symmetric.UF1CMA
module MAC           = Crypto.Symmetric.MAC
module Seq = FStar.Seq
module BufferUtils   = Crypto.AEAD.BufferUtils

(*** First, some predicates and lemmas
     shared between enxor and dexor **)

let separation (#i:id) 
	       (t:PRF.state i)
	       (#len:u32)
	       (plain:plainBuffer i (v len))
	       (cipher:lbuffer (v len)) =
    let bp = as_buffer plain in
    Buffer.disjoint bp cipher /\
    Buffer.frameOf bp <> (PRF.(t.rgn)) /\
    Buffer.frameOf cipher <> (PRF.(t.rgn))

let liveness (#i:id) 
	     (t:PRF.state i)
	     (#len:u32) 
	     (plain:plainBuffer i (v len))   
	     (cipher:lbuffer (v len))
	     (h:mem) =
    Plain.live h plain /\
    Buffer.live h cipher /\
    (prf i
      ==> h `HS.contains` (itable i t))

let iteration_lengths_ok (#i:id)
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

(*+ modifies_table_above_x_and_buffer: 
       A clause in the write effect counter_enxor and counter_dexor
	   -- modifies the prf table at domains at or above x
	      and a buffer b
	   -- in the case of enxor, b is the cipher buffer
	   -- in the case of dexor, b is the plain buffer
 **)
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
    HS.modifies_ref t.rgn (Set.singleton (FStar.Heap.addr_of (HS.as_ref r))) h0 h1 /\
    Buffer.modifies_buf_1 rb b h0 h1 /\
    Seq.length contents0 <= Seq.length contents1 /\
    Seq.equal (Seq.slice contents1 0 (Seq.length contents0)) contents0 /\
    all_above x (Seq.slice contents1 (Seq.length contents0) (Seq.length contents1))
  else
    (let rid = Buffer.frameOf b in
     HS.modifies_one rid h0 h1 /\ 
     Buffer.modifies_buf_1 rid b h0 h1))

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
let weaken_modifies (#i:id) (#l:nat) (t:PRF.state i)
		    (x:PRF.domain i) (b:lbuffer l)
		    (h0:HS.mem) (h1:HS.mem)
    : Lemma (requires (modifies_table_above_x_and_buffer t x b h0 h1))
	    (ensures (BufferUtils.enxor_modifies PRF.(t.rgn) b h0 h1))
    = ()

(*+ modifies_table_above_x_and_buffer is a pre-order, 
	as proven by the reflexivity and transitivity lemmas below *)
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
	cut (Seq.equal Seq.empty emp);
	FStar.Classical.forall_intro (Seq.contains_elim emp)
      else ()

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
	FStar.Classical.forall_intro (Seq.append_contains_equiv diff_01 diff_12)
      else ()

(*+ modifies_x_buffer_1 is the write effect of prf_enxor and prf_dexor, 
        which modifies the buffer and a single point x in the prf table.
	
        This lemma weakens that write effect to a write effect on all
        points above x in the table
 **)	
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
	FStar.Classical.forall_intro (Seq.contains_elim diff)
      else Buffer.lemma_reveal_modifies_1 c h_0 h_1

(*** Enxor specifics ***)

(*+ prf_enxor_leaves_none_strictly_above_x: 
	modifying a single point in the table 
	leaves those above it unchanged **)
val prf_enxor_leaves_none_strictly_above_x: 
  #i:id -> 
   t:PRF.state i ->
   x:domain i{ctr_0 i <^ x.ctr} ->
   len:u32 ->
   remaining_len:u32{safelen i (v remaining_len) x.ctr /\ 
		     remaining_len <> 0ul /\ remaining_len <=^ len} ->
   c:lbuffer (v len) ->
   h_0:mem ->
   h_1:mem ->
     Lemma (requires none_above_prf_st x t h_0 /\
		     modifies_x_buffer_1 t x c h_0 h_1 /\ 
		     Buffer.frameOf c <> t.rgn)
           (ensures none_above_prf_st (PRF.incr i x) t h_1)
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let prf_enxor_leaves_none_strictly_above_x #i t x len remaining_len c h_0 h_1
    = if prf i then
	let r = itable i t in
	let t_0 = HS.sel h_0 r in 
	let t_1 = HS.sel h_1 r in
	let ex = Seq.index t_1 (Seq.length t_0) in
	assert (PRF.is_entry_domain x ex);
	assert (Seq.equal t_1 (Seq.snoc t_0 ex));
	let rgn = t.mac_rgn in
	assert (find t_0 x == None);
	Seq.find_snoc t_0 ex (PRF.is_entry_domain x);
	assert (Some? (find t_1 x));
	assert (find t_1 x == Some ex.range);
	let y = PRF.incr i x in
	let aux (z:domain i{z `above` y})
	  : Lemma (find t_1 z == None)
	  = assert (z `above` x); 
	    Seq.find_snoc t_0 ex (PRF.is_entry_domain z) in
	FStar.Classical.forall_intro aux
      else ()

(*+ Working towards a main auxiliary lemma:  extending_counter_blocks **)

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 100"
(*+ frame_counterblocks_snoc:
	 modifying a single entry in the prf table and the cipher
	 carries counterblocks forward by snoc'ing a single OTP block **)
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
		    final_blocks == Seq.snoc initial_blocks last_entry))
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

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3rlimit 400"
(*+ extending_counter_blocks: 
	 A main auxiliary lemma
	 Shows that each iteration of counter_enxor extends the counterblocks
	 to include the block just encrypted, without touching existing blocks
  **)
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
			none_above_prf_st x t h0 /\
		        h0 `HS.contains` r /\
			HS.sel h0 (itable i t) ==
			  Seq.append (HS.sel h_init (itable i t))
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
		      Seq.equal (HS.sel h1 (itable i t))
				(Seq.append (HS.sel h_init (itable i t))
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
 	 let suffix = Seq.last r1 in
	 assert (Seq.equal r1 (Seq.snoc r0 suffix));
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

(*+ enxor_invariant: 
      An inductive invariant for counter_enxor 
      
      stated relative to h_init, 
      the initial memory before starting the loop

      and h, the per-iteration memory 
 **)
let enxor_invariant (#i:id) (t:PRF.state i) (x:PRF.domain i)
		    (len:u32) (remaining_len:u32)
		    (plain:plainBuffer i (v len))
		    (cipher:lbuffer (v len))
		    (h_init:mem) (h:mem) = 
  liveness t plain cipher h /\
  iteration_lengths_ok x len remaining_len /\
  (safeId i
      ==> (let prf_table = HS.sel h (itable i t) in
           let initial_domain = {x with ctr=ctr_0 i +^ 1ul} in
           let completed_len = len -^ remaining_len in
	   Seq.equal prf_table
    		     (Seq.append (HS.sel h_init (itable i t))
    				 (counterblocks i t.mac_rgn initial_domain
    				      (v len) 0 (v completed_len)
    				      (Plain.sel_plain h len plain)
    				      (Buffer.as_seq h cipher)))))

(*+ counter_enxor:
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
    separation t plain cipher /\
    liveness t plain cipher h /\
    iteration_lengths_ok x len remaining_len /\
    // if ciphertexts are authenticated, then fresh blocks are available
    (safeMac i ==> none_above_prf_st x t h) /\
    enxor_invariant t x len remaining_len plain cipher h_init h))
  (ensures (fun h0 _ h1 ->
    liveness t plain cipher h1 /\
    iteration_lengths_ok x len remaining_len /\
    // in all cases, we extend the table only at x and its successors.
    modifies_table_above_x_and_buffer t x cipher h0 h1 /\
    enxor_invariant t x len 0ul plain cipher h_init h1))
#set-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let rec counter_enxor #i t x len remaining_len plain cipher h_init =
  let completed_len = len -^ remaining_len in
  let h0 = get () in
  if remaining_len <> 0ul then
    begin // at least one more block
      let starting_pos = len -^ remaining_len in
      let l = min remaining_len (PRF.blocklen i) in
      let cipher_hd = Buffer.sub cipher starting_pos l in
      let plain_hd = Plain.sub plain starting_pos l in
      PRF.prf_enxor i t x l cipher_hd plain_hd;
      let h1 = get () in
      x_buffer_1_modifies_table_above_x_and_buffer t x cipher h0 h1;
      if safeMac i then prf_enxor_leaves_none_strictly_above_x t x len remaining_len cipher h0 h1;
      extending_counter_blocks t x (v len) (v completed_len) plain cipher h0 h1 h_init;
      let y = PRF.incr i x in
      counter_enxor t y len (remaining_len -^ l) plain cipher h_init;
      let h2 = get () in
      trans_modifies_table_above_x_and_buffer t x y cipher h0 h1 h2
    end
  else refl_modifies_table_above_x_and_buffer t x cipher h0

(*+ enxor: The main function exposed to clients for encryption **)
val enxor  :
         #i:id ->
         iv:Cipher.iv (Cipher.algi i) ->
    aead_st:aead_state i Writer ->
    #aadlen:aadlen -> 
        aad:lbuffer (v aadlen) ->
       #len:nz_ok_len_32 i ->
      plain:plainBuffer i (v len) ->
 cipher_tag:lbuffer (v len + v MAC.taglen) ->
         ak:CMA.state (i, iv) -> 
	 ST unit
  (requires (fun h ->
	     let x = {iv=iv; ctr=otp_offset i} in
	     let t = aead_st.prf in
	     HS.(is_stack_region h.tip) /\
	     enc_dec_separation aead_st aad plain cipher_tag /\
	     enc_dec_liveness aead_st aad plain cipher_tag h /\
	     inv aead_st h /\
             ak_live aead_st.prf.mac_rgn ak h /\
	     (safeMac i ==> 
       	         is_mac_for_iv aead_st ak h /\
		 fresh_nonce_st iv aead_st h /\
	         CMA.mac_is_unset (i, iv) aead_st.prf.mac_rgn ak h /\
		 none_above_prf_st x t h)))    // if ciphertexts are authenticated, then fresh blocks are available
   (ensures (fun h0 _ h1 ->
 	     let x = {iv=iv; ctr=otp_offset i} in
	     let t = aead_st.prf in
	     let cipher : lbuffer (v len) = Buffer.sub cipher_tag 0ul len in
	     enc_dec_liveness aead_st aad plain cipher_tag h1 /\
	     modifies_table_above_x_and_buffer t x cipher h0 h1 /\
	     enxor_invariant t x len 0ul plain cipher h0 h1 /\
             ak_live aead_st.prf.mac_rgn ak h1 /\	    
	     (safeMac i ==>
		 fresh_nonce_st iv aead_st h1 /\
      	         is_mac_for_iv aead_st ak h1 /\
	         CMA.mac_is_unset (i, iv) aead_st.prf.mac_rgn ak h1) /\
	         enxor_h0_h1 aead_st iv aad plain cipher_tag h0 h1))
let enxor #i iv aead_st #aadlen aad #len plain_b cipher_tag ak =
  let h_init = ST.get () in
  let x = {iv=iv; ctr=otp_offset i} in
  let t = aead_st.prf in
  let cipher_b : lbuffer (v len) = Buffer.sub cipher_tag 0ul len in
  let _ = 
    let plain = Plain.sel_plain h_init len plain_b in
    let cipher = Buffer.as_seq h_init cipher_b in
    counterblocks_emp i t.mac_rgn x (v len) 0 plain cipher;
    assert (safeId i ==> Seq.equal (HS.sel h_init (itable i t))
				   (Seq.append (HS.sel h_init (itable i t))
				 	        Seq.empty)) in
  let h0 = get () in 						
  counter_enxor t x len len plain_b cipher_b h_init;
  let h1 = get () in 
  if safeMac i then begin
    let prf = PRF.itable i aead_st.prf in 
    let tab_0 = HS.sel h0 prf in
    let tab_1 = HS.sel h1 prf in
    let suffix = Seq.slice tab_1 (Seq.length tab_0) (Seq.length tab_1) in
    assert (Seq.equal tab_1 (Seq.append tab_0 suffix));
    let x0 = {iv=iv; ctr=PRF.ctr_0 i} in
    lemma_prf_find_append_some tab_0 suffix x0
  end
  

(*** Dexor specifics ***)

(*+ dexor_modifies: 
	the write effect of dexor 
	  -- either just the plain buffer, if either not idealized or safe
	  -- or both the plain buffer and the prf table otherwise 
	     (since the attacker may call it anyway)
**)
let dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) (x:PRF.domain i) 
		   (pb:plainBuffer i (v len)) (h0:mem) (h1:mem) =
   if not (prf i) || safeId i
   then Buffer.modifies_1 (as_buffer pb) h0 h1
   else modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let dexor_of_prf_dexor_modifies (#i:id) (#len:u32) (t:PRF.state i) 
				(x:PRF.domain i{ctr_0 i <^ x.ctr}) 
				(pb:plainBuffer i (v len)) (h0:mem) (h1:mem)
   : Lemma (requires (prf_dexor_modifies t x pb h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then ()
     else x_buffer_1_modifies_table_above_x_and_buffer t x (as_buffer pb) h0 h1

(*+ dexor_modifies is a pre-order **)

(*+ reflexivity **)
let dexor_modifies_refl (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len)) (h0:mem)
   : Lemma (requires (Buffer.live h0 (as_buffer pb)))
	   (ensures (dexor_modifies t x pb h0 h0))
   = if not (prf i) || safeId i
     then ()
     else refl_modifies_table_above_x_and_buffer t x (as_buffer pb) h0

(*+ transitivity **)
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

(*+ dexor_modifies_widen: 
	weakening a modifies clause to cover a wider range of a buffer *)
let dexor_modifies_widen (#i:id) (#len:u32) (t:PRF.state i) 
			 (x:PRF.domain i{ctr_0 i <^ x.ctr}) 
			 (pb:plainBuffer i (v len))
                         (from:u32{FStar.Buffer.(v from + idx (Plain.as_buffer pb)) < pow2 n})
			 (len:u32{FStar.Buffer.(v len <= length (Plain.as_buffer pb) /\ 
				  v from + v len <= length (Plain.as_buffer pb))})
			 (h0:mem) (h1:mem)
   : Lemma (requires (Buffer.live h0 (Plain.as_buffer pb) /\ 
		      dexor_modifies t x (Plain.sub pb from len) h0 h1))
	   (ensures (dexor_modifies t x pb h0 h1))
   = if not (prf i) || safeId i
     then (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer (Plain.sub pb from len)) h0 h1;
           Buffer.lemma_intro_modifies_1 (Plain.as_buffer pb) h0 h1)
     else ()
     
(*+ decrypted_up_to: 
      A predicate relating the contents of the partially filled
      concrete plain buffer pb 
      to a fragment of the expected ideal plain text p **)
let decrypted_up_to (#i:id) (#len:u32) (completed:u32{completed <=^ len}) 
		    (pb:plainBuffer i (v len)) (p:maybe_plain i (v len)) 
		    (h:mem{Buffer.live h (as_buffer pb)}) =
  safeId i ==> 		    
    Seq.equal (as_bytes (Plain.slice (Plain.sel_plain h len pb) 0 (v completed)))
	      (as_bytes (Plain.slice (as_plain p) 0 (v completed)))

(*+ decrypted_up_to_end: 
      When filled completely, the concrete buffer contains 
      the expected plain text **)
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

(*+ prf_contains_all_otp_blocks_st: 
         A wrapper around prf_contains_all_otp_blocks, 
	 requiring it of the entire current prf table
 **)
let prf_contains_all_otp_blocks_st (#i:id)
 		 	   (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
			   (#len:nat)
			   (remaining_len:nat{remaining_len <= len /\ safelen i remaining_len x.ctr})
			   (plain:maybe_plain i len)
			   (cipher:lbuffer len)
			   (t:PRF.state i)
			   (h:mem)
   = let from_pos = len - remaining_len in
     safeId i /\ Buffer.live h cipher ==>				
     prf_contains_all_otp_blocks x from_pos
	 (as_plain plain)
	 (Buffer.as_seq h cipher)
	 (HS.sel h (PRF.itable i t))

(*+ frame_prf_contains_all_otp_blocks_st:
	if we have prf_contains_all_otp_blocks_st,
	and we call prf_dexor,
	then in the safeId case, it only modifies the plain buffer
    	not the prf table.
	So, we can restore prf_contains_all_otp_blocks_st
 **)
let frame_prf_contains_all_otp_blocks_st (#i:id) 
			      (x_init:PRF.domain i{PRF.ctr_0 i <^ x_init.ctr})
     			      (x:PRF.domain i{x `above` x_init})
			      (#len:u32)
			      (remaining_len:u32{remaining_len <=^ len /\ safelen i (v remaining_len) x.ctr})
			      (t:PRF.state i) 
			      (pb:plainBuffer i (v len))
			      (p:maybe_plain i (v len))
			      (cipher: lbuffer (v len))
			      (h0:mem)
    			      (h1:mem)
   : Lemma (requires (separation t pb cipher  /\
		      liveness t pb cipher h0 /\
		      prf_contains_all_otp_blocks_st x (v remaining_len) p cipher t h0 /\
                      prf_dexor_modifies t x_init pb h0 h1))
          (ensures  (liveness t pb cipher h1 /\
		     prf_contains_all_otp_blocks_st x (v remaining_len) p cipher t h1))
   = FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer pb) h0) h1


(*+ invert_prf_contains_all_otp_blocks_st:
	This is just an unfolding of prf_contains_all_otp_blocks
	using a unit of fuel for it. 
	Contexts that use 0 fuel must invoke this lemma to reason
	about prf_contains_all_otp_blocks
 **)
#reset-options "--z3rlimit 200 --initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"
val invert_prf_contains_all_otp_blocks_st 
    (i:id) 
    (x:PRF.domain i{PRF.ctr_0 i <^ x.ctr})
    (len:u32{len <> 0ul /\ safelen i (v len) (PRF.ctr_0 i +^ 1ul)})
    (remaining_len:u32{safelen i (v remaining_len) x.ctr /\ 
		       remaining_len <> 0ul /\ 
		       remaining_len <=^ len})
    (t:PRF.state i) 
    (p:maybe_plain i (v len))
    (cipher: lbuffer (v len))
    (h:mem{Buffer.live h cipher})
   : Lemma (requires (prf_contains_all_otp_blocks_st x (v remaining_len) p cipher t h))
 	   (ensures  (let starting_pos = len -^ remaining_len in
	              let l = min remaining_len (PRF.blocklen i) in
		      let cipher_hd = Buffer.sub cipher starting_pos l in 
		      safeId i ==> (
		       let plain_hd = Plain.slice (as_plain p) (v starting_pos) (v starting_pos + v l) in
		       let blocks = HS.sel h (PRF.itable i t) in
		       let c = Buffer.as_seq h cipher_hd in
		       PRF.contains_cipher_block (v l) x c blocks /\
       		       PRF.contains_plain_block x plain_hd blocks /\ 
		       prf_contains_all_otp_blocks_st (PRF.incr i x) (v (remaining_len -^ l)) p cipher t h)))
let invert_prf_contains_all_otp_blocks_st i x len remaining_len t p cipher h
   = if safeId i 
     then let prf_table = HS.sel h (PRF.itable i t) in
	  let cipher = Buffer.as_seq h cipher in
	  let plain = as_plain p in
	  let from_pos = v (len -^ remaining_len) in 
	  invert_prf_contains_all_otp_blocks x from_pos plain cipher prf_table

(*+ extend_decrypted_up_to: 
	A main auxiliary lemma for counter_dexor 
	If the prf table prf_contains_all_otp_blocks
	And we have partially filled the plain buffer with the expected plain
	Then an iteration of counter_dexor extends the plain buffer as expected 
 **)	
val extend_decrypted_up_to: #i:id -> (t:PRF.state i) -> (x:PRF.domain i) ->
			    #len:u32 -> remaining_len:u32{remaining_len_ok x len remaining_len} ->
			   (pb:plainBuffer i (v len)) ->
			   (p:maybe_plain i (v len)) ->
   			   (cipher:lbuffer (v len)) ->
			   (h0:mem) ->
			   (h1:mem) ->
      Lemma (requires (let starting_pos = len -^ remaining_len in
		       let l = min remaining_len (PRF.blocklen i) in
		       let plain = Plain.sub pb starting_pos l in
		       separation t pb cipher /\
		       liveness t pb cipher h0 /\
		       remaining_len <> 0ul /\
		       Plain.live h1 pb /\
		       prf_dexor_modifies t x plain h0 h1 /\
	               prf_contains_all_otp_blocks_st x (v remaining_len) p cipher t h0 /\
		       (safeId i ==> 
			   decrypted_up_to starting_pos pb p h0 /\
			   contains_plain_block x (sel_plain h1 l plain) (HS.sel h1 (PRF.itable i t)))))
	    (ensures (let starting_pos = len -^ remaining_len in
		      let l = min remaining_len (PRF.blocklen i) in
		      Plain.live h1 pb /\
		      (safeId i ==> 
			   decrypted_up_to (starting_pos +^ l) pb p h1)))
#reset-options "--z3rlimit 100 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
let extend_decrypted_up_to #i t x #len remaining_len pb p cipher h0 h1 = 
  let starting_pos = len -^ remaining_len in
  let l = min remaining_len (PRF.blocklen i) in
  let frame = Plain.sub pb 0ul starting_pos in
  let plain = Plain.sub pb starting_pos l in
  assert (Buffer.disjoint (Plain.as_buffer frame) (Plain.as_buffer plain));
  let next = starting_pos +^ l in
  if safeId i then begin
    Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0 h1;
    let pb_contents_0 = as_bytes (Plain.slice (Plain.sel_plain h0 len pb) 0 (v starting_pos)) in
    let p_contents_0  = as_bytes (Plain.slice (as_plain p) 0 (v starting_pos)) in
    let pb_contents_1 = as_bytes (Plain.slice (Plain.sel_plain h1 len pb) 0 (v next)) in
    let plain_contents_1 = as_bytes (Plain.sel_plain h1 l plain) in
    let frame_pb_contents_1 = as_bytes (Plain.slice (Plain.sel_plain h1 len pb) 0 (v starting_pos)) in
    assert (Seq.equal pb_contents_0 frame_pb_contents_1);
    assert (Seq.equal pb_contents_1 (Seq.append p_contents_0 plain_contents_1));
    invert_prf_contains_all_otp_blocks_st i x len remaining_len t p cipher h0
  end

(*+ dexor_requires:
	pre-condition for counter_dexor **)
let dexor_requires (#i:id) (t:PRF.state i) (x:PRF.domain i)
		   (#len:u32) (remaining_len:u32)
		   (plain:plainBuffer i (v len))
		   (cipher:lbuffer (v len))
		   (p:maybe_plain i (v len))
		   (h:mem) =
    remaining_len_ok x len remaining_len /\ (
    let bp = as_buffer plain in
    let initial_domain = {x with ctr=otp_offset i} in
    let completed_len = len -^ remaining_len in 
    separation t plain cipher /\
    liveness t plain cipher h /\
    // if ciphertexts are authenticated, then the table already includes all we need
    prf_contains_all_otp_blocks_st x (v remaining_len) p cipher t h /\
    //and the buffer is partially filled as expected
    (safeId i ==> decrypted_up_to completed_len plain p h))
      
let dexor_ensures (#i:id) (t:PRF.state i) (x:PRF.domain i)
		  (#len:u32)
		  (plain:plainBuffer i (v len))
		  (cipher:lbuffer (v len))
		  (p:maybe_plain i (v len))
		  (h0:mem) (h1:mem) = 
    liveness t plain cipher h1 /\		  
    // in all cases, we extend the table only at x and its successors.
    dexor_modifies t x plain h0 h1 /\
    (safeId i ==> 
       decrypted_up_to len plain p h1 /\
       //this clause seems unnecessary, except for perhaps simplifying some proofs
       Seq.equal (HS.sel h0 (PRF.itable i t)) (HS.sel h1 (PRF.itable i t)))

val counter_dexor:
  i:id -> t:PRF.state i -> x:PRF.domain i ->
  len:u32 -> remaining_len:u32 ->
  plain:plainBuffer i (v len) ->
  cipher:lbuffer (v len) ->
  p:maybe_plain i (v len) ->
  ST unit (requires (fun h -> dexor_requires t x remaining_len plain cipher p h))
 	  (ensures (fun h0 _ h1 -> dexor_ensures t x plain cipher p h0 h1))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
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

      invert_prf_contains_all_otp_blocks_st i x len remaining_len t p cipher h0;
      prf_dexor i t x l cipher_hd plain_hd;
      
      let h1 = get() in 
      let y = PRF.incr i x in
      frame_prf_contains_all_otp_blocks_st x y (remaining_len -^ l) t plain p cipher h0 h1;
      FStar.Classical.move_requires (FStar.Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0) h1;
      extend_decrypted_up_to t x remaining_len plain p cipher h0 h1;
      incr_remaining_len_ok x len remaining_len;

      counter_dexor i t y len (remaining_len -^ l) plain cipher p;

      let h2 = get () in
      dexor_of_prf_dexor_modifies t x plain_hd h0 h1;
      dexor_modifies_widen t x plain starting_pos l h0 h1;
      dexor_modifies_trans t x y plain h0 h1 h2;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h0) h1;
      FStar.Classical.move_requires (Buffer.lemma_reveal_modifies_1 (Plain.as_buffer plain) h1) h2
    end
   else dexor_modifies_refl t x plain h0

let decrypt_ok (#i:id) (n:Cipher.iv (Cipher.algi i)) (st:aead_state i Reader) 
	       (#aadlen:aadlen) (aad:lbuffer (v aadlen))
	       (#plainlen:Encoding.txtlen_32)
	       (plain:plainBuffer i (v plainlen))
	       (cipher_tagged:lbuffer (v plainlen + v MAC.taglen))
	       (h1:mem) =
  (enc_dec_liveness st aad plain cipher_tagged h1 /\
   safeId i) ==> (
   let aead_entries = HS.sel h1 (st_ilog st) in
   let aad = Buffer.as_seq h1 aad in
   let plain = Plain.sel_plain h1 plainlen plain in
   let cipher_tagged = Buffer.as_seq h1 cipher_tagged in 
   found_matching_entry n aead_entries #aadlen aad plain cipher_tagged)

(*+ found_entry: 
      the entry in the aead table corresponding to nonce n
      contains the expected aad, plain and cipher text
 **)
let found_entry (#i:id) (n:Cipher.iv (Cipher.algi i)) (st:aead_state i Reader)
		(#aadlen:aadlen) (aad:lbuffer (v aadlen)) 
	        (#plainlen:Encoding.txtlen_32)
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


let find_fresh_iv_none (#i:id) (#r:rid)
		       (st:aead_state i Reader)
		       (iv:Cipher.iv (Cipher.algi i))
		       (blocks:prf_table r i)
		       (h:mem{safeMac i /\ (
			      let aead_entries = HS.sel h (st_ilog st) in
			      let x_1 = {iv=iv; ctr=otp_offset i} in
			      ~(fresh_nonce iv aead_entries) /\
			      all_above x_1 blocks)})
		       (y:PRF.domain i)
  : Lemma (requires (fresh_nonce y.iv (HS.sel h (st_ilog st))))
          (ensures (PRF.find blocks y == None))
  = assert (y.iv <> iv);
    let x_1 = {iv=iv; ctr=otp_offset i} in
    find_other_iv_all_above blocks x_1 y

val dexor:
  #i:id ->
  st:aead_state i Reader ->
  iv:Cipher.iv (Cipher.algi i) ->
  #aadlen:aadlen -> aad:lbuffer (v aadlen) ->
  #len:Encoding.txtlen_32 ->
  plain:plainBuffer i (v len) ->
  cipher_tagged:lbuffer (v len + v MAC.taglen) ->
  p:maybe_plain i (v len) ->
  ST unit
  (requires (fun h ->
	    let x_1 = {iv=iv; ctr=otp_offset i} in
	    let t = st.prf in
	    let cipher : lbuffer (v len) = Buffer.sub cipher_tagged 0ul len in
	    enc_dec_separation st aad plain cipher_tagged /\
	    enc_dec_liveness st aad plain cipher_tagged h /\
	    inv st h /\
            len <> 0ul /\
	    safelen i (v len) (otp_offset i) /\
            prf_contains_all_otp_blocks_st x_1 (v len) p cipher t h /\
	    (safeMac i ==> ~(fresh_nonce iv (HS.sel h (st_ilog st)))) /\
	    found_entry iv st aad cipher_tagged p h))
  (ensures (fun h0 _ h1 ->
  	    let x_1 = {iv=iv; ctr=otp_offset i} in
	    enc_dec_liveness st aad plain cipher_tagged h1 /\
	    dexor_modifies st.prf x_1 plain h0 h1 /\
	    inv st h1 /\
	    decrypt_ok iv st aad plain cipher_tagged h1))
#reset-options "--z3rlimit 200 --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open Crypto.AEAD.Encoding 
let dexor #i st iv #aadlen aad #len plain cipher_tagged p =
  let x_1 = {iv=iv; ctr=otp_offset i} in
  let t = st.prf in
  let cipher : lbuffer (v len) = Buffer.sub cipher_tagged 0ul len in
  let h0 = get () in
  counter_dexor i t x_1 len len plain cipher p;
  let h1 = get () in
  decrypted_up_to_end plain p h1;
  if not (prf i) || safeId i
  then begin
    FStar.Buffer.lemma_reveal_modifies_1 (as_buffer plain) h0 h1;
    frame_inv_modifies_1 (as_buffer plain) st h0 h1
  end
  else if safeMac i
  then //re-establishing the invariant takes a bit of work;
       //basically, we know the iv is not fresh since verify succeeded
       //and we only modified entries for that iv, so we didn't impact any fresh nonces
       let aead_entries_0 = HS.sel #(aead_entries i) h0 (st_ilog st) in
       let aead_entries_1 = HS.sel #(aead_entries i) h1 (st_ilog st) in
       let prf_entries_1 = HS.sel h1 (PRF.itable i st.prf) in
       let prf_entries_0 = HS.sel h0 (PRF.itable i st.prf) in
       assert (aead_entries_1 == aead_entries_0);
       assert (HS.modifies_ref st.prf.mac_rgn Set.empty h0 h1);
       assert (fresh_nonces_are_unused prf_entries_0 aead_entries_1 h0);
       let open FStar.Classical in
       let h0':(h:mem{safeMac i}) = h0 in
       let h1':(h:mem{safeMac i}) = h1 in
       forall_intro (move_requires (frame_unused_aead_iv_for_prf_h h0' h1 prf_entries_0));
       assert (forall (iv:Cipher.iv (alg i)).{:pattern (fresh_nonce iv aead_entries_1)}
               fresh_nonce iv aead_entries_1 ==>
               unused_aead_iv_for_prf prf_entries_0 iv h1);
       let blocks = Seq.slice prf_entries_1 (Seq.length prf_entries_0) (Seq.length prf_entries_1) in
       assert (Seq.equal prf_entries_1 (Seq.append prf_entries_0 blocks)); //AR: this is a simpler Seq proof
       forall_intro (move_requires (find_fresh_iv_none st iv blocks h1));
       forall_intro (move_requires (frame_unused_aead_iv_for_prf_append prf_entries_0 blocks h1'));
       assert (fresh_nonces_are_unused prf_entries_1 aead_entries_1 h1)
