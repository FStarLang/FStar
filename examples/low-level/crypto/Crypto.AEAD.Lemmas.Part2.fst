(* This module includes several lemmas to work with the 
   invariants defined in Crypto.AEAD.Invariant *)
module Crypto.AEAD.Lemmas.Part2
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

module Plain = Crypto.Plain
module PRF = Crypto.Symmetric.PRF

open Crypto.AEAD.Lemmas

let prf_blocks rgn i = Seq.seq (PRF.entry rgn i)
let aead_entries i = Seq.seq (entry i)

module Cipher = Crypto.Symmetric.Cipher

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3timeout 1000"
let invert_refines (h:mem) (i:id {safeId i}) (rgn:region)
		   (entries: Seq.seq (entry i)) (blocks: Seq.seq (PRF.entry rgn i))
   : Lemma (refines h i rgn entries blocks
	     <==>
	    ((Seq.length entries = 0 /\ Seq.length blocks = 0) \/ (
	     Seq.length entries > 0 /\ (
	     let e = SeqProperties.head entries in
	     let entries_tl = SeqProperties.tail entries in
	     let b = num_blocks e in 
	     b < Seq.length blocks /\
	     (let blocks_for_e, blocks_tl = SeqProperties.split blocks (b + 1) in
             refines_one_entry h e blocks_for_e /\
	     refines h i rgn entries_tl blocks_tl)))))
   = ()

let find_entry_first (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (entry i){Seq.length entries > 0})
  : Lemma (let head, tl = SeqProperties.head entries, SeqProperties.tail entries in
           if head.nonce = n then 
	     find_entry n entries == Some head
	   else find_entry n entries == find_entry n tl)
  = ()
  
val false_elim : #a:Type -> u:unit{false} -> Tot a
let rec false_elim #a u = false_elim ()

let from_x_blocks_included_in (#i:id) (#rgn:rid) (x:PRF.domain i) (blocks:prf_blocks rgn i) (blocks':prf_blocks rgn i) = 
  forall (y:PRF.domain i).{:pattern (find blocks y)}
       y `above` x /\
       v y.ctr <= v (ctr_0 i +^ 1ul) + Seq.length blocks
       ==> find blocks y == find blocks' y

let contains_all_blocks (#i:id) (#rgn:rid) (e:entry i) (blocks:prf_blocks rgn i) =
  let n = e.nonce in
  let x0 = {iv=n; ctr=ctr_0 i} in
  forall (y:domain i{y `above` x0 /\ v y.ctr <= v (ctr_0 i) + num_blocks e}). is_Some (find blocks y)

val find_entry_blocks:    (i:id) -> (rgn:rid) ->
			  (n:Cipher.iv (alg i){safeId i}) ->
			  (entries:aead_entries i) ->
			  (prf_entries:prf_blocks rgn i) ->
			  (h:mem{refines h i rgn entries prf_entries /\
			         is_Some (find_mac prf_entries ({iv=n; ctr=ctr_0 i}))}) ->
     Pure (entry i * prf_blocks rgn i)
          (requires True)
	  (ensures (fun (entry, blocks) ->
			let x0 = {iv=n; ctr=ctr_0 i} in
			entry.nonce = n /\
			refines_one_entry h entry blocks /\
			find_entry n entries == Some entry /\
			from_x_blocks_included_in (PRF.incr i x0) blocks prf_entries /\
			find_mac prf_entries x0 == Some (PRF.macRange rgn i x0 (Seq.index blocks 0).range)))
	  (decreases (Seq.length entries))
	  
#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100"
let rec find_entry_blocks i rgn n entries prf_entries h =
  let x0 = {iv=n; ctr=ctr_0 i} in
  let x1 = PRF.incr i x0 in
  invert_refines h i rgn entries prf_entries;
  if Seq.length entries = 0 
  then (find_is_some prf_entries x0; false_elim())
  else let e = SeqProperties.head entries in
       let b = num_blocks e in 
       let blocks_for_e, blocks_tl = SeqProperties.split prf_entries (b + 1) in
       assert (Seq.equal prf_entries (Seq.append blocks_for_e blocks_tl));
       assert (refines_one_entry h e blocks_for_e); //-- post-condition (1)
       let Entry nonce ad plainlen p c_tagged = e in
       let c, tag = SeqProperties.split c_tagged plainlen in
       find_entry_first n entries;
       if e.nonce = n then begin
	 assert (find_entry n entries == Some e); //-- post-condition (2)
	 assume (from_x_blocks_included_in x1 blocks_for_e prf_entries); //-- post-condition (3)
	 let hd, tl = SeqProperties.head blocks_for_e, SeqProperties.tail blocks_for_e in
	 assert (Seq.equal (SeqProperties.cons hd tl) blocks_for_e);
	 let PRF.Entry x mac = hd in
	 assert (x == x0);
	 assert (tl == counterblocks i rgn (PRF.incr i x) plainlen 0 plainlen p c);
	 find_cons_hd hd tl (PRF.is_entry_domain x0);
	 assert (find blocks_for_e x0 == Some mac);
	 find_blocks_append_l blocks_for_e blocks_tl x0; //-- post-condition (4)
	 (e, blocks_for_e)
       end
       else let tail = SeqProperties.tail entries in
	    assume (find_mac prf_entries x0 == find_mac blocks_tl x0);  //TODO: for pre-condition and for post-condition (4), via transitivity
	    let (e', blocks_for_e') = find_entry_blocks i rgn n tail blocks_tl h in
	    assume (from_x_blocks_included_in x1 blocks_for_e' prf_entries);    //TODO: for post-condition (3), via transitivity
	    (e', blocks_for_e')
	    //TODO, need to prove that find_mac blocks_prefix x0 = None
	    //Should be easy since we know that all of their nonces do not match n

(*** Lemmas about modifying tables and buffers ***)

let trans_all_above (#rgn:region) (#i:id) (s:Seq.seq (PRF.entry rgn i)) 
		    (x:PRF.domain i) (y:PRF.domain i{y `above` x})
    : Lemma (all_above s y ==> all_above s x)
    = ()

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
     Lemma (requires none_above x t h_0 /\
		     modifies_x_buffer_1 t x c h_0 h_1 /\ 
		     Buffer.frameOf c <> t.rgn)
           (ensures none_above (PRF.incr i x) t h_1)

module CMA = Crypto.Symmetric.UF1CMA

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100"
let prf_enxor_leaves_none_strictly_above_x #i t x len remaining_len c h_0 h_1
    = if CMA.authId (i, PRF x.iv) then
	let r = itable i t in
	let t_0 = HS.sel h_0 r in 
	let t_1 = HS.sel h_1 r in
	let ex = Seq.index t_1 (Seq.length t_0) in
	assert (PRF.is_entry_domain x ex);
	assert (Seq.equal t_1 (SeqProperties.snoc t_0 ex));
	let rgn = t.mac_rgn in
	assert (find t_0 x == None);
	find_snoc t_0 ex (PRF.is_entry_domain x);
	assert (is_Some (find t_1 x));
	assert (find t_1 x == Some ex.range);
	let y = PRF.incr i x in
	let aux (z:domain i{z `above` y}) 
	  : Lemma (find t_1 z == None) 
	  = find_snoc t_0 ex (PRF.is_entry_domain z) in
	FStar.Classical.forall_intro aux
      else ()
