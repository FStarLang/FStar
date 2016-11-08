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

let find_entry_last (#i:id) (n:Cipher.iv (alg i)) (entries:Seq.seq (entry i){Seq.length entries > 0})
  : Lemma (let tl, last = SeqProperties.split entries (Seq.length entries - 1) in
	   let last = Seq.index last 0 in
           if last.nonce = n then 
	     find_entry n entries == Some last
	   else find_entry n entries == find_entry n tl)
  = let tl, last = SeqProperties.split entries (Seq.length entries - 1) in
    let last = Seq.index last 0 in
    if last.nonce = n then ()
    else admit() //seq_find is annoying to work with

// States consistency of the PRF table contents vs the AEAD entries
// (not a projection from one another because of allocated MACs and aad)
val refines_snoc: 
  h:mem -> 
  i:id {safeId i} -> rgn:region ->
  entries: Seq.seq (entry i) -> 
  blocks: Seq.seq (PRF.entry rgn i) -> GTot Type0
  (decreases (Seq.length entries))
let rec refines_snoc h i rgn entries blocks = 
  if Seq.length entries = 0 then 
    Seq.length blocks == 0 //NS:using == to get it to match with the Type returned by the other branch
  else let entries_prefix, es = SeqProperties.split entries (Seq.length entries - 1) in
       let e = Seq.index es 0 in
       let b = num_blocks e in 
       b < Seq.length blocks /\
       (let blocks_prefix, blocks_for_e = SeqProperties.split blocks (Seq.length blocks - (b + 1)) in
        refines_one_entry h e blocks_for_e /\
	refines_snoc h i rgn entries_prefix blocks_prefix)


#reset-options "--z3timeout 100 --initial_fuel 2 --max_fuel 2 --initial_ifuel 0 --max_ifuel 0"
(* refines_one_entry can be lifted refines sums block lengths *)
private let refines_snoc_singleton (h:mem) (i:id{safeId i}) (rgn:region) (e:entry i) (blocks_for_e:Seq.seq (PRF.entry rgn i))
  : Lemma (requires (refines_one_entry h e blocks_for_e))
	  (ensures (refines_snoc h i rgn (Seq.create 1 e) blocks_for_e))
  = let b = num_blocks e in 
    assert (Seq.equal (Seq.slice blocks_for_e (Seq.length blocks_for_e - (b + 1)) (Seq.length blocks_for_e))
	   	      blocks_for_e)

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3timeout 1000"
let rec refines_snoc_append (h:mem) (i:id {safeId i}) (rgn:region)
 			    (entries: Seq.seq (entry i))
			    (blocks: Seq.seq (PRF.entry rgn i))
			    (e:entry i) (bs: Seq.seq (PRF.entry rgn i))
       : Lemma (requires (refines_snoc h i rgn entries blocks /\
			  refines_one_entry h e bs))
	       (ensures  (refines_snoc h i rgn (SeqProperties.cons e entries)
					       (Seq.append bs blocks)))
               (decreases (Seq.length (entries)))						 
       = if Seq.length entries = 0 then 
	   (assert (Seq.equal (SeqProperties.cons e entries) (Seq.create 1 e));
	    assert (Seq.equal (Seq.append bs blocks) bs);
	    refines_snoc_singleton h i rgn e bs)
	 else let all_entries = SeqProperties.cons e entries in
	      let all_blocks = Seq.append bs blocks in 
	      let all_entries_prefix, all_entries_last_es = SeqProperties.split all_entries (Seq.length all_entries - 1) in
	      let entries_prefix, entries_last_es = SeqProperties.split entries (Seq.length entries - 1) in
	      let last_e = Seq.index entries_last_es 0 in
     	      assert (Seq.equal all_entries_last_es entries_last_es);
	      let b = num_blocks last_e in 
	      let blocks_prefix, blocks_for_last_e = SeqProperties.split blocks (Seq.length blocks - (b + 1)) in
	      let all_blocks_prefix, all_blocks_for_last_e = SeqProperties.split all_blocks (Seq.length all_blocks - (b + 1)) in
	      refines_snoc_append h i rgn entries_prefix blocks_prefix e bs;
	      assert (Seq.equal all_blocks_prefix (Seq.append bs blocks_prefix));
	      assert (Seq.equal all_entries_prefix (SeqProperties.cons e entries_prefix));
	      assert (Seq.equal all_blocks_for_last_e blocks_for_last_e)

let rec refines_refines_snoc (h:mem) (i:id {safeId i}) (rgn:region)
 			     (entries: Seq.seq (entry i))
			     (blocks: Seq.seq (PRF.entry rgn i))
     : Lemma (requires (refines h i rgn entries blocks))
	     (ensures (refines_snoc h i rgn entries blocks))
	     (decreases (Seq.length entries))
     = if Seq.length entries = 0
       then ()
       else let hd, tl = SeqProperties.split entries 1 in 
	    let hd = Seq.index entries 0 in
	    let n = num_blocks hd in 
	    let hd_blocks, blocks_tl = SeqProperties.split blocks (n + 1) in 
	    refines_refines_snoc h i rgn tl blocks_tl;
	    refines_snoc_append h i rgn tl blocks_tl hd hd_blocks;
	    assert (Seq.equal entries (SeqProperties.cons hd tl));
	    assert (Seq.equal blocks (Seq.append hd_blocks blocks_tl))

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100"
val false_elim : #a:Type -> u:unit{false} -> Tot a
let rec false_elim #a u = false_elim ()

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0 --z3timeout 1000"
let invert_refines_snoc (h:mem) (i:id {safeId i}) (rgn:region)
			(entries: Seq.seq (entry i)) (blocks: Seq.seq (PRF.entry rgn i))
   : Lemma (refines_snoc h i rgn entries blocks
	     <==>
	    ((Seq.length entries = 0 /\ Seq.length blocks = 0) \/ (
	     Seq.length entries > 0 /\ (
	     let entries_prefix, es = SeqProperties.split entries (Seq.length entries - 1) in
	     let e = Seq.index es 0 in
	     let b = num_blocks e in 
	     b < Seq.length blocks /\
	     (let blocks_prefix, blocks_for_e = SeqProperties.split blocks (Seq.length blocks - (b + 1)) in
             refines_one_entry h e blocks_for_e /\
	     refines_snoc h i rgn entries_prefix blocks_prefix)))))
   = ()

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 1000"
let find_blocks_append (#i:id) (#rgn:rid) (b:prf_blocks rgn i) (b':prf_blocks rgn i) (x:domain i) 
  : Lemma (requires (is_Some (find b' x)))
          (ensures (find (Seq.append b b') x == find b' x))
  = admit()


val find_entry_blocks:    (i:id) -> (rgn:rid) ->
			  (n:Cipher.iv (alg i){safeId i}) ->
			  (entries:aead_entries i) ->
			  (prf_entries:prf_blocks rgn i) ->
			  (h:mem{refines_snoc h i rgn entries prf_entries /\
			         is_Some (find_mac prf_entries ({iv=n; ctr=ctr_0 i}))}) ->
     Pure (entry i * prf_blocks rgn i)
          (requires True)
	  (ensures (fun (entry, blocks) ->
			let x0 = {iv=n; ctr=ctr_0 i} in
			refines_one_entry h entry blocks /\
			find_entry n entries == Some entry /\
			find_mac prf_entries x0 == Some (PRF.macRange rgn i x0 (Seq.index blocks 0).range)))
	  (decreases (Seq.length entries))
let rec find_entry_blocks i rgn n entries prf_entries h =
  let x0 = {iv=n; ctr=ctr_0 i} in
  let cur = Seq.length entries in 
  invert_refines_snoc h i rgn entries prf_entries;
  if cur = 0 
  then false_elim()
  else let ix = cur - 1 in 
       let e = Seq.index entries ix in
       let b = num_blocks e in 
       let blocks_prefix, blocks_for_e = SeqProperties.split prf_entries (Seq.length prf_entries - (b + 1)) in
       assert (Seq.equal prf_entries (Seq.append blocks_prefix blocks_for_e));
       assert (refines_one_entry h e blocks_for_e);
       let Entry nonce ad plainlen p c_tagged = e in
       let c, tag = SeqProperties.split c_tagged plainlen in
       let _ = find_entry_last n entries in
       if e.nonce = n then 
	 let _ = assert (find_entry n entries == Some e) in
	 let hd, tl = SeqProperties.split blocks_for_e 1 in
	 let hd = Seq.index hd 0 in
	 assert (Seq.equal (SeqProperties.cons hd tl) blocks_for_e);
	 let PRF.Entry x mac = hd in
	 assert (x == x0);
	 assert (tl == counterblocks i rgn (PRF.incr i x) plainlen 0 plainlen p c);
	 all_above_counterblocks i rgn (PRF.incr i x) plainlen 0 plainlen p c;
	 find_mac_counterblocks_none n tl;
	 assert (find #rgn #i tl x0 == None);
	 let finder (e:PRF.entry rgn i) = e.x = x0 in
	 assume (SeqProperties.seq_find finder tl == None); //TODO: this is silly... need to investigate
	 find_cons_hd hd tl finder;
	 assert (find blocks_for_e x0 == Some mac);
	 find_blocks_append blocks_prefix blocks_for_e x0;
	 (e, blocks_for_e)
       else let entries' = Seq.slice entries 0 (Seq.length entries - 1) in
	    assume (find_mac prf_entries x0 == find_mac blocks_prefix x0); //TODO, need to prove that find_mac blocks_prefix x0 = None
            find_entry_blocks i rgn n entries' blocks_prefix h
       

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

let fresh_frame_modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i)
			     (x:PRF.domain i{ctr_0 i <^ x.ctr})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (HS.fresh_frame h_0 h_1 /\ 
		       (* Buffer.live h_0 c /\ *)
		       (* (prf i ==> HS.contains h_0 (PRF.itable i t)) /\ *)
		       modifies_table_above_x_and_buffer t x c h_1 h_2))
	    (ensures (modifies_table_above_x_and_buffer t x c h_0 h_2))
    = admit()

let pop_frame_modifies_table_above_x_and_buffer (#i:id) (#l:nat) (t:PRF.state i)
			     (x:PRF.domain i{ctr_0 i <^ x.ctr})
			     (c:lbuffer l)
			     (h_0:mem) (h_1:mem) (h_2:mem)
    : Lemma (requires (modifies_table_above_x_and_buffer t x c h_0 h_1 /\ HS.poppable h_1 /\  h_2==HS.pop h_1))
	    (ensures (modifies_table_above_x_and_buffer t x c h_0 h_2))
    = admit()

//A generic sequence lemma to prove
let find_snoc (#a:Type) (s:Seq.seq a) (x:a) (f:a -> Tot bool)
  : Lemma (let res = SeqProperties.seq_find f (SeqProperties.snoc s x) in
	   match res with 
	   | None -> SeqProperties.seq_find f s == None /\ not (f x)
	   | Some y -> res == SeqProperties.seq_find f s \/ (f x /\ x==y))
  = admit()


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

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --z3timeout 100"
let prf_enxor_leaves_none_strictly_above_x #i t x len remaining_len c h_0 h_1
    = if safeId i then
	let r = itable i t in
	let t_0 = HS.sel h_0 r in 
	let t_1 = HS.sel h_1 r in
	let ex = Seq.index t_1 (Seq.length t_0) in
	assert (Seq.equal t_1 (SeqProperties.snoc t_0 ex));
	let rgn = t.mac_rgn in 
	assert (find t_0 x == None);
	find_snoc t_0 ex (fun (e:PRF.entry rgn i) -> e.x = x);
	assert (is_Some (find t_1 x));
	assert (find t_1 x == Some ex.range);
	let y = PRF.incr i x in 
	assert (find t_0 y == None)
      else ()
