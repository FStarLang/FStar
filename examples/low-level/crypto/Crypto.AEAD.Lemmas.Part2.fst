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
