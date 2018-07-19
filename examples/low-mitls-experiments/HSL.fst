module HSL

(*
 * This module is a prototype of handshake log module in mitls
 *)

open LowStar.ModifiesPat

open FStar.UInt32

open FStar.HyperStack
open FStar.HyperStack.ST

module Mods   = LowStar.Modifies
module Buffer = LowStar.Buffer

module ST = FStar.HyperStack.ST

type u32 = UInt32.t

type loc = LowStar.Modifies.loc

(*
 * We currently model the reading side of TLS
 * HSL maintains a buffer, that record layer writes the incoming messages in
 * HSL also maintains two pointers in the buffer, p0 and p1
 * p0 represents the point until which HSL has parsed the incoming messages
 * Between p0 and p1 is the current, incomplete message
 * So, the record layer appends to the buffer after p1
 * At some point (in HSL.process), HSL decides that the contents between p0 and p1 is a valid message
 * And at that point, it moves p0 and p1
 * msgs is the list of all subsequences in the buffer that don't contain a 0ul
 *)
abstract noeq type hsl_state =
  | Mk_state: len:u32 ->
              buf:Buffer.buffer u32{Buffer.len buf == len} ->
              p0:reference u32 ->
	      p1:reference u32 ->
	      msgs:reference (list (u32 * u32)) ->
	      hsl_state

(* abstract getters *)
abstract let hsl_get_len (st:hsl_state) :u32 = st.len
abstract let hsl_get_buf (st:hsl_state) :Buffer.buffer u32 = st.buf
abstract let hsl_get_p0 (st:hsl_state) :reference u32 = st.p0
abstract let hsl_get_p1 (st:hsl_state) :reference u32 = st.p1
abstract let hsl_get_msgs (st:hsl_state) :reference (list (u32 * u32)) = st.msgs

[@"opaque_to_smt"]
unfold private let loc_pairwise_disjoint (s:TSet.set loc) :Type0 =
  forall (l1 l2:loc). TSet.mem l1 s ==> TSet.mem l2 s ==> Mods.loc_disjoint l1 l2

(* liveness and disjointness *)
[@"opaque_to_smt"]
unfold private let liveness_and_disjointness (st:hsl_state) (h:mem) :Type0 =
  let len, buf, p0, p1, msgs = hsl_get_len st, hsl_get_buf st, hsl_get_p0 st, hsl_get_p1 st, hsl_get_msgs st in
  
  //we used to have !{} syntax, which is now repurposed for Set, would be nice to have some such syntax for TSet
  loc_pairwise_disjoint (TSet.union (TSet.singleton (Mods.loc_mreference p0))
                                    (TSet.union (TSet.singleton (Mods.loc_mreference p1))
				                (TSet.union (TSet.singleton (Mods.loc_buffer buf))
						            (TSet.singleton (Mods.loc_mreference msgs))))) /\

  Buffer.live h buf /\ contains h p0 /\ contains h p1 /\ contains h msgs /\  //liveness
  Buffer.len buf == len /\  //buffer length
  sel h p0 <=^ len /\  //p0 and p1 invariants
  sel h p1 <=^ len /\
  sel h p0 <=^ sel h p1

(* an invariant on the sequence content between p0 and p1 in the buffer *)
[@"opaque_to_smt"]
unfold private let null_terminator_invariant_buf
  (len:u32) (buf:Buffer.buffer u32) (p0 p1:u32)
  (h:mem{Buffer.len buf == len /\ p1 <=^ len /\ p0 <=^ p1}) :GTot Type0
  = let subseq_size = p1 -^ p0 in
    let subseq = Buffer.as_seq h (Buffer.gsub buf p0 subseq_size) in
    forall (i:nat). i < v subseq_size ==> Seq.index subseq i =!= 0ul

[@"opaque_to_smt"]
unfold private let msgs_list_invariant_buf
  (len:u32) (buf:Buffer.buffer u32) (l:list (u32 * u32)) (p0:u32{p0 <=^ len})
  (h:mem{Buffer.len buf == len}) :GTot Type0
  = forall (i j:u32). List.Tot.mem (i, j) l ==>
                 (i <^ j /\ j <^ p0 /\
		  (let subseq_size = j -^ i in
		   let subseq = Buffer.as_seq h (Buffer.gsub buf i subseq_size) in
		   forall (k:nat). k < v subseq_size ==> Seq.index subseq k =!= 0ul))

(* an invariant on the sequence content between p0 and p1 in the buffer *)
[@"opaque_to_smt"]
unfold private let null_terminator_invariant (st:hsl_state) (h:mem{liveness_and_disjointness st h}) :GTot Type0 
  = let buf, p0, p1 = hsl_get_buf st, sel h (hsl_get_p0 st), sel h (hsl_get_p1 st) in
    null_terminator_invariant_buf (hsl_get_len st) buf p0 p1 h

(* an invariant on the list of indices *)
[@"opaque_to_smt"]
unfold private let msgs_list_invariant (st:hsl_state) (h:mem{liveness_and_disjointness st h}) :GTot Type0 
  = let len, buf, p0, msgs = hsl_get_len st, hsl_get_buf st, sel h (hsl_get_p0 st), sel h (hsl_get_msgs st) in
    msgs_list_invariant_buf len buf msgs p0 h

[@"opaque_to_smt"]
unfold private let hsl_invariant_predicate (st:hsl_state) (h:mem) :Type0 =
  liveness_and_disjointness st h /\
  null_terminator_invariant st h /\
  msgs_list_invariant st h

(* finally, the abstract invariant and its elimination *)
abstract let hsl_invariant (st:hsl_state) (h:mem) :Type0 = hsl_invariant_predicate st h

let lemma_hsl_invariant_elim (st:hsl_state) (h:mem)
  :Lemma (requires (hsl_invariant st h))
         (ensures  (hsl_invariant_predicate st h))
         [SMTPat (hsl_invariant st h)]
  = ()

(*
 * HSL footprint = p0, p1, and the buffer contents between p0 and p1 
 * This is not abstract, so that the client (Record) can append the buffer after p1, and use the framing lemma
 *)
let hsl_footprint (st:hsl_state) (h:mem{hsl_invariant st h}) =
  loc_union (loc_union (loc_buffer (Buffer.gsub (hsl_get_buf st) 0ul (sel h (hsl_get_p1 st))))
		       (loc_mreference (hsl_get_p0 st)))
	    (loc_union (loc_mreference (hsl_get_p1 st))
	               (loc_mreference (hsl_get_msgs st)))

(*
 * Framing the HSL invariant across its footprint
 *)
#set-options "--z3rlimit 30"
let lemma_frame_hsl_invariant (st:hsl_state) (l:loc) (h0 h1:mem)
  :Lemma (requires (hsl_invariant st h0                  /\
                    loc_disjoint l (hsl_footprint st h0) /\
		    Mods.modifies l h0 h1))
	 (ensures  (hsl_invariant st h1 /\ hsl_footprint st h1 == hsl_footprint st h0))
	 [SMTPat (hsl_invariant st h0); SMTPat (loc_disjoint l (hsl_footprint st h0));
	  SMTPat (Mods.modifies l h0 h1)]
  = let buf, p0', p1, msgs = hsl_get_buf st, hsl_get_p0 st, hsl_get_p1 st, hsl_get_msgs st in

    let b0 = Buffer.as_seq h0 buf in
    let b1 = Buffer.as_seq h0 buf in
    let p0 = v (sel h0 p0') in
    let p1 = v (sel h0 p1) in

    let msgs0 = sel h0 msgs in
    let msgs1 = sel h1 msgs in
    assert (msgs0 == msgs1);

    //we need this to prove the uncommented part below, essentially that the buffer
    //contents did not change between p0 and p1
    //we have buffer contents did not change from 0 to p1,
    //it is a bit unfortunate that from that we can't SMT derive between p0 to p1
    assert (forall (k:nat). k < p1 ==> Seq.index b0 k == Seq.index (Seq.slice b0 0 p1) k);
    assert (forall (i j:nat) (k:nat). (i < j /\ j < p0 /\ k < (j - i)) ==>
                              Seq.index (Seq.slice b0 i j) k == Seq.index (Seq.slice b1 i j) k)
    // assert (Seq.equal (Buffer.as_seq h0 (Buffer.gsub buf (sel h0 p0) (sel h0 p1 -^ sel h0 p0)))
    //                   (Buffer.as_seq h1 (Buffer.gsub buf (sel h1 p0) (sel h1 p1 -^ sel h1 p0))))

assume val fresh_loc: Mods.loc -> mem -> mem -> Type0

#reset-options
(*
 * Creating of HSL state
 * Assuming freshness and disjointness for now
 *)
let hsl_create (len:u32{len >^ 0ul})
  :ST hsl_state (requires (fun h0       -> True))
                (ensures  (fun h0 st h1 -> Buffer.len (hsl_get_buf st) == len               /\
		                        hsl_invariant st h1                              /\
		                        fresh_loc (loc_buffer (hsl_get_buf st)) h0 h1    /\
					fresh_loc (loc_mreference (hsl_get_p0 st)) h0 h1 /\
					fresh_loc (loc_mreference (hsl_get_p1 st)) h0 h1 /\
					fresh_loc (loc_mreference (hsl_get_msgs st)) h0 h1 /\
		                        Mods.modifies loc_none h0 h1))
  = let h0 = ST.get () in
    let buf = Buffer.gcmalloc root 0ul len in
    let p0 = ralloc root 0ul in
    let p1 = ralloc root 0ul in
    let msgs = ralloc root [] in
    let h2 = ST.get () in
    let st = Mk_state len buf p0 p1 msgs in
    assume (fresh_loc (loc_buffer (hsl_get_buf st)) h0 h2);
    assume (fresh_loc (loc_mreference (hsl_get_p0 st)) h0 h2);
    assume (fresh_loc (loc_mreference (hsl_get_p1 st)) h0 h2);
    assume (fresh_loc (loc_mreference (hsl_get_msgs st)) h0 h2);
    assume (loc_pairwise_disjoint (TSet.union (TSet.singleton (Mods.loc_mreference p0))
                                              (TSet.union (TSet.singleton (Mods.loc_mreference p1))
				                          (TSet.union (TSet.singleton (Mods.loc_buffer buf))
							              (TSet.singleton (Mods.loc_mreference msgs))))));
    st

(*
 * Auxiliary function for processing the buffer, skip ahead
 *)
private let rec aux_process (len:u32) (b:Buffer.buffer u32) (p0 p1 p:u32) (l:list (u32 * u32))
  :ST (u32 * list (u32 * u32))
      (requires (fun h0 -> Buffer.live h0 b /\
                        len == Buffer.len b /\ p <=^ len /\ p1 <=^ p /\ p0 <=^ p1 /\
                        null_terminator_invariant_buf len b p0 p1 h0 /\
			msgs_list_invariant_buf len b l p0 h0))
      (ensures  (fun h0 (r, l) h1 -> Buffer.live h1 b /\ 
	                          r <=^ p /\
				  null_terminator_invariant_buf len b r p h1 /\
				  msgs_list_invariant_buf len b l r h1 /\
	                          Mods.modifies loc_none h0 h1))
  = if p = p1 then p0, l
    else
      let c = Buffer.index b p1 in
      if c = 0ul then
        if p0 = p1 then aux_process len b (p1 +^ 1ul) (p1 +^ 1ul) p l
        else aux_process len b (p1 +^ 1ul) (p1 +^ 1ul) p ((p0, p1)::l)
      else aux_process len b p0 (p1 +^ 1ul) p l

(*
 * Main process function that client (Record) calls once it has appended some data to the input buffer
 * It updates the p0 and p1 pointers, so that p1 points to p (the input index)
 * And maintains the invariant
 *)
let hsl_process (st:hsl_state) (p:u32)
  :ST unit (requires (fun h0      -> hsl_invariant st h0 /\  //invariant holds
                                  p <=^ hsl_get_len st /\  //the new index upto which client wrote is in bounds
				  sel h0 (hsl_get_p1 st) <^ p))  //p1 < p, i.e. some new data is there
           (ensures  (fun h0 _ h1 -> hsl_invariant st h1 /\  //invariants holds again
	                          sel h1 (hsl_get_p1 st) == p /\  //p1 has been updated to p
	                          Mods.modifies (Mods.loc_union (Mods.loc_mreference (hsl_get_p0 st))
				                                (Mods.loc_mreference (hsl_get_p1 st))) h0 h1))
  = let len, buf, p0, p1, msgs = hsl_get_len st, hsl_get_buf st, hsl_get_p0 st, hsl_get_p1 st, hsl_get_msgs st in
    let new_p0, new_msgs = aux_process len buf (!p0) (!p1) p (!msgs) in
    p0 := new_p0;
    p1 := p;
    msgs := new_msgs
