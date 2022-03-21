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
 * 
 * We also keep msgs: list of all subsequences in the buffer that don't contain a 0ul
 *)
val hsl_state : Type0

(* abstract getters *)
val hsl_get_len (st:hsl_state) :u32
val hsl_get_buf (st:hsl_state) :Buffer.buffer u32
val hsl_get_p0 (st:hsl_state) :reference u32
val hsl_get_p1 (st:hsl_state) :reference u32
val hsl_get_msgs (st:hsl_state) :reference (list (u32 * u32))

(* Liveness and disjointness *)
[@"opaque_to_smt"]
unfold private let liveness_and_disjointness (st:hsl_state) (h:mem) :Type0 =
  let len, buf, p0, p1, msgs = hsl_get_len st, hsl_get_buf st, hsl_get_p0 st, hsl_get_p1 st, hsl_get_msgs st in
  
  loc_pairwise_disjoint [
    Mods.loc_mreference p0;
    Mods.loc_mreference p1;
    Mods.loc_buffer buf;
    Mods.loc_mreference msgs;
  ] /\

  Buffer.live h buf /\ contains h p0 /\ contains h p1 /\ contains h msgs /\  //liveness
  Buffer.len buf == len /\  //buffer length
  sel h p1 <=^ len /\  //p1 is leq len
  sel h p0 <=^ sel h p1  //p0 is leq p1

(*
 * An invariant on the sequence content between p0 and p1 in the buffer, that it doesn't contains 0ul
 *
 *)
[@"opaque_to_smt"]
unfold private let null_terminator_invariant_helper
  (buf:Buffer.buffer u32) (p0:u32) (p1:u32{p1 <=^ Buffer.len buf /\ p0 <=^ p1}) (h:mem)
  = let subseq_size = p1 -^ p0 in
    let subseq = Buffer.as_seq h (Buffer.gsub buf p0 subseq_size) in
    forall (i:nat). i < v subseq_size ==> Seq.index subseq i =!= 0ul

(* Lifted to hsl_state *)
[@"opaque_to_smt"]
unfold private let null_terminator_invariant (st:hsl_state) (h:mem{liveness_and_disjointness st h})
  = let buf, p0, p1 = hsl_get_buf st, sel h (hsl_get_p0 st), sel h (hsl_get_p1 st) in
    null_terminator_invariant_helper buf p0 p1 h

(*
 * An invariant on the list that all subsequences are 0ul free
 *)
[@"opaque_to_smt"]
unfold private let msgs_list_invariant_helper
  (buf:Buffer.buffer u32) (l:list (u32 * u32)) (p0:u32{p0 <=^ Buffer.len buf}) (h:mem)
  = forall (i j:u32). List.Tot.mem (i, j) l ==>  //if (i, j) is in the list
                 (i <^ j /\ j <^ p0 /\  //then both lie before p0
		  (let subseq_size = j -^ i in
		   let subseq = Buffer.as_seq h (Buffer.gsub buf i subseq_size) in
		   forall (k:nat). k < v subseq_size ==> Seq.index subseq k =!= 0ul))  //and no 0ul

(* Lifted to hsl_state *)
[@"opaque_to_smt"]
unfold private let msgs_list_invariant (st:hsl_state) (h:mem{liveness_and_disjointness st h})
  = let buf, p0, msgs = hsl_get_buf st, sel h (hsl_get_p0 st), sel h (hsl_get_msgs st) in
    msgs_list_invariant_helper buf msgs p0 h

(* Combine the predicates above *)
[@"opaque_to_smt"]
unfold private let hsl_invariant_predicate (st:hsl_state) (h:mem)
  = liveness_and_disjointness st h /\ null_terminator_invariant st h /\ msgs_list_invariant st h

(* Finally, the abstract invariant and its elimination *)
val hsl_invariant (st:hsl_state) (h:mem) : Type0

(*
 * This is a place where we can control what clients get to derive from the invariant
 * For now, we put everything in here
 *)
val lemma_hsl_invariant_elim (st:hsl_state) (h:mem)
  :Lemma (requires (hsl_invariant st h))
         (ensures  (hsl_invariant_predicate st h))
         [SMTPat (hsl_invariant st h)]

(*
 * HSL footprint = p0, p1, buffer contents between 0 and p1, and msgs
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
val lemma_frame_hsl_invariant (st:hsl_state) (l:loc) (h0 h1:mem)
  :Lemma (requires (hsl_invariant st h0                  /\
                    loc_disjoint l (hsl_footprint st h0) /\
		    Mods.modifies l h0 h1))
	 (ensures  (hsl_invariant st h1 /\ hsl_footprint st h1 == hsl_footprint st h0))

(*
 * Creating of HSL state
 *)
val hsl_create (len:u32{len >^ 0ul})
  :ST hsl_state (requires (fun h0       -> True))
                (ensures  (fun h0 st h1 -> Buffer.len (hsl_get_buf st) == len               /\
		                        hsl_invariant st h1                              /\
		                        fresh_loc (loc_buffer (hsl_get_buf st)) h0 h1    /\
					fresh_loc (loc_mreference (hsl_get_p0 st)) h0 h1 /\
					fresh_loc (loc_mreference (hsl_get_p1 st)) h0 h1 /\
					fresh_loc (loc_mreference (hsl_get_msgs st)) h0 h1 /\
		                        Mods.modifies loc_none h0 h1))

#set-options "--z3rlimit 16"

(*
 * Main process function that client (Record) calls once it has appended some data to the input buffer
 * It updates the p0 and p1 pointers, so that p1 points to p (the input index)
 * Also updates the msgs
 * And maintains the invariant
 *)
val hsl_process (st:hsl_state) (p:u32)
  :ST unit (requires (fun h0      -> hsl_invariant st h0 /\  //invariant holds
                                  p <=^ hsl_get_len st /\  //the new index up to which client wrote is in bounds
				  sel h0 (hsl_get_p1 st) <^ p))  //p1 < p, i.e. some new data is there
           (ensures  (fun h0 _ h1 -> hsl_invariant st h1 /\  //invariants holds again
	                          sel h1 (hsl_get_p1 st) == p /\  //p1 has been updated to p
	                          Mods.modifies (Mods.loc_union (Mods.loc_mreference (hsl_get_p0 st))
                                                (Mods.loc_union (Mods.loc_mreference (hsl_get_msgs st))
				                                (Mods.loc_mreference (hsl_get_p1 st)))) h0 h1))
