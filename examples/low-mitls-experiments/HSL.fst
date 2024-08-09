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
noeq type hsl_state =
  | Mk_state: len:u32 ->
              buf:Buffer.buffer u32{Buffer.len buf == len} ->
              p0:reference u32 ->
	      p1:reference u32 ->
	      msgs:reference (list (u32 & u32)) ->
	      hsl_state

(* abstract getters *)
let hsl_get_len (st:hsl_state) :u32 = st.len
let hsl_get_buf (st:hsl_state) :Buffer.buffer u32 = st.buf
let hsl_get_p0 (st:hsl_state) :reference u32 = st.p0
let hsl_get_p1 (st:hsl_state) :reference u32 = st.p1
let hsl_get_msgs (st:hsl_state) :reference (list (u32 & u32)) = st.msgs

(* Finally, the abstract invariant and its elimination *)
let hsl_invariant (st:hsl_state) (h:mem) = hsl_invariant_predicate st h

(*
 * This is a place where we can control what clients get to derive from the invariant
 * For now, we put everything in here
 *)
let lemma_hsl_invariant_elim (st:hsl_state) (h:mem)
  :Lemma (requires (hsl_invariant st h))
         (ensures  (hsl_invariant_predicate st h))
         [SMTPat (hsl_invariant st h)]
  = ()

(*
 * Framing the HSL invariant across its footprint
 *)
let lemma_frame_hsl_invariant (st:hsl_state) (l:loc) (h0 h1:mem)
  :Lemma (requires (hsl_invariant st h0                  /\
                    loc_disjoint l (hsl_footprint st h0) /\
		    Mods.modifies l h0 h1))
	 (ensures  (hsl_invariant st h1 /\ hsl_footprint st h1 == hsl_footprint st h0))
  = ()

(*
 * Creating of HSL state
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
    let h00 = ST.get () in
    let p0 = ralloc root 0ul in
    let p1 = ralloc root 0ul in
    let msgs = ralloc root [] in
    let h2 = ST.get () in
    let st = Mk_state len buf p0 p1 msgs in
    st

(*
 * Auxiliary function for processing the buffer
 *
 * Processes the buffer between p1 and p, one at a time
 * Returns new p0, and updated list of indices
 *)
private let rec aux_process (b:Buffer.buffer u32) (p0 p1 p:u32) (l:list (u32 & u32))
  :ST (u32 & list (u32 & u32))
      (requires (fun h0 -> Buffer.live h0 b /\
                        p <=^ Buffer.len b /\ p1 <=^ p /\ p0 <=^ p1 /\
                        null_terminator_invariant_helper b p0 p1 h0 /\
			msgs_list_invariant_helper b l p0 h0))
      (ensures  (fun h0 (r, l) h1 -> Buffer.live h1 b /\ 
	                          r <=^ p /\
				  null_terminator_invariant_helper b r p h1 /\
				  msgs_list_invariant_helper b l r h1 /\
	                          Mods.modifies loc_none h0 h1))
  = if p = p1 then p0, l  //done
    else
      let c = Buffer.index b p1 in
      if c = 0ul then  //found a 0
        if p0 = p1 then aux_process b (p1 +^ 1ul) (p1 +^ 1ul) p l  //if the subsequence is empty, just go ahead
        else aux_process b (p1 +^ 1ul) (p1 +^ 1ul) p ((p0, p1)::l)  //else add it to the list
      else aux_process b p0 (p1 +^ 1ul) p l

#set-options "--z3rlimit 16"

(*
 * Main process function that client (Record) calls once it has appended some data to the input buffer
 * It updates the p0 and p1 pointers, so that p1 points to p (the input index)
 * Also updates the msgs
 * And maintains the invariant
 *)
let hsl_process (st:hsl_state) (p:u32)
  :ST unit (requires (fun h0      -> hsl_invariant st h0 /\  //invariant holds
                                  p <=^ hsl_get_len st /\  //the new index upto which client wrote is in bounds
				  sel h0 (hsl_get_p1 st) <^ p))  //p1 < p, i.e. some new data is there
           (ensures  (fun h0 _ h1 -> hsl_invariant st h1 /\  //invariants holds again
	                          sel h1 (hsl_get_p1 st) == p /\  //p1 has been updated to p
	                          Mods.modifies (Mods.loc_union (Mods.loc_mreference (hsl_get_p0 st))
                                                (Mods.loc_union (Mods.loc_mreference (hsl_get_msgs st))
				                                (Mods.loc_mreference (hsl_get_p1 st)))) h0 h1))
  = let len, buf, p0, p1, msgs = hsl_get_len st, hsl_get_buf st, hsl_get_p0 st, hsl_get_p1 st, hsl_get_msgs st in
    let new_p0, new_msgs = aux_process buf !p0 !p1 p !msgs in
    p0 := new_p0;
    p1 := p;
    msgs := new_msgs
