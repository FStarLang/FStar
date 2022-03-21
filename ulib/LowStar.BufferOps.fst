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
module LowStar.BufferOps

(* Handy notations for LowStar.Buffer, so users can open this module
   instead of the whole LowStar.Buffer, to just bring these operators
   and notations into the scope without bringing any definition from
   LowStar.Buffer into the scope. *)

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq
module B = LowStar.Buffer
module L = FStar.List.Tot

inline_for_extraction
unfold
let op_Array_Access (#a:Type0) (#rrel #rel:B.srel a) = B.index #a #rrel #rel

inline_for_extraction
unfold
let op_Array_Assignment (#a:Type0) (#rrel #rel:B.srel a) = B.upd #a #rrel #rel

(* NOTE: DO NOT mark ( !* ) as inline_for_extraction,
   because it is specially treated by KaRaMeL to extract as *p instead
   of p[0] *)
let ( !* ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel):
  HST.Stack a
  (requires (fun h -> B.live h p))
  (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) =
  B.index p 0ul

(* NOTE: DO NOT mark ( *= ) as inline_for_extraction,
   because it is specially treated by KaRaMeL to extract as *p = v instead
   of p[0] = v *)
let ( *= ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel) (v:a) : HST.Stack unit
  (requires (fun h -> B.live h p /\ rel (B.as_seq h p) (Seq.upd (B.as_seq h p) 0 v)))
  (ensures (fun h0 _ h1 ->
    B.live h1 p /\
    B.as_seq h1 p `Seq.equal` Seq.create 1 v /\
    B.modifies (B.loc_buffer p) h0 h1
  ))
= B.upd p 0ul v

// TODO: remove

inline_for_extraction
let blit (#a:Type0) (#rrel1 #rel1 #rrel2 #rel2:B.srel a) = B.blit #a #rrel1 #rel1 #rrel2 #rel2
