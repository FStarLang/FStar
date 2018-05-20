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

inline_for_extraction
unfold
let op_Array_Access = B.index

inline_for_extraction
unfold
let op_Array_Assignment = B.upd

(* NOTE: DO NOT mark ( !* ) as inline_for_extraction,
   because it is specially treated by KreMLin to extract as *p instead
   of p[0] *)
let ( !* ) (#a: Type) (p: B.pointer a):
  HST.Stack a
  (requires (fun h -> B.live h p))
  (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) =
  B.index p 0ul

(* NOTE: DO NOT mark ( *= ) as inline_for_extraction,
   because it is specially treated by KreMLin to extract as *p = v instead
   of p[0] = v *)
let ( *= ) (#a: Type) (p: B.pointer a) (v: a) : HST.Stack unit
  (requires (fun h -> B.live h p))
  (ensures (fun h0 _ h1 ->
    B.live h1 p /\
    B.as_seq h1 p `Seq.equal` Seq.create 1 v /\
    B.modifies_1 p h0 h1
  ))
= B.upd p 0ul v

module M = LowStar.Modifies // many people will forget about it, so add it here so that it appears in the dependencies, and so its patterns will be in the SMT verification context without polluting the F* scope
