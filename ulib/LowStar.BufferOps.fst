module LowStar.BufferOps

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq
module B = LowStar.Buffer

inline_for_extraction
val op_Array_Access: #a:Type -> b: B.buffer a -> n:U32.t{U32.v n< B.length b} -> HST.Stack a
     (requires (fun h -> B.live h b))
     (ensures (fun h0 z h1 -> h1 == h0
       /\ z == Seq.index (B.as_seq h0 b) (U32.v n)))
let op_Array_Access #a b n = B.index #a b n

inline_for_extraction
val op_Array_Assignment: #a:Type -> b: B.buffer a -> n:UInt32.t -> z:a -> HST.Stack unit
  (requires (fun h -> B.live h b /\ U32.v n < B.length b))
  (ensures (fun h0 _ h1 -> B.live h0 b /\ B.live h1 b /\ U32.v n < B.length b
    /\ B.modifies_1 b h0 h1
    /\ B.as_seq h1 b == Seq.upd (B.as_seq h0 b) (U32.v n) z ))
let op_Array_Assignment #a b n z = B.upd #a b n z

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
