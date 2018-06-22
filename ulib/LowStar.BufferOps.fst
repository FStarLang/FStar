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
module MP = LowStar.ModifiesPat

/// TODO: remove two assumptions + make this meta-evaluate properly
inline_for_extraction
let rec assign_list #a (l: list a) (b: B.buffer a): HST.Stack unit
  (requires (fun h0 ->
    B.live h0 b /\
    B.length b = L.length l))
  (ensures (fun h0 _ h1 ->
    B.live h1 b /\
    M.(modifies (loc_buffer b) h0 h1) /\
    B.as_seq h1 b == Seq.of_list l))
=
  match l with
  | [] ->
      let h = HST.get () in
      assert (B.length b = 0);
      assert (Seq.length (B.as_seq h b) = 0);
      assert (Seq.equal (B.as_seq h b) (Seq.empty #a));
      assume (Seq.of_list [] == Seq.empty #a)
  | hd :: tl ->
      let b_hd = B.sub b 0ul 1ul in
      let b_tl = B.offset b 1ul in
      let h = HST.get () in
      b_hd.(0ul) <- hd;
      let h0 = HST.get () in
      assign_list tl b_tl;
      let h1 = HST.get () in
      assert B.(as_seq h1 b_hd == as_seq h0 b_hd);
      assert (B.get h1 b_hd 0 == hd);
      assert (B.as_seq h1 b_tl == Seq.of_list tl);
      assert (Seq.equal (B.as_seq h1 b) (Seq.append (B.as_seq h1 b_hd) (B.as_seq h1 b_tl)));
      assume (Seq.equal (Seq.of_list l) (Seq.cons hd (Seq.of_list tl)))
