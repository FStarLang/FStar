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

unfold
let deref #a (h: HS.mem) (x: B.pointer a) =
  B.get h x 0

module M = LowStar.ModifiesPat // many people will forget about it, so add it here so that it appears in the dependencies, and so its patterns will be in the SMT verification context without polluting the F* scope

val blit
  (#t: Type)
  (src: B.buffer t)
  (idx_src: U32.t)
  (dst: B.buffer t)
  (idx_dst: U32.t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h ->
    B.live h src /\ B.live h dst /\ B.disjoint src dst /\
    U32.v idx_src + U32.v len <= B.length src /\
    U32.v idx_dst + U32.v len <= B.length dst
  ))
  (ensures (fun h _ h' ->
    M.modifies (M.loc_buffer dst) h h' /\
    B.live h' dst /\
    Seq.slice (B.as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
    Seq.slice (B.as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len) /\
    Seq.slice (B.as_seq h' dst) 0 (U32.v idx_dst) ==
    Seq.slice (B.as_seq h dst) 0 (U32.v idx_dst) /\
    Seq.slice (B.as_seq h' dst) (U32.v idx_dst + U32.v len) (B.length dst) ==
    Seq.slice (B.as_seq h dst) (U32.v idx_dst + U32.v len) (B.length dst)
  ))
let rec blit #t a idx_a b idx_b len =
  let h0 = HST.get () in
  if len = 0ul then ()
  else begin
    let len' = U32.(len -^ 1ul) in
    blit #t a idx_a b idx_b len';
    let z = U32.(a.(idx_a +^ len')) in
    b.(U32.(idx_b +^ len')) <- z;
    let h1 = HST.get() in
    Seq.snoc_slice_index (B.as_seq h1 b) (U32.v idx_b) (U32.v idx_b + U32.v len');
    Seq.cons_head_tail (Seq.slice (B.as_seq h0 b) (U32.v idx_b + U32.v len') (B.length b));
    Seq.cons_head_tail (Seq.slice (B.as_seq h1 b) (U32.v idx_b + U32.v len') (B.length b))
  end

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
