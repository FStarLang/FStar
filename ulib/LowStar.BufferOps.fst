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

inline_for_extraction unfold
let op_Array_Access
  (#a: Type0) (#rrel: Seq.seq_pre a) (#rel: Seq.seq_pre a) (b: B.mbuffer a rrel rel) (i: U32.t) =
  B.index b i

inline_for_extraction unfold
let op_Array_Assignment
  (#a: Type0) (#rrel: Seq.seq_pre a) (#rel: Seq.seq_pre a) (b: B.mbuffer a rrel rel) (i: U32.t)
  (v: a) = B.upd b i v

(* NOTE: DO NOT mark ( !* ) as inline_for_extraction,
   because it is specially treated by KreMLin to extract as *p instead
   of p[0] *)
let op_Bang_Star (#a: Type0) (#rrel: Seq.seq_pre a) (#rel: Seq.seq_pre a) (p: B.mpointer a rrel rel)
  : HST.Stack a
    (requires (fun h -> B.live h p))
    (ensures (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) = B.index p 0ul

(* NOTE: DO NOT mark ( *= ) as inline_for_extraction,
   because it is specially treated by KreMLin to extract as *p = v instead
   of p[0] = v *)
let op_Star_Equals
  (#a: Type0) (#rrel: Seq.seq_pre a) (#rel: Seq.seq_pre a) (p: B.mpointer a rrel rel) (v: a)
  : HST.Stack unit
    (requires (fun h -> B.live h p /\ rel (B.as_seq h p) (Seq.upd (B.as_seq h p) 0 v)))
    (ensures
      (fun h0 _ h1 ->
          B.live h1 p /\ Seq.equal (B.as_seq h1 p) (Seq.create 1 v) /\
          B.modifies (B.loc_buffer p) h0 h1)) = B.upd p 0ul v

// TODO: remove

inline_for_extraction
let blit
  (#a: Type0) (#rrel1: Seq.seq_pre a) (#rrel2: Seq.seq_pre a) (#rel1: Seq.seq_pre a)
  (#rel2: Seq.seq_pre a) (src: B.mbuffer a rrel1 rel1) (idx_src: U32.t)
  (dst: B.mbuffer a rrel2 rel2) (idx_dst: U32.t) (len: U32.t) = B.blit src idx_src dst idx_dst len

