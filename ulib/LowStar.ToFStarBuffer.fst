module LowStar.ToFStarBuffer

(* WARNING: FOR TRANSITIONAL PURPOSES ONLY *)

module Old = FStar.Buffer
module OldM = FStar.Modifies
module New = LowStar.Buffer
module NewM = LowStar.Modifies
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

assume val new_to_old_ghost (#t: Type0) (b: New.buffer t) : GTot (Old.buffer t)
assume val old_to_new_ghost (#t: Type0) (b: Old.buffer t) : GTot (New.buffer t)

assume val new_to_old_st (#t: Type0) (b: New.buffer t) : HST.Stack (Old.buffer t)
  (requires (fun h -> New.live h b))
  (ensures (fun h b' h' -> h' == h /\ b' == new_to_old_ghost b))

assume val old_to_new_st (#t: Type0) (b: Old.buffer t) : HST.Stack (New.buffer t)
  (requires (fun h -> Old.live h b))
  (ensures (fun h b' h' -> h' == h /\ b' == old_to_new_ghost b))

assume val new_to_old_to_new (#t: Type0) (b: New.buffer t) : Lemma
  (old_to_new_ghost (new_to_old_ghost b) == b)
  [SMTPat (old_to_new_ghost (new_to_old_ghost b))]

assume val old_to_new_to_old (#t: Type0) (b: Old.buffer t) : Lemma
  (new_to_old_ghost (old_to_new_ghost b) == b)
  [SMTPat (new_to_old_ghost (old_to_new_ghost b))]

assume val live_new_to_old (#t: Type0) (h: HS.mem) (b: New.buffer t) : Lemma
  (Old.live h (new_to_old_ghost b) <==> New.live h b)
  [SMTPat (Old.live h (new_to_old_ghost b))]

assume val live_old_to_new (#t: Type0) (h: HS.mem) (b: Old.buffer t) : Lemma
  (New.live h (old_to_new_ghost b) <==> Old.live h b)
  [SMTPat (New.live h (old_to_new_ghost b))]

assume val frameOf_new_to_old (#t: Type0) (b: New.buffer t) : Lemma
  (Old.frameOf (new_to_old_ghost b) == New.frameOf b)
  [SMTPat (Old.frameOf (new_to_old_ghost b))]

assume val frameOf_old_to_new (#t: Type0) (b: Old.buffer t) : Lemma
  (New.frameOf (old_to_new_ghost b) == Old.frameOf b)
  [SMTPat (New.frameOf (old_to_new_ghost b))]

assume val as_addr_new_to_old (#t: Type0) (b: New.buffer t) : Lemma
  (Old.as_addr (new_to_old_ghost b) == New.as_addr b)
  [SMTPat (Old.as_addr (new_to_old_ghost b))]

assume val as_addr_old_to_new (#t: Type0) (b: Old.buffer t) : Lemma
  (New.as_addr (old_to_new_ghost b) == Old.as_addr b)
  [SMTPat (New.as_addr (old_to_new_ghost b))]

assume val length_new_to_old (#t: Type0) (b: New.buffer t) : Lemma
  (Old.length (new_to_old_ghost b) == New.length b)
  [SMTPat (Old.length (new_to_old_ghost b))]

assume val length_old_to_new (#t: Type0) (b: Old.buffer t) : Lemma
  (New.length (old_to_new_ghost b) == Old.length b)
  [SMTPat (New.length (old_to_new_ghost b))]

assume val as_seq_new_to_old (#t: Type0) (h: HS.mem) (b: New.buffer t) : Lemma
  (Old.as_seq h (new_to_old_ghost b) == New.as_seq h b)
  [SMTPat (Old.as_seq h (new_to_old_ghost b))]

assume val as_seq_old_to_new (#t: Type0) (h: HS.mem) (b: Old.buffer t) : Lemma
  (New.as_seq h (old_to_new_ghost b) == Old.as_seq h b)
  [SMTPat (New.as_seq h (old_to_new_ghost b))]

assume val gsub_new_to_old (#t: Type0) (b: New.buffer t) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= New.length b))
  (ensures (Old.sub (new_to_old_ghost b) i len == new_to_old_ghost (New.gsub b i len)))
  [SMTPatOr [
    [SMTPat (Old.sub (new_to_old_ghost b) i len)];
    [SMTPat (new_to_old_ghost (New.gsub b i len))];
  ]]

assume val gsub_old_to_new (#t: Type0) (b: Old.buffer t) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= Old.length b))
  (ensures (New.gsub (old_to_new_ghost b) i len == old_to_new_ghost (Old.sub b i len)))
  [SMTPatOr [
    [SMTPat (New.gsub (old_to_new_ghost b) i len)];
    [SMTPat (old_to_new_ghost (Old.sub b i len))];
  ]]

assume val new_to_old_includes_left (#t: Type0) (b1: New.buffer t) (b2: Old.buffer t) : Lemma
  ((new_to_old_ghost b1 `Old.includes` b2) <==> (b1 `New.includes` (old_to_new_ghost b2)))
  [SMTPatOr [
    [SMTPat (new_to_old_ghost b1 `Old.includes` b2)];
    [SMTPat (b1 `New.includes` old_to_new_ghost b2)];
  ]]

assume val new_to_old_includes_right (#t: Type0) (b1: Old.buffer t) (b2: New.buffer t) : Lemma
  ((b1 `Old.includes` (new_to_old_ghost b2)) <==> (old_to_new_ghost b1 `New.includes` b2))
  [SMTPatOr [
    [SMTPat (b1 `Old.includes` new_to_old_ghost b2)];
    [SMTPat (old_to_new_ghost b1 `New.includes` b2)];
  ]]

assume val new_to_old_disjoint (#t: Type0) (b1: New.buffer t) (b2: Old.buffer t) : Lemma
  ((new_to_old_ghost b1 `Old.disjoint` b2) <==> (b1 `New.disjoint` (old_to_new_ghost b2)))
  [SMTPatOr [
    [SMTPat (new_to_old_ghost b1 `Old.disjoint` b2)];
    [SMTPat (b1 `New.disjoint` old_to_new_ghost b2)];
  ]]

(* The modifies clause *)

module M = FStar.ModifiesGen

noextract
let old_and_new_aloc (is_new: bool) : Tot M.aloc_t =
  if is_new then M.raise_aloc New.abuffer else OldM.cloc_aloc

noextract
let old_and_new_cl (is_new: bool) : Tot (M.cls (old_and_new_aloc is_new)) =
  if is_new then M.raise_cls NewM.cloc_cls else OldM.cloc_cls

noextract
let old_and_new_cl_union : M.cls (M.aloc_union old_and_new_aloc) = M.cls_union old_and_new_cl

assume val loc_buffer_new_to_old (#t: Type0) (b: New.buffer t) : Lemma
  (M.union_loc_of_loc
     old_and_new_cl
     false
     (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b)))
   ==
   M.union_loc_of_loc
     old_and_new_cl
     true
     (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b))))

let modifies_0_modifies (h h' : HS.mem) : Lemma
  (requires (Old.modifies_0 h h'))
  (ensures (NewM.modifies NewM.loc_none h h'))
  [SMTPat (Old.modifies_0 h h')]
= OldM.modifies_to_cloc OldM.loc_none h h';
  OldM.cloc_of_loc_none ();
  M.modifies_union_loc_of_loc old_and_new_cl false M.loc_none h h';
  M.union_loc_of_loc_none old_and_new_cl false;
  M.union_loc_of_loc_none old_and_new_cl true;
  M.modifies_union_loc_of_loc old_and_new_cl true M.loc_none h h';
  M.raise_loc_none #_ #NewM.cloc_cls;
  M.modifies_raise_loc #_ #NewM.cloc_cls M.loc_none h h';
  NewM.cloc_of_loc_none ();
  NewM.modifies_to_cloc NewM.loc_none h h'

let modifies_1_modifies
  (#t: Type)
  (b: New.buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (Old.modifies_1 (new_to_old_ghost b) h h'))
  (ensures (NewM.modifies (NewM.loc_buffer b) h h'))
  [SMTPat (Old.modifies_1 (new_to_old_ghost b) h h')]
= OldM.modifies_to_cloc (OldM.loc_buffer (new_to_old_ghost b)) h h';
  M.modifies_union_loc_of_loc old_and_new_cl false (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b))) h h';
  loc_buffer_new_to_old b;
  M.modifies_union_loc_of_loc old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b))) h h';
  M.modifies_raise_loc #_ #NewM.cloc_cls (NewM.cloc_of_loc (NewM.loc_buffer b)) h h';
  NewM.modifies_to_cloc (NewM.loc_buffer b) h h'

let modifies_2_modifies
  (#t1 #t2: Type)
  (b1: New.buffer t1)
  (b2: New.buffer t2)
  (h h' : HS.mem)
: Lemma
  (requires (Old.modifies_2 (new_to_old_ghost b1) (new_to_old_ghost b2) h h'))
  (ensures (NewM.modifies (NewM.loc_union (NewM.loc_buffer b1) (NewM.loc_buffer b2)) h h'))
  [SMTPat (Old.modifies_2 (new_to_old_ghost b1) (new_to_old_ghost b2) h h')]
= OldM.modifies_to_cloc (OldM.loc_union (OldM.loc_buffer (new_to_old_ghost b1)) (OldM.loc_buffer (new_to_old_ghost b2))) h h';
  OldM.cloc_of_loc_union (OldM.loc_buffer (new_to_old_ghost b1)) (OldM.loc_buffer (new_to_old_ghost b2));
  M.modifies_union_loc_of_loc old_and_new_cl false (M.loc_union (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b1))) (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b2)))) h h';
  M.union_loc_of_loc_union old_and_new_cl false (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b1))) (OldM.cloc_of_loc (OldM.loc_buffer (new_to_old_ghost b2)));
  loc_buffer_new_to_old b1;
  loc_buffer_new_to_old b2;
  M.union_loc_of_loc_union old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b1))) (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b2)));
  M.modifies_union_loc_of_loc old_and_new_cl true (M.loc_union (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b1))) (M.raise_loc (NewM.cloc_of_loc (NewM.loc_buffer b2)))) h h';
  M.raise_loc_union (NewM.cloc_of_loc (NewM.loc_buffer b1)) (NewM.cloc_of_loc (NewM.loc_buffer b2));
  M.modifies_raise_loc #_ #NewM.cloc_cls (M.loc_union (NewM.cloc_of_loc (NewM.loc_buffer b1)) (NewM.cloc_of_loc (NewM.loc_buffer b2))) h h';
  NewM.cloc_of_loc_union (NewM.loc_buffer b1) (NewM.loc_buffer b2);
  NewM.modifies_to_cloc (NewM.loc_union (NewM.loc_buffer b1) (NewM.loc_buffer b2)) h h'

(* Examples *)

let new_eqb
  (#a: eqtype)
  (b1 b2: New.buffer a)
  (len: U32.t)
: HST.Stack bool
  (requires (fun h -> New.live h b1 /\ New.live h b2 /\ U32.v len <= New.length b1 /\ U32.v len <= New.length b2))
  (ensures (fun h res h' ->
    h' == h /\
    (res <==> Seq.equal (New.as_seq h (New.gsub b1 0ul len)) (New.as_seq h (New.gsub b2 0ul len)))
  ))
= let b1' = new_to_old_st b1 in
  let b2' = new_to_old_st b2 in
  Old.eqb b1' b2' len

let new_blit
  (#t: Type)
  (src: New.buffer t)
  (idx_src: U32.t)
  (dst: New.buffer t)
  (idx_dst: U32.t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h ->
    New.live h src /\ New.live h dst /\ New.disjoint src dst /\
    U32.v idx_src + U32.v len <= New.length src /\
    U32.v idx_dst + U32.v len <= New.length dst
  ))
  (ensures (fun h _ h' ->
    NewM.modifies (NewM.loc_buffer dst) h h' /\
    New.live h' dst /\
    Seq.slice (New.as_seq h' dst) (U32.v idx_dst) (U32.v idx_dst + U32.v len) ==
    Seq.slice (New.as_seq h src) (U32.v idx_src) (U32.v idx_src + U32.v len) /\
    Seq.slice (New.as_seq h' dst) 0 (U32.v idx_dst) ==
    Seq.slice (New.as_seq h dst) 0 (U32.v idx_dst) /\
    Seq.slice (New.as_seq h' dst) (U32.v idx_dst + U32.v len) (New.length dst) ==
    Seq.slice (New.as_seq h dst) (U32.v idx_dst + U32.v len) (New.length dst)
  ))
= let src' = new_to_old_st src in
  let dst' = new_to_old_st dst in
  Old.blit src' idx_src dst' idx_dst len

let new_fill
  (#t: Type)
  (b: New.buffer t)
  (z: t)
  (len: U32.t)
: HST.Stack unit
  (requires (fun h -> New.live h b /\ U32.v len <= New.length b))
  (ensures (fun h _ h' ->
    NewM.modifies (NewM.loc_buffer b) h h' /\
    Seq.slice (New.as_seq h' b) 0 (U32.v len) == Seq.create (U32.v len) z /\
    Seq.slice (New.as_seq h' b) (U32.v len) (New.length b) == Seq.slice (New.as_seq h b) (U32.v len) (New.length b)
  ))
= let b' = new_to_old_st b in
  Old.fill b' z len
