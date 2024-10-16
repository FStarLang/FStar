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
module LowStar.ToFStarBuffer

(* WARNING: FOR TRANSITIONAL PURPOSES ONLY *)
#set-options "--ext 'context_pruning='"
module Old = FStar.Buffer
module OldM = FStar.Modifies
module New = LowStar.Buffer
module NewM = LowStar.Modifies
module HST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module U32 = FStar.UInt32

assume val new_to_old_ghost (#t: Type0) (b: New.buffer t) : GTot (Old.buffer t)
assume val old_to_new_ghost (#t: Type0) (b: Old.buffer t) : GTot (New.buffer t)

assume val new_to_old_st (#t: Type0) (b: New.buffer t) : HST.Stack (b' : Old.buffer t { b' == new_to_old_ghost b } )
  (requires (fun h -> New.live h b))
  (ensures (fun h b' h' -> h' == h))

assume val old_to_new_st (#t: Type0) (b: Old.buffer t) : HST.Stack (b' : New.buffer t { b' == old_to_new_ghost b })
  (requires (fun h -> Old.live h b))
  (ensures (fun h b' h' -> h' == h))

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

assume val new_to_old_disjoint (#t1 #t2: Type0) (b1: New.buffer t1) (b2: Old.buffer t2) : Lemma
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

let old_to_union_loc (l: OldM.loc) : GTot (M.loc old_and_new_cl_union) =
  M.union_loc_of_loc old_and_new_cl false (OldM.cloc_of_loc l)

let new_to_union_loc (l: NewM.loc) : GTot (M.loc old_and_new_cl_union) =
  M.union_loc_of_loc old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc l))

let old_to_new_modifies (old_l: OldM.loc) (new_l: NewM.loc) (h h' : HS.mem) : Lemma
  (requires (OldM.modifies old_l h h' /\ old_to_union_loc old_l == new_to_union_loc new_l))
  (ensures (NewM.modifies new_l h h'))
= OldM.modifies_to_cloc old_l h h';
  M.modifies_union_loc_of_loc old_and_new_cl false (OldM.cloc_of_loc old_l) h h';
  M.modifies_union_loc_of_loc old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc new_l)) h h';
  M.modifies_raise_loc (NewM.cloc_of_loc new_l) h h';
  NewM.modifies_to_cloc new_l h h'

let old_to_union_loc_none : squash (old_to_union_loc OldM.loc_none == M.loc_none) =
  OldM.cloc_of_loc_none ();
  M.union_loc_of_loc_none old_and_new_cl false

let new_to_union_loc_none : squash (new_to_union_loc NewM.loc_none == M.loc_none) =
  NewM.cloc_of_loc_none ();
  M.raise_loc_none #_ #NewM.cloc_cls;
  M.union_loc_of_loc_none old_and_new_cl true

let old_to_union_loc_union (old1 old2: OldM.loc) : Lemma
 (old_to_union_loc (old1 `OldM.loc_union` old2) == old_to_union_loc old1 `M.loc_union` old_to_union_loc old2)
  [SMTPat (old_to_union_loc (old1 `OldM.loc_union` old2))]
= OldM.cloc_of_loc_union old1 old2;
  M.union_loc_of_loc_union old_and_new_cl false (OldM.cloc_of_loc old1) (OldM.cloc_of_loc old2)

let new_to_union_loc_union (new1 new2: NewM.loc) : Lemma
 (new_to_union_loc (new1 `NewM.loc_union` new2) == new_to_union_loc new1 `M.loc_union` new_to_union_loc new2)
  [SMTPat (new_to_union_loc (new1 `NewM.loc_union` new2))]
= NewM.cloc_of_loc_union new1 new2;
  M.raise_loc_union (NewM.cloc_of_loc new1) (NewM.cloc_of_loc new2);
  M.union_loc_of_loc_union old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc new1)) (M.raise_loc (NewM.cloc_of_loc new2))

let old_to_union_loc_addresses (preserve_liveness: bool) (r: HS.rid) (n: Set.set nat) : Lemma
  (old_to_union_loc (OldM.loc_addresses preserve_liveness r n) == M.loc_addresses preserve_liveness r n)
  [SMTPat (old_to_union_loc (OldM.loc_addresses preserve_liveness r n))]
= OldM.cloc_of_loc_addresses preserve_liveness r n;
  M.union_loc_of_loc_addresses old_and_new_cl false preserve_liveness r n

let new_to_union_loc_addresses (preserve_liveness: bool) (r: HS.rid) (n: Set.set nat) : Lemma
  (new_to_union_loc (NewM.loc_addresses preserve_liveness r n) == M.loc_addresses preserve_liveness r n)
  [SMTPat (new_to_union_loc (NewM.loc_addresses preserve_liveness r n))]
= NewM.cloc_of_loc_addresses preserve_liveness r n;
  M.raise_loc_addresses u#0 u#0 #_ #NewM.cloc_cls preserve_liveness r n;
  M.union_loc_of_loc_addresses old_and_new_cl true preserve_liveness r n

let old_to_union_loc_regions (preserve_liveness: bool) (r: Set.set HS.rid) : Lemma
  (old_to_union_loc (OldM.loc_regions preserve_liveness r) == M.loc_regions preserve_liveness r)
  [SMTPat (old_to_union_loc (OldM.loc_regions preserve_liveness r))]
= OldM.cloc_of_loc_regions preserve_liveness r;
  M.union_loc_of_loc_regions old_and_new_cl false preserve_liveness r

let new_to_union_loc_regions (preserve_liveness: bool) (r: Set.set HS.rid) : Lemma
  (new_to_union_loc (NewM.loc_regions preserve_liveness r) == M.loc_regions preserve_liveness r)
  [SMTPat (new_to_union_loc (NewM.loc_regions preserve_liveness r))]
= NewM.cloc_of_loc_regions preserve_liveness r;
  M.raise_loc_regions u#0 u#0 #_ #NewM.cloc_cls preserve_liveness r;
  M.union_loc_of_loc_regions old_and_new_cl true preserve_liveness r

let union_loc_to_new (l: M.loc old_and_new_cl_union) : GTot NewM.loc =
  NewM.loc_of_cloc (M.lower_loc (M.loc_of_union_loc true l))

let union_loc_to_new_new_to_union_loc (l: NewM.loc) : Lemma
  (union_loc_to_new (new_to_union_loc l) == l)
  [SMTPat (union_loc_to_new (new_to_union_loc l))]
= M.loc_of_union_loc_union_loc_of_loc old_and_new_cl true (M.raise_loc (NewM.cloc_of_loc l));
  M.lower_loc_raise_loc u#0 u#0 (NewM.cloc_of_loc l);
  NewM.loc_of_cloc_of_loc l

let union_loc_to_new_none : squash (union_loc_to_new M.loc_none == NewM.loc_none) =
  M.loc_of_union_loc_none old_and_new_cl true;
  M.lower_loc_none u#0 u#0 #_ #NewM.cloc_cls;
  NewM.cloc_of_loc_none ();
  NewM.loc_of_cloc_of_loc NewM.loc_none

let coerce (t2: Type) (#t1: Type) (x: t1) : Pure t2 (requires (t1 == t2)) (ensures (fun y -> x == y)) = x

let union_loc_to_new_union (l1 l2: M.loc old_and_new_cl_union) : Lemma
  (union_loc_to_new (l1 `M.loc_union` l2) == union_loc_to_new l1 `NewM.loc_union` union_loc_to_new l2)
  [SMTPat (union_loc_to_new (l1 `M.loc_union` l2))]
= M.loc_of_union_loc_union old_and_new_cl true l1 l2;
  let t : Type u#1 = M.loc (old_and_new_cl true) in
  let i1 : t = M.loc_of_union_loc true l1 in
  let i2 : t = M.loc_of_union_loc true l2 in
  let j1 : M.loc (M.raise_cls NewM.cloc_cls) = coerce (M.loc (M.raise_cls NewM.cloc_cls)) i1 in
  let j2 : M.loc (M.raise_cls u#0 u#0 NewM.cloc_cls) = coerce (M.loc (M.raise_cls NewM.cloc_cls)) i2 in
  M.lower_loc_union u#0 u#0 j1 j2;
  NewM.cloc_of_loc_union (NewM.loc_of_cloc (M.lower_loc j1)) (NewM.loc_of_cloc (M.lower_loc j2));
  NewM.loc_of_cloc_of_loc (NewM.loc_of_cloc (M.lower_loc j1) `NewM.loc_union` NewM.loc_of_cloc (M.lower_loc j2))

let union_loc_to_new_addresses (preserve_liveness: bool) (r: HS.rid) (n: Set.set nat) : Lemma
  (union_loc_to_new (M.loc_addresses preserve_liveness r n) == NewM.loc_addresses preserve_liveness r n)
  [SMTPat (union_loc_to_new (M.loc_addresses preserve_liveness r n))]
= M.loc_of_union_loc_addresses old_and_new_cl true preserve_liveness r n;
  M.lower_loc_addresses u#0 u#0 #_ #NewM.cloc_cls preserve_liveness r n;
  NewM.cloc_of_loc_addresses preserve_liveness r n;
  NewM.cloc_of_loc_of_cloc (M.loc_addresses preserve_liveness r n)

let union_loc_to_new_regions (preserve_liveness: bool) (r: Set.set HS.rid) : Lemma
  (union_loc_to_new (M.loc_regions preserve_liveness r) == NewM.loc_regions preserve_liveness r)
  [SMTPat (union_loc_to_new (M.loc_regions preserve_liveness r))]
= M.loc_of_union_loc_regions old_and_new_cl true preserve_liveness r;
  M.lower_loc_regions u#0 u#0 #_ #NewM.cloc_cls preserve_liveness r;
  NewM.cloc_of_loc_regions preserve_liveness r;
  NewM.cloc_of_loc_of_cloc (M.loc_regions preserve_liveness r)

let old_to_new_modifies' (old_l: OldM.loc) (h h' : HS.mem) : Lemma
  (requires (OldM.modifies old_l h h' /\ new_to_union_loc (union_loc_to_new (old_to_union_loc old_l)) == old_to_union_loc old_l))
  (ensures (NewM.modifies (union_loc_to_new (old_to_union_loc old_l)) h h'))
  [SMTPat (OldM.modifies old_l h h')]
= old_to_new_modifies old_l (union_loc_to_new (old_to_union_loc old_l)) h h'

assume val loc_buffer_new_to_old (#t: Type0) (b: New.buffer t) : Lemma
  (old_to_union_loc (OldM.loc_buffer (new_to_old_ghost b)) == new_to_union_loc (NewM.loc_buffer b))
  [SMTPat (old_to_union_loc (OldM.loc_buffer (new_to_old_ghost b)))]

let modifies_0_modifies (h h' : HS.mem) : Lemma
  (requires (Old.modifies_0 h h'))
  (ensures (NewM.modifies NewM.loc_none h h'))
= ()

let modifies_1_modifies
  (#t: Type)
  (b: New.buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (Old.modifies_1 (new_to_old_ghost b) h h'))
  (ensures (NewM.modifies (NewM.loc_buffer b) h h'))
= ()

let modifies_2_modifies
  (#t1 #t2: Type)
  (b1: New.buffer t1)
  (b2: New.buffer t2)
  (h h' : HS.mem)
: Lemma
  (requires (Old.modifies_2 (new_to_old_ghost b1) (new_to_old_ghost b2) h h'))
  (ensures (NewM.modifies (NewM.loc_union (NewM.loc_buffer b1) (NewM.loc_buffer b2)) h h'))
= ()

(* Examples *)

/// Basic example of mutating a new buffer by converting it first to
/// an old buffer.
///
/// The spec shows that all three flavors of modifies clauses can be
/// proven and the precise contents are reflected into the new buffer
let ex1 (#a:Type) (b:New.buffer nat{New.length b > 0}) (b1:New.buffer a)
  : HST.ST unit
           (requires (fun h -> New.live h b /\ New.disjoint b b1 /\ New.live h b1))
           (ensures (fun h0 _ h1 ->
             New.get h1 b 0 == 0 /\
             Old.get h1 (new_to_old_ghost b) 0 == 0 /\
             New.as_seq h0 b1 == New.as_seq h1 b1 /\
             NewM.modifies (NewM.loc_buffer b) h0 h1 /\
             OldM.modifies (OldM.loc_buffer (new_to_old_ghost b)) h0 h1 /\
             Old.modifies_1 (new_to_old_ghost b) h0 h1)) =
  let old = new_to_old_st b in
  Old.upd old 0ul 0

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


(* Conversions in the other way round, to have old buffer code call into new buffer code. Those are more aggressive. *)

assume
val loc_disjoint_new_disjoint_old
  (#t1 #t2: Type)
  (b1: New.buffer t1)
  (b2: New.buffer t2)
: Lemma
  (requires (NewM.loc_disjoint (NewM.loc_buffer b1) (NewM.loc_buffer b2)))
  (ensures (Old.disjoint (new_to_old_ghost b1) (new_to_old_ghost b2)))
  [SMTPat (Old.disjoint (new_to_old_ghost b1) (new_to_old_ghost b2))]

assume
val modifies_modifies_0
  (h h' : HS.mem)
: Lemma
  (requires (NewM.modifies NewM.loc_none h h'))
  (ensures (Old.modifies_0 h h'))
  [SMTPat (NewM.modifies NewM.loc_none h h')]

assume
val modifies_modifies_1
  (#t: Type)
  (b: Old.buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (NewM.modifies (NewM.loc_buffer (old_to_new_ghost b)) h h'))
  (ensures (Old.modifies_1 b h h'))
  [SMTPat (NewM.modifies (NewM.loc_buffer (old_to_new_ghost b)) h h')]

assume
val modifies_modifies_2
  (#t1 #t2: Type)
  (b1: Old.buffer t1)
  (b2: Old.buffer t2)
  (h h' : HS.mem)
: Lemma
  (requires (NewM.modifies (NewM.loc_buffer (old_to_new_ghost b1) `NewM.loc_union` NewM.loc_buffer (old_to_new_ghost b2)) h h'))
  (ensures (Old.modifies_2 b1 b2 h h'))
  [SMTPat (NewM.modifies (NewM.loc_buffer (old_to_new_ghost b1) `NewM.loc_union` NewM.loc_buffer (old_to_new_ghost b2)) h h')]


/// Basic example of mutating an old buffer by converting it first to
/// a new buffer.
///
/// The spec shows that all two flavors of modifies clauses can be
/// proven and the precise contents are reflected into the new buffer

let ex1' (#a:Type) (b:Old.buffer nat{Old.length b > 0}) (b1:Old.buffer a)
  : HST.ST unit
           (requires (fun h -> Old.live h b /\ Old.disjoint b b1 /\ Old.live h b1))
           (ensures (fun h0 _ h1 ->
             Old.get h1 b 0 == 0 /\
             New.get h1 (old_to_new_ghost b) 0 == 0 /\
             Old.as_seq h0 b1 == Old.as_seq h1 b1 /\
             NewM.modifies (NewM.loc_buffer (old_to_new_ghost b)) h0 h1 /\
             Old.modifies_1 b h0 h1)) =
  let ne = old_to_new_st b in
  New.upd ne 0ul 0

let ex1'' (#a:Type) (b:New.buffer nat{New.length b > 0}) (b1:New.buffer a)
  : HST.ST unit
           (requires (fun h -> New.live h b /\ NewM.loc_disjoint (NewM.loc_buffer b) (NewM.loc_buffer b1) /\ New.live h b1))
           (ensures (fun h0 _ h1 ->
             New.get h1 b 0 == 0 /\
             Old.get h1 (new_to_old_ghost b) 0 == 0 /\
             New.as_seq h0 b1 == New.as_seq h1 b1 /\
             NewM.modifies (NewM.loc_buffer b) h0 h1 /\
             OldM.modifies (OldM.loc_buffer (new_to_old_ghost b)) h0 h1 /\
             Old.modifies_1 (new_to_old_ghost b) h0 h1)) =
  let old = new_to_old_st b in
  let old1 = new_to_old_st b1 in
  ex1' old old1
