module LowStar.ModifiesPat
include LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

abstract
let loc_includes_union_l_buffer
  (s1 s2: loc)
  (#t: Type)
  (b: B.buffer t)
: Lemma
  (requires (loc_includes s1 (loc_buffer b) \/ loc_includes s2 (loc_buffer b)))
  (ensures (loc_includes (loc_union s1 s2) (loc_buffer b)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_buffer b))]
= loc_includes_union_l s1 s2 (loc_buffer b)

abstract
let loc_includes_union_l_addresses
  (s1 s2: loc)
  (prf: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (loc_includes s1 (loc_addresses prf r a) \/ loc_includes s2 (loc_addresses prf r a)))
  (ensures (loc_includes (loc_union s1 s2) (loc_addresses prf r a)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_addresses prf r a))]
= loc_includes_union_l s1 s2 (loc_addresses prf r a)

abstract
let loc_includes_union_l_regions
  (s1 s2: loc)
  (prf: bool)
  (r: Set.set HS.rid)
: Lemma
  (requires (loc_includes s1 (loc_regions prf r) \/ loc_includes s2 (loc_regions prf r)))
  (ensures (loc_includes (loc_union s1 s2) (loc_regions prf r)))
  [SMTPat (loc_includes (loc_union s1 s2) (loc_regions prf r))]
= loc_includes_union_l s1 s2 (loc_regions prf r)

(* Duplicate the modifies clause to cope with cases that must not be used with transitivity *)

abstract
let modifies_inert
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= modifies s h1 h2

let modifies_inert_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies_inert s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies_inert s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]
= ()

let modifies_inert_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies_inert p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (HS.contains h' b) ]
  ] ]
= ()

let modifies_inert_buffer_elim
  (#t1: Type)
  (b: B.buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    B.live h b /\
    modifies_inert p h h'
  ))
  (ensures (
    B.live h' b /\ (
    B.as_seq h b == B.as_seq h' b
  )))
  [SMTPatOr [
    [ SMTPat (modifies_inert p h h'); SMTPat (B.as_seq h b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (B.live h b) ];
    [ SMTPat (modifies_inert p h h'); SMTPat (B.as_seq h' b) ] ;
    [ SMTPat (modifies_inert p h h'); SMTPat (B.live h' b) ]
  ] ]
= ()

let modifies_inert_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies_inert l h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies_inert l h h');];
  ]]
= ()

let modifies_inert_liveness_insensitive_buffer_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: B.buffer t)
: Lemma
  (requires (modifies_inert l h h' /\ address_liveness_insensitive_locs `loc_includes` l /\ B.live h x))
  (ensures (B.live h' x))
  [SMTPatOr [
    [SMTPat (B.live h x); SMTPat (modifies_inert l h h');];
    [SMTPat (B.live h' x); SMTPat (modifies_inert l h h');];
  ]]
= ()

let modifies_inert_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' x)];
  ]]
= ()

let modifies_inert_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]
= ()

let modifies_inert_liveness_insensitive_region_buffer_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (x: B.buffer t)
: Lemma
  (requires (modifies_inert l2 h h' /\ region_liveness_insensitive_locs `loc_includes` l2 /\ HS.live_region h (B.frameOf x)))
  (ensures (HS.live_region h' (B.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h (B.frameOf x))];
    [SMTPat (modifies_inert l2 h h'); SMTPat (HS.live_region h' (B.frameOf x))];
  ]]
= ()

let fresh_frame_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (modifies_inert loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]
= fresh_frame_modifies h0 h1

let popped_modifies_inert
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.popped h0 h1))
  (ensures (modifies_inert (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]
= popped_modifies h0 h1
