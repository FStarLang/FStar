module FStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = FStar.Buffer

(*** The modifies clause *)

val loc : Type u#1

val loc_none: loc

val loc_union
  (s1 s2: loc)
: GTot loc

(** The following is useful to make Z3 cut matching loops with
modifies_trans and modifies_refl *)
val loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_buffer
  (#t: Type)
  (b: B.buffer t)
: GTot loc

val loc_addresses
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc

val loc_regions
  (r: Set.set HS.rid)
: GTot loc

let loc_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))

let loc_region_only
  (r: HS.rid)
: GTot loc
= loc_regions (Set.singleton r)

let loc_all_regions_from
  (r: HS.rid)
: GTot loc
= loc_regions (HS.mod_set (Set.singleton r))


(* Inclusion of memory locations *)

val loc_includes
  (s1 s2: loc)
: GTot Type0

val loc_includes_refl
  (s: loc)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_union_l
  (s1 s2 s: loc)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  [SMTPat (loc_includes (loc_union s1 s2) s)]

val loc_includes_none
  (s: loc)
: Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val loc_includes_buffer
  (#t: Type)
  (b1 b2: B.buffer t)
: Lemma
  (requires (b1 `B.includes` b2))
  (ensures (loc_includes (loc_buffer b1) (loc_buffer b2)))
  [SMTPatOr [
    [SMTPat (B.includes b1 b2)];
    [SMTPat (loc_includes(loc_buffer b1) (loc_buffer b2))]
  ]]

val loc_includes_gsub_buffer_r
  (l: loc)
  (#t: Type)
  (b: B.buffer t)
  (i: UInt32.t)
  (len: UInt32.t)
: Lemma
  (requires (UInt32.v i + UInt32.v len <= (B.length b) /\ loc_includes l (loc_buffer b)))
  (ensures (UInt32.v i + UInt32.v len <= (B.length b) /\ loc_includes l (loc_buffer (B.sub b i len))))
  [SMTPat (loc_includes l (loc_buffer (B.sub b i len)))]

val loc_includes_gsub_buffer_l
  (#t: Type)
  (b: B.buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= (B.length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1))
  (ensures (UInt32.v i1 + UInt32.v len1 <= (B.length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\ loc_includes (loc_buffer (B.sub b i1 len1)) (loc_buffer (B.sub b i2 len2))))
  [SMTPat (loc_includes (loc_buffer (B.sub b i1 len1)) (loc_buffer (B.sub b i2 len2)))]

val loc_includes_addresses_buffer
  (#t: Type)
  (r: HS.rid)
  (s: Set.set nat)
  (p: B.buffer t)
: Lemma
  (requires (B.frameOf p == r /\ Set.mem (B.as_addr p) s))
  (ensures (loc_includes (loc_addresses r s) (loc_buffer p)))
  [SMTPat (loc_includes (loc_addresses r s) (loc_buffer p))]

val loc_includes_region_buffer
  (#t: Type)
  (s: Set.set HS.rid)
  (b: B.buffer t)
: Lemma
  (requires (Set.mem (B.frameOf b) s))
  (ensures (loc_includes (loc_regions s) (loc_buffer b)))
  [SMTPat (loc_includes (loc_regions s) (loc_buffer b))]

val loc_includes_region_addresses
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions s) (loc_addresses r a)))
  [SMTPat (loc_includes (loc_regions s) (loc_addresses r a))]

val loc_includes_region_region
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (Set.subset s2 s1))
  (ensures (loc_includes (loc_regions s1) (loc_regions s2)))
  [SMTPat (loc_includes (loc_regions s1) (loc_regions s2))]

val loc_includes_region_union_l
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2))]


(* Disjointness of two memory locations *)

val loc_disjoint
  (s1 s2: loc)
: GTot Type0

val loc_disjoint_sym
  (s1 s2: loc)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
  [SMTPat (loc_disjoint s1 s2)]

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r
  (s s1 s2: loc)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))
  [SMTPatOr [
    [SMTPat (loc_disjoint p1 p2); SMTPat (loc_disjoint p1' p2')];
    [SMTPat (loc_includes p1 p1'); SMTPat (loc_includes p2 p2')];
  ]]

val loc_disjoint_buffer
  (#t1 #t2: Type)
  (b1: B.buffer t1)
  (b2: B.buffer t2)
: Lemma
  (requires (B.disjoint b1 b2))
  (ensures (loc_disjoint (loc_buffer b1) (loc_buffer b2)))
  [SMTPatOr [
    [SMTPat (B.disjoint b1 b2)];
    [SMTPat (loc_disjoint (loc_buffer b1) (loc_buffer b2))];
  ]]

val loc_disjoint_gsub_buffer
  (#t: Type)
  (b: B.buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (
    UInt32.v i1 + UInt32.v len1 <= (B.length b) /\
    UInt32.v i2 + UInt32.v len2 <= (B.length b) /\ (
    UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
    UInt32.v i2 + UInt32.v len2 <= UInt32.v i1
  )))
  (ensures (
    UInt32.v i1 + UInt32.v len1 <= (B.length b) /\
    UInt32.v i2 + UInt32.v len2 <= (B.length b) /\
    loc_disjoint (loc_buffer (B.sub b i1 len1)) (loc_buffer (B.sub b i2 len2))
  ))
  [SMTPat (loc_disjoint (loc_buffer (B.sub b i1 len1)) (loc_buffer (B.sub b i2 len2)))]

val loc_disjoint_addresses
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2))]

val loc_disjoint_buffer_addresses
  (#t: Type)
  (p: B.buffer t)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> B.frameOf p \/ (~ (Set.mem (B.as_addr p) n))))
  (ensures (loc_disjoint (loc_buffer p) (loc_addresses r n)))
  [SMTPat (loc_disjoint (loc_buffer p) (loc_addresses r n))]
  
val loc_disjoint_regions
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions rs1) (loc_regions rs2)))
  [SMTPat (loc_disjoint (loc_regions rs1) (loc_regions rs2))]


(** The modifies clause proper *)

val modifies
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_mreference_elim
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_mreference b) p /\
    HS.contains h b /\
    modifies p h h'
  ))
  (ensures (
    HS.contains h' b /\
    HS.sel h b == HS.sel h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h b) ];
    [ SMTPat (modifies p h h'); SMTPat (HS.sel h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (HS.contains h' b) ]
  ] ]

val modifies_buffer_elim
  (#t1: Type)
  (b: B.buffer t1)
  (p: loc)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_buffer b) p /\
    B.live h b /\
    ((B.length b) == 0 ==> B.live h' b) /\ // necessary for liveness, because all buffers of size 0 are disjoint for any memory location, so we cannot talk about their liveness individually without referring to a larger nonempty buffer
    modifies p h h'
  ))
  (ensures (
    B.live h' b /\ (
    B.as_seq h b == B.as_seq h' b
  )))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (B.as_seq h b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (B.live h b) ];
    [ SMTPat (modifies p h h'); SMTPat (B.as_seq h' b) ] ;
    [ SMTPat (modifies p h h'); SMTPat (B.live h' b) ]
  ] ]

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPatOr [
    [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')];
    [SMTPat (modifies s1 h h'); SMTPat (loc_includes s1 s2)];
    [SMTPat (modifies s2 h h'); SMTPat (loc_includes s1 s2)];
  ]]

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

val modifies_only_live_regions
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]

val modifies_fresh_frame_popped
  (h0 h1: HS.mem)
  (s: loc)
  (h2 h3: HS.mem)
: Lemma
  (requires (
    HS.fresh_frame h0 h1 /\
    modifies (loc_union (loc_all_regions_from h1.HS.tip) s) h1 h2 /\
    h2.HS.tip == h1.HS.tip /\
    HS.popped h2 h3
  ))
  (ensures (
    modifies s h0 h3 /\
    h3.HS.tip == h0.HS.tip
  ))
  [SMTPat (HS.fresh_frame h0 h1); SMTPat (HS.popped h2 h3); SMTPat (modifies s h0 h3)]

val modifies_loc_regions_intro
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions rs) h1 h2))

val modifies_loc_addresses_intro
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses r a) l) h1 h2))

val modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies loc_none h h'))

val modifies_salloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HS.is_stack_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.salloc_post init h x h'))
  (ensures (modifies loc_none h h'))

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_mreference r) m (HS.free r m))

val modifies_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))

val modifies_buffer_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))

val modifies_0_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_0 h1 h2))
  (ensures (modifies loc_none h1 h2))

val modifies_1_modifies
  (#a: Type)
  (b: B.buffer a)
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_1 b h1 h2))
  (ensures (modifies (loc_buffer b) h1 h2))
  [SMTPatOr [
    [SMTPat (B.modifies_1 b h1 h2)];
    [SMTPat (modifies (loc_buffer b) h1 h2)];
  ]]

val modifies_2_modifies
  (#a1 #a2: Type)
  (b1: B.buffer a1)
  (b2: B.buffer a2)
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_2 b1 b2 h1 h2))
  (ensures (modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h1 h2))

val modifies_3_modifies
  (#a1 #a2 #a3: Type)
  (b1: B.buffer a1)
  (b2: B.buffer a2)
  (b3: B.buffer a3)
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_3 b1 b2 b3 h1 h2))
  (ensures (modifies (loc_union (loc_buffer b1) (loc_union (loc_buffer b2) (loc_buffer b3))) h1 h2))

val modifies_buffer_rcreate_post_common
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: FStar.UInt32.t)
  (b: B.buffer a)
  (h0 h1: HS.mem)
: Lemma
  (requires (B.rcreate_post_common r init len b h0 h1))
  (ensures (modifies loc_none h0 h1))

val mreference_live_buffer_unused_in_disjoint
  (#t1: Type)
  (#pre: Preorder.preorder t1)
  (#t2: Type)
  (h: HS.mem)
  (b1: HS.mreference t1 pre)
  (b2: B.buffer t2)
: Lemma
  (requires (HS.contains h b1 /\ B.unused_in b2 h))
  (ensures (loc_disjoint (loc_mreference b1)  (loc_buffer b2)))
  [SMTPat (HS.contains h b1); SMTPat (B.unused_in b2 h)]

val buffer_live_mreference_unused_in_disjoint
  (#t1: Type)
  (#t2: Type)
  (#pre: Preorder.preorder t2)
  (h: HS.mem)
  (b1: B.buffer t1)
  (b2: HS.mreference t2 pre)
: Lemma
  (requires (B.live h b1 /\ HS.unused_in b2 h))
  (ensures (loc_disjoint (loc_buffer b1) (loc_mreference b2)))
  [SMTPat (B.live h b1); SMTPat (HS.unused_in b2 h)]
