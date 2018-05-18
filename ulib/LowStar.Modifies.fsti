module LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer

/// # The modifies clause for regions, references and buffers.
///
/// This module presents the modifies clause, a way to track the set
/// of memory locations modified by a stateful Low* (or even F*)
/// program. The basic principle of modifies clauses is that any
/// location that is disjoint from a set of memory locations modified
/// by an operation is preserved by that operation.
///
/// We start by specifying a monoid of sets of memory locations. From
/// a rough high-level view, ``loc`` is the type of sets of memory
/// locations, equipped with an identity element ``loc_none``,
/// representing the empty set, and an associative and commutative
/// operator, ``loc_union``, representing the union of two sets of
/// memory locations.
///
/// Moreover, ``loc_union`` is idempotent, which is useful to cut SMT
/// matching loops with ``modifies_trans`` and ``modifies_refl`` below.

val loc : Type0

val loc_none: loc

val loc_union
  (s1 s2: loc)
: GTot loc

val loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_union_comm
  (s1 s2: loc)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)

val loc_union_assoc
  (s1 s2 s3: loc)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_loc_none_l
  (s: loc)
: Lemma
  (loc_union loc_none s == s)

val loc_union_loc_none_r
  (s: loc)
: Lemma
  (loc_union s loc_none == s)


/// ``loc_buffer b`` is the set of memory locations associated to a buffer ``b``.

val loc_buffer
  (#t: Type)
  (b: B.buffer t)
: GTot loc


/// ``loc_addresses r n`` is the set of memory locations associated to a
/// set of addresses ``n`` in a given region ``r``.

val loc_addresses
  (r: HS.rid)
  (n: Set.set nat)
: GTot loc


/// ``loc_regions r`` is the set of memory locations associated to a set
/// ``r`` of regions.

val loc_regions
  (r: Set.set HS.rid)
: GTot loc


/// ``loc_mreference b`` is the set of memory locations associated to a
/// reference ``b``, which is actually the set of memory locations
/// associated to the address of ``b``.

let loc_mreference
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot loc
= loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))


/// ``loc_region_only r`` is the set of memory locations associated to a
/// region ``r`` but not any region ``r'`` that extends ``r`` (in the sense
/// of ``FStar.HyperStack.extends``.)

let loc_region_only
  (r: HS.rid)
: GTot loc
= loc_regions (Set.singleton r)


/// ``loc_all_regions_from r`` is the set of all memory locations
/// associated to a region ``r`` and any region ``r'`` that transitively
/// extends ``r`` (in the sense of ``FStar.HyperStack.extends``,
/// e.g. nested stack frames.)

let loc_all_regions_from
  (r: HS.rid)
: GTot loc
= loc_regions (HS.mod_set (Set.singleton r))


/// We equip the ``loc`` monoid of sets of memory locations with an
/// inclusion relation, ``loc_includes``, which is a preorder compatible
/// with ``loc_union``. Although we consider sets of memory locations,
/// we do not specify them using any F* set library such as
/// ``FStar.Set``, ``FStar.TSet`` or ``FStar.GSet``, because ``loc_includes``
/// encompasses more than just set-theoretic inclusion.

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


/// If a buffer ``b1`` includes a buffer ``b2`` in the sense of the buffer
/// theory (see ``LowStar.Buffer.includes``), then so are their
/// corresponding sets of memory locations.

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
  (ensures (UInt32.v i + UInt32.v len <= (B.length b) /\ loc_includes l (loc_buffer (B.gsub b i len))))
  [SMTPat (loc_includes l (loc_buffer (B.gsub b i len)))]

val loc_includes_gsub_buffer_l
  (#t: Type)
  (b: B.buffer t)
  (i1: UInt32.t)
  (len1: UInt32.t)
  (i2: UInt32.t)
  (len2: UInt32.t)
: Lemma
  (requires (UInt32.v i1 + UInt32.v len1 <= (B.length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1))
  (ensures (UInt32.v i1 + UInt32.v len1 <= (B.length b) /\ UInt32.v i1 <= UInt32.v i2 /\ UInt32.v i2 + UInt32.v len2 <= UInt32.v i1 + UInt32.v len1 /\ loc_includes (loc_buffer (B.gsub b i1 len1)) (loc_buffer (B.gsub b i2 len2))))
  [SMTPat (loc_includes (loc_buffer (B.gsub b i1 len1)) (loc_buffer (B.gsub b i2 len2)))]


/// Given a buffer ``b``, if its address is in a set ``s`` of addresses in
/// the region of ``b``, then the set of memory locations corresponding
/// to ``b`` is included in the set of memory locations corresponding to
/// the addresses in ``s`` in region ``r``.
///
/// In particular, the set of memory locations corresponding to a
/// buffer is included in the set of memory locations corresponding to
/// its region and address.

val loc_includes_addresses_buffer
  (#t: Type)
  (r: HS.rid)
  (s: Set.set nat)
  (p: B.buffer t)
: Lemma
  (requires (B.frameOf p == r /\ Set.mem (B.as_addr p) s))
  (ensures (loc_includes (loc_addresses r s) (loc_buffer p)))
  [SMTPat (loc_includes (loc_addresses r s) (loc_buffer p))]


/// The set of memory locations corresponding to a buffer is included
/// in the set of memory locations corresponding to its region.

val loc_includes_region_buffer
  (#t: Type)
  (s: Set.set HS.rid)
  (b: B.buffer t)
: Lemma
  (requires (Set.mem (B.frameOf b) s))
  (ensures (loc_includes (loc_regions s) (loc_buffer b)))
  [SMTPat (loc_includes (loc_regions s) (loc_buffer b))]


/// If a region ``r`` is in a set of region ``s``, then the set of memory
/// locations corresponding to a set of addresses ``a`` in ``r`` is
/// included in the set of memory locations corresponding to the
/// regions in ``s``.
///
/// In particular, the the set of memory locations corresponding to a
/// set of addresses ``a`` in a given region ``r`` is included in the set
/// of memory locations corresponding to region ``r``.

val loc_includes_region_addresses
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions s) (loc_addresses r a)))
  [SMTPat (loc_includes (loc_regions s) (loc_addresses r a))]

/// If a set of region identifiers ``s1`` includes a set of region
/// identifiers ``s2``, then so are their corresponding sets of memory
/// locations.

val loc_includes_region_region
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (Set.subset s2 s1))
  (ensures (loc_includes (loc_regions s1) (loc_regions s2)))
  [SMTPat (loc_includes (loc_regions s1) (loc_regions s2))]

/// The following lemma can act as a cut when reasoning with sets of
/// memory locations corresponding to sets of regions.

val loc_includes_region_union_l
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2)))
  [SMTPat (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2))]


/// Since inclusion encompasses more than just set-theoretic
/// inclusion, we also need to specify disjointness accordingly, as a
/// symmetric relation compatible with union.

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

/// If two sets of memory locations are disjoint, then so are any two
/// included sets of memory locations.

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))
  [SMTPatOr [
    [SMTPat (loc_disjoint p1 p2); SMTPat (loc_disjoint p1' p2')];
    [SMTPat (loc_includes p1 p1'); SMTPat (loc_includes p2 p2')];
  ]]

/// If two buffers are disjoint in the sense of the theory of buffers
/// (see ``LowStar.Buffer.disjoint``), then so are their corresponding
/// sets of memory locations.

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
    loc_disjoint (loc_buffer (B.gsub b i1 len1)) (loc_buffer (B.gsub b i2 len2))
  ))
  [SMTPat (loc_disjoint (loc_buffer (B.gsub b i1 len1)) (loc_buffer (B.gsub b i2 len2)))]


/// If two sets of addresses correspond to different regions or are
/// disjoint, then their corresponding sets of memory locations are
/// disjoint.

val loc_disjoint_addresses
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2)))
  [SMTPat (loc_disjoint (loc_addresses r1 n1) (loc_addresses r2 n2))]

/// If the region of a buffer ``p`` is not ``r``, or its address is not in
/// the set ``n`` of addresses, then their corresponding sets of memory
/// locations are disjoint.

val loc_disjoint_buffer_addresses
  (#t: Type)
  (p: B.buffer t)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r <> B.frameOf p \/ (~ (Set.mem (B.as_addr p) n))))
  (ensures (loc_disjoint (loc_buffer p) (loc_addresses r n)))
  [SMTPat (loc_disjoint (loc_buffer p) (loc_addresses r n))]

/// If two sets of region identifiers are disjoint, then so are their
/// corresponding sets of memory locations.

val loc_disjoint_regions
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions rs1) (loc_regions rs2)))
  [SMTPat (loc_disjoint (loc_regions rs1) (loc_regions rs2))]


/// The modifies clauses proper.
///
/// Let ``s`` be a set of memory locations, and ``h1`` and ``h2`` be two
/// memory states. Then, ``s`` is modified from ``h1`` to ``h2`` only if,
/// any memory location disjoint from ``s`` is preserved from ``h1`` into
/// ``h2``. Elimination lemmas illustrating this principle follow.

val modifies
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0

/// If a region ``r`` is disjoint from a set ``s`` of memory locations
/// which is modified, then its liveness is preserved.

val modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]

/// If a reference ``b`` is disjoint from a set ``p`` of memory locations
/// which is modified, then its liveness and contents are preserved.

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

/// If a buffer ``b`` *of positive length* is disjoint from a set ``p`` of
/// memory locations which is modified, then its liveness and contents
/// are preserved.
///
/// Here it is important to require that the length of ``b`` must not be
/// zero. Indeed, let ``x`` be a buffer of size 2, and pose ``y = B.gsub
/// x 2ul 0ul``. Then, ``y`` is disjoint from ``x``, because it is a
/// sub-buffer of ``x`` covering a range disjoint from that of ``x``
/// (since ``x == B.gsub x 0ul 2ul``.) However, if ``x`` is deallocated,
/// then ``x`` is no longer live, and so neither is ``y``, as a sub-buffer
/// of ``x``. This means that the liveness of buffers of length 0 cannot
/// be preserved by modifies clauses. Fortunately, in most cases, to
/// talk about the liveness of ``y``, it is always possible to reason
/// about the liveness of a buffer which encloses ``y``, such as ``x``.

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

/// If the memory state does not change, then any memory location is
/// modified (and, in particular, the empty set, ``loc_none``.)

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

/// If a set ``s2`` of memory locations is modified, then so is any set
/// ``s1`` that includes ``s2``. In other words, it is always possible to
/// weaken a modifies clause by widening its set of memory locations.

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

/// Modifies clauses are transitive. This lemma is the most general
/// one.

val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))
  [SMTPat (modifies s12 h1 h2); SMTPat (modifies s23 h2 h3)]

/// Regions that are not live can be removed from sets of memory
/// locations that are modified.

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

/// As a consequence, fresh regions can be removed from modifies
/// clauses.

val no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]

/// Stack discipline: any stack frame (and all its transitively
/// extending regions) that is pushed, modified and popped can be
/// removed from a modifies clause.

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

/// Compatibility lemmas to rescue modifies clauses specified in the
/// standard F* HyperStack library.

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

/// Modifies clauses for allocating a reference: nothing is
/// modified. (In particular, a modifies clause does not track
/// memory locations that are created.)

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

/// Modifies clause for freeing a reference: the address is modified.

val modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_mreference r) m (HS.free r m))

/// Another compatibility lemma

val modifies_none_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies loc_none h1 h2))

/// Main lemmas to integrate non-compositional modifies clauses
/// specified in ``LowStar.Buffer`` for elementary operations.
///
/// Case ``modifies_0``: allocation.

val modifies_0_modifies
  (h1 h2: HS.mem)
: Lemma
  (requires (B.modifies_0 h1 h2))
  (ensures (modifies loc_none h1 h2))
  [SMTPatOr [
    [SMTPat (B.modifies_0 h1 h2)];
    [SMTPat (modifies loc_none h1 h2)];
  ]]

/// Case ``modifies_1``: update, free.

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

/// Any live reference is disjoint from a buffer which has not been allocated yet.

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

/// Any live buffer is disjoint from a reference which has not been
/// allocated yet.

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

///  A memory ``h`` does not contain address ``a`` in region ``r``, denoted
///  ``does_not_contain_addr h (r, a)``, only if, either region ``r`` is
///  not live, or address ``a`` is unused in region ``r``.

(* BEGIN TODO: move to FStar.Monotonic.HyperStack *)

val does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: GTot Type0

val not_live_region_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (~ (HS.live_region h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val unused_in_does_not_contain_addr
  (h: HS.mem)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (h `does_not_contain_addr` (HS.frameOf r, HS.as_addr r)))

val addr_unused_in_does_not_contain_addr
  (h: HS.mem)
  (ra: HS.rid * nat)
: Lemma
  (requires (HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (Map.sel h.HS.h (fst ra))))
  (ensures (h `does_not_contain_addr` ra))

val free_does_not_contain_addr
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
: Lemma
  (requires (
    HS.is_mm r /\
    m `HS.contains` r /\
    fst x == HS.frameOf r /\
    snd x == HS.as_addr r
  ))
  (ensures (
    HS.free r m `does_not_contain_addr` x
  ))
  [SMTPat (HS.free r m `does_not_contain_addr` x)]

val does_not_contain_addr_elim
  (#a: Type0)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel)
  (m: HS.mem)
  (x: HS.rid * nat)
: Lemma
  (requires (
    m `does_not_contain_addr` x /\
    HS.frameOf r == fst x /\
    HS.as_addr r == snd x
  ))
  (ensures (~ (m `HS.contains` r)))

(** END TODO *)

/// Addresses that have not been allocated yet can be removed from
/// modifies clauses.

val modifies_only_live_addresses
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
