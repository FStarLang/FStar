module FStar.ModifiesGen

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(*** The modifies clause *)

(* NOTE: aloc cannot be a member of the class, because of OCaml
   extraction. So it must be a parameter of the class instead. *)

inline_for_extraction
type aloc_t = HS.rid -> nat -> Tot Type0

noeq
type cls (aloc: aloc_t) : Type u#1 = | Cls:
  (aloc_includes: (
    (#r: HS.rid) ->
    (#a: nat) ->
    aloc r a ->
    aloc r a ->
    GTot Type0
  )) ->
  (aloc_includes_refl: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    Lemma
    (aloc_includes x x)
  )) ->
  (aloc_includes_trans: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    (x3: aloc r a) ->
    Lemma
    (requires (aloc_includes x1 x2 /\ aloc_includes x2 x3))
    (ensures (aloc_includes x1 x3))
  )) ->
  (aloc_disjoint: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    GTot Type0
  )) ->
  (aloc_disjoint_sym: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x1: aloc r a) ->
    (x2: aloc r a) ->
    Lemma
    (aloc_disjoint x1 x2 <==> aloc_disjoint x2 x1)
  )) ->
  (aloc_disjoint_includes: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (larger1: aloc r a) ->
    (larger2: aloc r a) ->
    (smaller1: aloc r a) ->
    (smaller2: aloc r a) ->
    Lemma
    (requires (aloc_disjoint larger1 larger2 /\ larger1 `aloc_includes` smaller1 /\ larger2 `aloc_includes` smaller2))
    (ensures (aloc_disjoint smaller1 smaller2))
  )) ->
  (aloc_preserved: (
    (#r: HS.rid) ->
    (#a: nat) ->
    aloc r a ->
    HS.mem ->
    HS.mem ->
    GTot Type0
  )) ->
  (aloc_preserved_refl: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    (h: HS.mem) ->
    Lemma
    (aloc_preserved x h h)
  )) ->
  (aloc_preserved_trans: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (x: aloc r a) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (h3: HS.mem) ->
    Lemma
    (requires (aloc_preserved x h1 h2 /\ aloc_preserved x h2 h3))
    (ensures (aloc_preserved x h1 h3))
  )) ->
  (* if any reference at this address is preserved, then any location at this address is preserved *)
  (same_mreference_aloc_preserved: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (b: aloc r a) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    (f: (
      (a' : Type0) ->
      (pre: Preorder.preorder a') ->
      (r': HS.mreference a' pre) ->
      Lemma
      (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
      (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
    )) ->
    Lemma
    (aloc_preserved b h1 h2)
  )) ->
  (* In general, a location should not be disjoint from itself, but if it really is (e.g. a zero-length buffer), then it shall be always preserved. *)
  (aloc_disjoint_self_preserved: (
    (#r: HS.rid) ->
    (#a: nat) ->
    (b: aloc r a) ->
    (h1: HS.mem) ->
    (h2: HS.mem) ->
    Lemma
    (requires (aloc_disjoint b b))
    (ensures (aloc_preserved b h1 h2))
  )) ->
  cls aloc

val loc (#aloc: aloc_t) (c: cls aloc) : Tot (Type u#0)

val loc_none (#aloc: aloc_t) (#c: cls aloc): Tot (loc c)

val loc_union
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot (loc c)

(** The following is useful to make Z3 cut matching loops with
modifies_trans and modifies_refl *)
val loc_union_idem
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s s == s)

val loc_union_comm
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)

val loc_union_assoc
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_loc_none_l
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union loc_none s == s)

val loc_union_loc_none_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_union s loc_none == s)


val loc_of_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#n: nat)
  (b: aloc r n)
: GTot (loc c)

val loc_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (n: Set.set nat)
: GTot (loc c)

val loc_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (r: Set.set HS.rid)
: GTot (loc c)

let loc_mreference
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#p: Preorder.preorder a)
  (b: HS.mreference a p)
: GTot (loc c)
= loc_addresses (HS.frameOf b) (Set.singleton (HS.as_addr b))

let loc_region_only
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
: GTot (loc c)
= loc_regions (Set.singleton r)

let loc_all_regions_from
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
: GTot (loc c)
= loc_regions (HS.mod_set (Set.singleton r))


(* Inclusion of memory locations *)

val loc_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot Type0

val loc_includes_refl
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s s)

val loc_includes_trans
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s3: loc c)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))

val loc_includes_union_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_includes s s1 /\ loc_includes s s2))
  (ensures (loc_includes s (loc_union s1 s2)))

val loc_includes_union_l
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2 s: loc c)
: Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))

val loc_includes_none
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (loc_includes s loc_none)

val loc_includes_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#n: nat)
  (b1 b2: aloc r n)
: Lemma
  (requires (c.aloc_includes b1 b2))
  (ensures (loc_includes (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_includes_addresses_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (s: Set.set nat)
  (#a: nat)
  (p: aloc r a)
: Lemma
  (requires (Set.mem a s))
  (ensures (loc_includes (loc_addresses r s) (loc_of_aloc #_ #c p)))

val loc_includes_region_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (s: Set.set HS.rid)
  (#r: HS.rid)
  (#a: nat)
  (b: aloc r a)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions s) (loc_of_aloc #_ #c b)))

val loc_includes_region_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes (loc_regions #_ #c s) (loc_addresses r a)))

val loc_includes_region_region
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (Set.subset s2 s1))
  (ensures (loc_includes (loc_regions #_ #c s1) (loc_regions s2)))

val loc_includes_region_union_l
  (#aloc: aloc_t) (#c: cls aloc)
  (l: loc c)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions s1) l) (loc_regions s2)))


(* Disjointness of two memory locations *)

val loc_disjoint
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: GTot Type0

val loc_disjoint_sym
  (#aloc: aloc_t) (#c: cls aloc)
  (s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))

val loc_disjoint_none_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
: Lemma
  (ensures (loc_disjoint s loc_none))

val loc_disjoint_union_r
  (#aloc: aloc_t) (#c: cls aloc)
  (s s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s s1 /\ loc_disjoint s s2))
  (ensures (loc_disjoint s (loc_union s1 s2)))

val loc_disjoint_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (p1 p2 p1' p2' : loc c)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_aloc
  (#aloc: aloc_t) (#c: cls aloc)
  (#r1: HS.rid)
  (#a1: nat)
  (#r2: HS.rid)
  (#a2: nat)
  (b1: aloc r1 a1)
  (b2: aloc r2 a2)
: Lemma
  (requires ((r1 == r2 /\ a1 == a2) ==> c.aloc_disjoint b1 b2))
  (ensures (loc_disjoint (loc_of_aloc b1) (loc_of_aloc #_ #c b2)))

val loc_disjoint_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint (loc_addresses #_ #c r1 n1) (loc_addresses r2 n2)))

val loc_disjoint_aloc_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (#r' : HS.rid)
  (#a' : nat)
  (p: aloc r' a')
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (requires (r == r' ==> (~ (Set.mem a' n))))
  (ensures (loc_disjoint (loc_of_aloc p) (loc_addresses #_ #c r n)))
  
val loc_disjoint_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint (loc_regions #_ #c rs1) (loc_regions rs2)))


(** The modifies clause proper *)

val modifies
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_live_region
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_mreference_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (b: HS.mreference t pre)
  (p: loc c)
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

val modifies_aloc_elim
  (#aloc: aloc_t) (#c: cls aloc)
  (#r: HS.rid)
  (#a: nat)
  (b: aloc r a)
  (p: loc c)
  (h h': HS.mem)
: Lemma
  (requires (
    loc_disjoint (loc_of_aloc b) p /\
    modifies p h h'
  ))
  (ensures (
    c.aloc_preserved b h h'
  ))

val modifies_refl
  (#aloc: aloc_t) (#c: cls aloc)
  (s: loc c)
  (h: HS.mem)
: Lemma
  (modifies s h h)

val modifies_loc_includes
  (#aloc: aloc_t) (#c: cls aloc)
  (s1: loc c)
  (h h': HS.mem)
  (s2: loc c)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))

val modifies_trans
  (#aloc: aloc_t) (#c: cls aloc)
  (s12: loc c)
  (h1 h2: HS.mem)
  (s23: loc c)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val modifies_only_live_regions
  (#aloc: aloc_t) (#c: cls aloc)
  (rs: Set.set HS.rid)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))

val no_upd_fresh_region
  (#aloc: aloc_t) (#c: cls aloc)
  (r:HS.rid)
  (l:loc c)
  (h0:HS.mem)
  (h1:HS.mem)
: Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from r) l) h0 h1))
  (ensures  (modifies l h0 h1))

val modifies_fresh_frame_popped
  (#aloc: aloc_t) (#c: cls aloc)
  (h0 h1: HS.mem)
  (s: loc c)
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

val modifies_loc_regions_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (rs: Set.set HS.rid)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.modifies rs h1 h2))
  (ensures (modifies (loc_regions #_ #c rs) h1 h2))

val modifies_loc_addresses_intro
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r a h1 h2
  ))
  (ensures (modifies (loc_union (loc_addresses r a) l) h1 h2))

val modifies_ralloc_post
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies (loc_none #_ #c) h h'))

val modifies_salloc_post
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HS.is_stack_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.salloc_post init h x h'))
  (ensures (modifies (loc_none #_ #c) h h'))

val modifies_free
  (#aloc: aloc_t) (#c: cls aloc)
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_mreference #_ #c r) m (HS.free r m))

val modifies_none_modifies
  (#aloc: aloc_t) (#c: cls aloc)
  (h1 h2: HS.mem)
: Lemma
  (requires (HST.modifies_none h1 h2))
  (ensures (modifies (loc_none #_ #c) h1 h2))

(** BEGIN TODO: move to FStar.Monotonic.HyperStack *)

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

val modifies_only_live_addresses
  (#aloc: aloc_t) (#c: cls aloc)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))


(** * Compositionality *)

val aloc_union: (bool -> Tot aloc_t) -> Tot aloc_t

val cls_union (#a: (bool -> Tot aloc_t)) (c: ((b: bool) -> Tot (cls (a b)))) : Tot (cls (aloc_union a))

val union_loc_of_loc (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b))) (b: bool) (l: loc (c b)) : GTot (loc (cls_union c))

val union_loc_of_loc_none
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
: Lemma
  (union_loc_of_loc c b (loc_none #_ #(c b)) == loc_none #_ #(cls_union c))

val union_loc_of_loc_union
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (l1 l2: loc (c b))
: Lemma
  (union_loc_of_loc c b (loc_union #_ #(c b) l1 l2) == loc_union #_ #(cls_union c) (union_loc_of_loc c b l1) (union_loc_of_loc c b l2))

val union_loc_of_loc_addresses
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (r: HS.rid)
  (n: Set.set nat)
: Lemma
  (union_loc_of_loc c b (loc_addresses #_ #(c b) r n) == loc_addresses #_ #(cls_union c) r n)

val union_loc_of_loc_regions
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (r: Set.set HS.rid)
: Lemma
  (union_loc_of_loc c b (loc_regions #_ #(c b) r) == loc_regions #_ #(cls_union c) r)

val union_loc_of_loc_includes
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (s1 s2: loc (c b))
: Lemma
  (union_loc_of_loc c b s1 `loc_includes` union_loc_of_loc c b s2 <==> s1 `loc_includes` s2)

val union_loc_of_loc_disjoint
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (s1 s2: loc (c b))
: Lemma
  (union_loc_of_loc c b s1 `loc_disjoint` union_loc_of_loc c b s2 <==> s1 `loc_disjoint` s2)

val modifies_union_loc_of_loc
  (#al: (bool -> Tot aloc_t)) (c: (b: bool) -> Tot (cls (al b)))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2 <==> modifies #_ #(c b) l h1 h2)
