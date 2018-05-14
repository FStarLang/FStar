module FStar.ModifiesGen

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

noeq
type aloc (c: class) : Type0 = | ALoc:
  (region: HS.rid) ->
  (addr: nat) ->
  (loc: c.aloc region addr) ->
  aloc c

let aloc_domain (c: class) (regions: Ghost.erased (Set.set HS.rid)) (addrs: ((r: HS.rid { Set.mem r (Ghost.reveal regions) } ) -> GTot (Set.set nat))) : GTot (GSet.set (aloc c)) =
  GSet.comprehend (fun a -> Set.mem a.region (Ghost.reveal regions) && Set.mem a.addr (addrs a.region))

noeq
type loc' (c: class) : Type =
  | Loc:
      (regions: Ghost.erased (Set.set HS.rid)) ->
      (region_liveness_tags: Ghost.erased (Set.set HS.rid) { Ghost.reveal region_liveness_tags `Set.subset` Ghost.reveal regions } ) ->
      (addrs: (
	(r: HS.rid { Set.mem r (Ghost.reveal regions) } ) ->
	GTot (Set.set nat)
      )) ->
      (aux_addrs: (
	(r: HS.rid { Set.mem r (Ghost.reveal regions) } ) ->
	GTot (Set.set nat)
      )) ->
      (aux_addrs_disjoint: ((r: HS.rid { Set.mem r (Ghost.reveal regions) } ) -> Lemma (Set.subset (Set.intersect (aux_addrs r) (addrs r)) Set.empty ))) ->
      (aux: Ghost.erased (GSet.set (aloc c)) {
        aloc_domain c regions addrs `GSet.subset` Ghost.reveal aux /\
        Ghost.reveal aux `GSet.subset` (aloc_domain c regions addrs `GSet.union` aloc_domain c regions aux_addrs)
      } ) ->
      loc' c

let loc = loc'

let loc_none #c = Loc
  (Ghost.hide (Set.empty))
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (fun _ -> Set.empty)
  (fun _ -> ())
  (Ghost.hide GSet.empty)

let regions_of_loc
  (#c: class)
  (s: loc c)
: GTot (Set.set HS.rid)
= Ghost.reveal (Loc?.regions s)

let addrs_of_loc_weak
  (#c: class)
  (l: loc c)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_aux
  (#c: class)
  (l: loc c)
  (r: HS.rid)
: GTot (y: Set.set nat { Set.subset (Set.intersect y (addrs_of_loc_weak l r)) Set.empty } )
= if Set.mem r (regions_of_loc l)
  then (Loc?.aux_addrs_disjoint l r; Loc?.aux_addrs l r)
  else Set.empty

let addrs_of_loc
  (#c: class)
  (l: loc c)
  (r: HS.rid)
: GTot (Set.set nat)
= Set.union
    (addrs_of_loc_weak l r)
    (addrs_of_loc_aux l r)

let addrs_of_loc_aux_prop
  (#c: class)
  (l: loc c)
  (r: HS.rid)
: Lemma
  (Set.subset (Set.intersect (addrs_of_loc_aux l r) (addrs_of_loc_weak l r)) Set.empty)
  [SMTPatOr [
    [SMTPat (addrs_of_loc_aux l r)];
    [SMTPat (addrs_of_loc_weak l r)];
    [SMTPat (addrs_of_loc l r)];
  ]]
= ()

let loc_union #c s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in
  let regions = Set.union regions1 regions2 in
  let addrs
    (r: HS.rid { Set.mem r regions } )
  : GTot (Set.set nat)
  = Set.union
      (if Set.mem r regions1 then addrs_of_loc_weak s1 r else Set.empty)
      (if Set.mem r regions2 then addrs_of_loc_weak s2 r else Set.empty)
  in
  let aux_addrs
    (r: HS.rid { Set.mem r regions } )
  : Ghost (Set.set nat)
    (requires True)
    (ensures (fun y -> Set.subset (Set.intersect y (addrs r)) Set.empty))
  = Set.intersect
      (Set.union (addrs_of_loc_aux s1 r) (addrs_of_loc_aux s2 r))
      (Set.complement (addrs r))
  in
  let aux = Ghost.hide
      (Ghost.reveal (Loc?.aux s1) `GSet.union` Ghost.reveal (Loc?.aux s2))
  in
  Loc
    (Ghost.hide regions)
    (Ghost.hide (Set.union (Ghost.reveal (Loc?.region_liveness_tags s1)) (Ghost.reveal (Loc?.region_liveness_tags s2))))
    addrs
    aux_addrs
    (fun _ -> ())
    aux

let fun_set_equal (#t: Type) (#t': eqtype) (f1 f2: (t -> GTot (Set.set t'))) : GTot Type0 =
  forall (x: t) . {:pattern (f1 x) \/ (f2 x) } f1 x `Set.equal` f2 x

let fun_set_equal_elim (#t: Type) (#t' : eqtype) (f1 f2: (t -> GTot (Set.set t'))) : Lemma
  (requires (fun_set_equal f1 f2))
  (ensures (f1 == f2))
  [SMTPat (fun_set_equal f1 f2)]
= assert (f1 `FunctionalExtensionality.gfeq` f2)

let loc_equal (#c: class) (s1 s2: loc c) : GTot Type0 =
  let Loc regions1 region_liveness_tags1 addrs1 aux_addrs1 _ aux1 = s1 in
  let Loc regions2 region_liveness_tags2 addrs2 aux_addrs2 _ aux2 = s2 in
  Ghost.reveal regions1 `Set.equal` Ghost.reveal regions2 /\
  Ghost.reveal region_liveness_tags1 `Set.equal` Ghost.reveal region_liveness_tags2 /\
  fun_set_equal (Loc?.addrs s1) (Loc?.addrs s2) /\
  fun_set_equal (Loc?.aux_addrs s1) (Loc?.aux_addrs s2) /\
  Ghost.reveal (Loc?.aux s1) `GSet.equal` Ghost.reveal (Loc?.aux s2)

let loc_equal_elim (#c: class) (s1 s2: loc c) : Lemma
  (requires (loc_equal s1 s2))
  (ensures (s1 == s2))
  [SMTPat (s1 `loc_equal` s2)]
= assert (Loc?.aux_addrs_disjoint s1 `FunctionalExtensionality.gfeq` Loc?.aux_addrs_disjoint s2)

let loc_union_idem #c s =
  assert (loc_union s s `loc_equal` s)

let loc_union_comm #c s1 s2 =
  assert (loc_union s1 s2 `loc_equal` loc_union s2 s1)

let loc_union_assoc #c s1 s2 s3 =
  assert (loc_union s1 (loc_union s2 s3) `loc_equal` loc_union (loc_union s1 s2) s3)

let loc_union_loc_none_l #c s =
  assert (loc_union loc_none s `loc_equal` s)

let loc_union_loc_none_r #c s =
  assert (loc_union s loc_none `loc_equal` s)

let loc_of_aloc #c #r #n b =
    Loc
      (Ghost.hide (Set.singleton r))
      (Ghost.hide Set.empty)
      (fun _ -> Set.empty)
      (fun _ -> Set.singleton n)
      (fun _ -> ())
      (Ghost.hide (GSet.singleton (ALoc r n b)))

let loc_addresses #c r n =
  let regions = (Ghost.hide (Set.singleton r)) in
  Loc
    regions
    (Ghost.hide Set.empty)
    (fun _ -> n)
    (fun _ -> Set.empty)
    (fun _ -> ())
    (Ghost.hide (aloc_domain c regions (fun _ -> n)))

let loc_regions #c r =
  let addrs (r' : HS.rid { Set.mem r' r } ) : GTot (Set.set nat) =
    Set.complement Set.empty
  in
  Loc
    (Ghost.hide r)
    (Ghost.hide r)
    addrs
    (fun _ -> Set.empty)
    (fun _ -> ())
    (Ghost.hide (aloc_domain c (Ghost.hide r) addrs))

let aloc_includes (#c: class) (b0 b: aloc c) : GTot Type0 =
  b0.region == b.region /\ b0.addr == b.addr /\ c.aloc_includes b0.loc b.loc

let loc_aux_includes_buffer
  (#c: class)
  (s: GSet.set (aloc c))
  (b: aloc c)
: GTot Type0
  (decreases s)
= exists (b0 : aloc c) . b0 `GSet.mem` s /\ b0 `aloc_includes` b

let loc_aux_includes
  (#c: class)
  (s1 s2: GSet.set (aloc c))
: GTot Type0
  (decreases s2)
= forall (b2: aloc c) . GSet.mem b2 s2 ==> loc_aux_includes_buffer s1 b2

let loc_aux_includes_union_l
  (#c: class)
  (s1 s2 s: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s \/ loc_aux_includes s2 s))
  (ensures (loc_aux_includes (GSet.union s1 s2) s))
  (decreases s)
= ()

let loc_aux_includes_refl
  (#c: class)
  (s: GSet.set (aloc c))
: Lemma
  (loc_aux_includes s s)
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset
  (#c: class)
  (s1 s2: GSet.set (aloc c))
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset'
  (#c: class)
  (s1 s2: GSet.set (aloc c))
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
  [SMTPatOr [
    [SMTPat (s1 `GSet.subset` s2)];
    [SMTPat (loc_aux_includes s2 s1)];
  ]]
= loc_aux_includes_subset s1 s2

let loc_aux_includes_union_l_r
  (#c: class)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s s') s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s s' s

let loc_aux_includes_union_l_l
  (#c: class)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s' s) s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s' s s

let loc_aux_includes_buffer_includes
  (#c: class)
  (s: GSet.set (aloc c))
  (b1 b2: aloc c)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `aloc_includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let loc_aux_includes_loc_aux_includes_buffer
  (#c: class)
  (s1 s2: GSet.set (aloc c))
  (b: aloc c)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
= Classical.forall_intro_3 (fun s b1 b2 -> Classical.move_requires (loc_aux_includes_buffer_includes #c s b1) b2)

let loc_aux_includes_trans
  (#c: class)
  (s1 s2 s3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let addrs_of_loc_weak_loc_union
  (#c: class)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc_union
  (#c: class)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc (loc_union l1 l2) r) (Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes #c s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in (
    Set.subset regions2 regions1 /\
    Set.subset (Ghost.reveal (Loc?.region_liveness_tags s2)) (Ghost.reveal (Loc?.region_liveness_tags s1)) /\
    (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HS.rid) .
      Set.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      (Ghost.reveal (Loc?.aux s1)) `loc_aux_includes` (Ghost.reveal (Loc?.aux s2))
    )
  )

let loc_includes_refl #c s =
  loc_aux_includes_refl (Ghost.reveal (Loc?.aux s))

let loc_includes_refl'
  (#c: class)
  (s: loc c)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]
= loc_includes_refl s

let loc_includes_trans #c s1 s2 s3 =
  loc_aux_includes_trans (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s3))

let loc_includes_union_r #c s s1 s2 = ()

let loc_includes_union_l #c s1 s2 s =
  let u12 = loc_union s1 s2 in
    Classical.or_elim
      #(loc_includes s1 s)
      #(loc_includes s2 s)
      #(fun _ -> loc_includes (loc_union s1 s2) s)
      (fun _ ->
        loc_aux_includes_union_l_r (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2));
        assert (loc_includes (loc_union s1 s2) s1);
        loc_includes_trans u12 s1 s)
      (fun _ ->
        loc_aux_includes_union_l_l (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s1));
        assert (loc_includes (loc_union s1 s2) s2);
        loc_includes_trans u12 s2 s)

let loc_includes_none #c s = ()

let loc_includes_aloc #c #r #n b1 b2 = ()

let loc_includes_addresses_aloc #c r s #a p = ()

let loc_includes_region_aloc #c s #r #a b = ()

let loc_includes_region_addresses #c s r a = ()

let loc_includes_region_region #c s1 s2 = ()

let loc_includes_region_union_l #c l s1 s2 = ()


(* Disjointness of two memory locations *)

let aloc_disjoint (#c: class) (b1 b2: aloc c) : GTot Type0 =
  if b1.region = b2.region && b1.addr = b2.addr
  then c.aloc_disjoint b1.loc b2.loc
  else True

let aloc_disjoint_sym (#c: class) (b1 b2: aloc c) : Lemma
  (aloc_disjoint b1 b2 <==> aloc_disjoint b2 b1)
= Classical.forall_intro_2 (fun r a -> Classical.forall_intro_2 (fun b1 b2 -> c.aloc_disjoint_sym #r #a b1 b2))

let loc_aux_disjoint
  (#c: class)
  (l1 l2: GSet.set (aloc c))
: GTot Type0
= forall (b1 b2: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b2 l2) ==> aloc_disjoint b1 b2

let loc_aux_disjoint_union_l
  (#c: class)
  (ll1 lr1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint (GSet.union ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
= ()

let loc_aux_disjoint_union_r
  (#c: class)
  (l1 ll2 lr2: GSet.set (aloc c))
: Lemma
  (loc_aux_disjoint l1 (GSet.union ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let loc_aux_disjoint_sym
  (#c: class)
  (l1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
= Classical.forall_intro_2 (aloc_disjoint_sym #c)

let regions_of_loc_loc_union
  (#c: class)
  (s1 s2: loc c)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (#c: class)
  (s1 s2: loc c)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint_region_liveness_tags (#c: class) (l1 l2: loc c) : GTot Type0 =
  Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty

let loc_disjoint_addrs (#c: class) (l1 l2: loc c) : GTot Type0 =
  (forall (r: HS.rid) .
      Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
      Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty
  )

let loc_disjoint_aux (#c: class) (l1 l2: loc c) : GTot Type0 =
  loc_aux_disjoint (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2))

let loc_disjoint'
  (#c: class)
  (l1 l2: loc c)
: GTot Type0
= loc_disjoint_region_liveness_tags l1 l2 /\
  loc_disjoint_addrs l1 l2 /\
  loc_disjoint_aux l1 l2

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym #c l1 l2 =
  Classical.forall_intro_2 (loc_aux_disjoint_sym #c)

let loc_disjoint_sym'
  (#c: class)
  (s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
  [SMTPat (loc_disjoint s1 s2)]
= loc_disjoint_sym s1 s2

let loc_disjoint_none_r #c s = ()

let loc_disjoint_union_r #c s s1 s2 = ()

let aloc_disjoint_includes (#c: class) (b1 b2 b3 : aloc c) : Lemma
  (requires (aloc_disjoint b1 b2 /\ aloc_includes b2 b3))
  (ensures (aloc_disjoint b1 b3))
= if b1.region = b2.region && b1.addr = b2.addr
  then begin
    c.aloc_includes_refl b1.loc;
    c.aloc_disjoint_includes b1.loc b2.loc b1.loc b3.loc
  end
  else ()

let loc_aux_disjoint_loc_aux_includes
  (#c: class)
  (l1 l2 l3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= // FIXME: WHY WHY WHY do I need this assert?
  assert (forall (b1 b3: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b3 l3) ==> (exists (b2: aloc c) . GSet.mem b2 l2 /\ aloc_disjoint b1 b2 /\ aloc_includes b2 b3));
  Classical.forall_intro_3 (fun b1 b2 b3 -> Classical.move_requires (aloc_disjoint_includes #c b1 b2) b3)

let loc_disjoint_includes #c p1 p2 p1' p2' =
  regions_of_loc_monotonic p1 p1';
  regions_of_loc_monotonic p2 p2';
  let l1 = Ghost.reveal (Loc?.aux p1) in
  let l2 = Ghost.reveal (Loc?.aux p2) in
  let l1' = Ghost.reveal (Loc?.aux p1') in
  let l2' = Ghost.reveal (Loc?.aux p2') in
  loc_aux_disjoint_loc_aux_includes l1 l2 l2';
  loc_aux_disjoint_sym l1 l2';
  loc_aux_disjoint_loc_aux_includes l2' l1 l1';
  loc_aux_disjoint_sym l2' l1'

let loc_disjoint_aloc #c #r1 #a1 #r2 #b2 b1 b2 = ()

let loc_disjoint_addresses #c r1 r2 n1 n2 = ()

let loc_disjoint_aloc_addresses #c #r' #a' p r n = ()

let loc_disjoint_regions #c rs1 rs2 = ()


(** The modifies clause proper *)

let modifies_preserves_mreferences
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (Set.mem (HS.as_addr p) (addrs_of_loc s r)))
    ) ==> (
      HS.contains h2 p /\
      HS.sel h2 p == HS.sel h1 p
  ))

let modifies_preserves_mreferences_intro
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
  (f: (
    (t: Type) ->
    (pre: Preorder.preorder t) ->
    (p: HS.mreference t pre) ->
    Lemma
    (requires (
      HS.contains h1 p /\
      (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (Set.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))
    ))
    (ensures (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p))
  ))
: Lemma
  (modifies_preserves_mreferences s h1 h2)
= let f'
    (t : Type)
    (pre: Preorder.preorder t)
    (p : HS.mreference t pre)
  : Lemma
    (
  (HS.contains h1 p /\ (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (Set.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))) ==>
    (h2 `HS.contains` p /\ h2 `HS.sel` p == h1 `HS.sel` p))
  = Classical.move_requires (f t pre) p
  in
  Classical.forall_intro_3 f'

let modifies_preserves_alocs
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (r: HS.rid) (a: nat) (b: c.aloc r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a b))
    ==>
    c.aloc_preserved b h1 h2
  )

let modifies_preserves_alocs_intro
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
  (u: unit { modifies_preserves_mreferences s h1 h2 } )
  (f: (
    (r: HS.rid) ->
    (a: nat) ->
    (b: c.aloc r a) ->
    Lemma
    (requires (
      Set.mem r (regions_of_loc s) /\ 
      (~ (Set.mem a (addrs_of_loc_weak s r))) /\
      (Set.mem a (addrs_of_loc_aux s r) ==> loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a b)))
    ))
    (ensures (c.aloc_preserved b h1 h2))
  ))
: Lemma
  (modifies_preserves_alocs s h1 h2)
= let f'
    (r: HS.rid)
    (a: nat)
    (b: c.aloc r a)
  : Lemma
    (requires (loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a b))))
    (ensures (c.aloc_preserved b h1 h2))
  = if Set.mem r (regions_of_loc s) && (not (Set.mem a (addrs_of_loc_weak s r)))
    then
      Classical.move_requires (f r a) b
    else if Set.mem r (regions_of_loc s)
    then begin
      assert (Set.mem a (addrs_of_loc_weak s r));
      assert (GSet.mem (ALoc r a b) (Ghost.reveal (Loc?.aux s)));
      assert (aloc_disjoint (ALoc r a b) (ALoc r a b));
      c.aloc_disjoint_self_preserved b h1 h2
    end
    else
      c.same_mreference_aloc_preserved b h1 h2 (fun a' pre' r' -> ())
  in
  Classical.forall_intro_3 (fun r a b -> Classical.move_requires (f' r a) b)

let modifies_preserves_regions
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= forall (r: HS.rid) . (HS.live_region h1 r /\ ~ (Set.mem r (Ghost.reveal (Loc?.region_liveness_tags s)))) ==> HS.live_region h2 r

let modifies'
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_regions s h1 h2 /\
  modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_alocs s h1 h2

let modifies = modifies'

let modifies_live_region #c s h1 h2 r = ()

let modifies_mreference_elim #c #t #pre b p h h' = ()

let modifies_aloc_elim #c #r #a b p h h' = ()

let modifies_refl #c s h =
  Classical.forall_intro_3 (fun r a b -> c.aloc_preserved_refl #r #a b h)

let modifies_loc_includes #c s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro_2 (loc_aux_disjoint_sym #c);
  Classical.forall_intro_3 (fun l1 l2 l3 -> Classical.move_requires (loc_aux_disjoint_loc_aux_includes #c l1 l2) l3);
  assert (modifies_preserves_alocs s1 h h')

let modifies_trans'
  (#c: class)
  (s: loc c)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (c.aloc_preserved_trans #r #a b h1 h2) h3)

let modifies_trans #c s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

let addr_unused_in_aloc_preserved
    (#c: class)
    (#r: HS.rid)
    (#a: nat)
    (b: c.aloc r a)
    (h1: HS.mem)
    (h2: HS.mem)
  : Lemma
    (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel h1.HS.h r)))
    (ensures (c.aloc_preserved b h1 h2))
= c.same_mreference_aloc_preserved b h1 h2 (fun a' pre r' -> assert False)

let modifies_only_live_regions_weak
  (#c: class)
  (rs: Set.set HS.rid)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (addr_unused_in_aloc_preserved #c #r #a b h) h')

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
: GTot (loc c)
= let (Loc regions region_liveness_tags addrs aux_addrs aux_addrs_disjoint aux) = l in
  Loc
    (Ghost.hide (Set.intersect (Ghost.reveal regions) rs))
    (Ghost.hide (Set.intersect (Ghost.reveal region_liveness_tags) rs))
    (fun r -> addrs r)
    (fun r -> aux_addrs r)
    (fun r -> aux_addrs_disjoint r)
    (Ghost.hide (GSet.intersect (Ghost.reveal aux) (aloc_domain c (Ghost.hide rs) (fun r -> Set.complement Set.empty))))

let regions_of_loc_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else Set.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else Set.empty))

let loc_includes_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #c)

let loc_includes_loc_union_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_equal (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= ()

let loc_includes_loc_regions_restrict_to_regions
  (#c: class)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #c)

let modifies_only_live_regions #c rs l h h' =
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h h' (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions #c rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region #c r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let modifies_fresh_frame_popped #c h0 h1 s h2 h3 =
  let f01 (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (c.aloc_preserved b h0 h1)
  = c.same_mreference_aloc_preserved #r #a b h0 h1 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 f01;
  let s' = loc_union (loc_all_regions_from h1.HS.tip) s in
  modifies_loc_includes s' h0 h1 loc_none;
  let f23 (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (requires (r <> h2.HS.tip))
    (ensures (c.aloc_preserved b h2 h3))
  = c.same_mreference_aloc_preserved #r #a b h2 h3 (fun a' pre r' -> ())
  in
  let s23 = loc_region_only #c h2.HS.tip in
  assert (modifies_preserves_mreferences s23 h2 h3);
  modifies_preserves_alocs_intro s23 h2 h3 () (fun r a b ->
    f23 r a b
  );
  modifies_loc_includes s' h2 h3 s23;
  modifies_trans' s' h1 h2 h3;
  modifies_trans' s' h0 h1 h3;
  modifies_only_live_regions (HS.mod_set (Set.singleton h1.HS.tip)) s h0 h3

let modifies_loc_regions_intro #c rs h1 h2 =
  let f (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (requires (not (Set.mem r rs)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  assert (modifies_preserves_mreferences (loc_regions #c rs) h1 h2);
  modifies_preserves_alocs_intro (loc_regions rs) h1 h2 () (fun r a b ->
    f r a b
  )

let modifies_loc_addresses_intro_weak
  (#c: class)
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc c)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only r) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    loc_disjoint l (loc_region_only r)
  ))
  (ensures (modifies (loc_union (loc_addresses r s) l) h1 h2))
= assert (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) . ((HS.frameOf p == r /\ HS.contains h1 p /\ ~ (Set.mem (HS.as_addr p) s)) ==> (HS.contains h2 p /\ HS.sel h2 p == HS.sel h1 p))) ;
  assert (modifies_preserves_mreferences (loc_union (loc_addresses r s) l) h1 h2);
  let f (a: nat) (b: c.aloc r a) : Lemma
    (requires (not (Set.mem a s)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r_ -> ())
  in
  modifies_preserves_alocs_intro (loc_union (loc_addresses r s) l) h1 h2 () (fun r' a b -> if r = r' then f a b else ()
  )

let modifies_loc_addresses_intro #c r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  modifies_loc_addresses_intro_weak r s (restrict_to_regions l (Set.complement (Set.singleton r))) h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))

let modifies_ralloc_post #c #a #rel i init h x h' =
  let g (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_salloc_post #c #a #rel init h x h' =
  let g (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_free #c #a #rel r m =
  let g (r': HS.rid) (a: nat) (b: c.aloc r' a) : Lemma
    (requires (r' <> HS.frameOf r \/ a <> HS.as_addr r))
    (ensures (c.aloc_preserved b m (HS.free r m)))
  = c.same_mreference_aloc_preserved #r' #a b m (HS.free r m) (fun a' pre r' -> ())
  in
  modifies_preserves_alocs_intro (loc_mreference r) m (HS.free r m) () (fun r a b -> g r a b)

let modifies_none_modifies #c h1 h2
= let g (r: HS.rid) (a: nat) (b: c.aloc r a) : Lemma
    (c.aloc_preserved b h1 h2)
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g


let does_not_contain_addr' (h: HS.mem) (ra: HS.rid * nat) : GTot Type0 =
  forall (a: Type) (rel: Preorder.preorder a) (r: HS.mreference a rel) . {:pattern (h `HS.contains` r) } (HS.frameOf r == fst ra /\ HS.as_addr r == snd ra /\ h `HS.contains` r) ==> False

let does_not_contain_addr = does_not_contain_addr'

let not_live_region_does_not_contain_addr h ra = ()

let unused_in_does_not_contain_addr h #a #rel r = ()

let addr_unused_in_does_not_contain_addr h ra = ()

let free_does_not_contain_addr #a #rel r m x = ()

let does_not_contain_addr_elim #a #rel r m x = ()

let modifies_only_live_addresses_weak
  (#c: class)
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    loc_disjoint (loc_addresses r a) l /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
= assert (modifies_preserves_mreferences l h h');
  modifies_preserves_alocs_intro l h h' () (fun r' a' b' ->
    if r = r' && Set.mem a' a
    then c.same_mreference_aloc_preserved #r' #a' b' h h' (fun a_ pre_ r_ -> ())
    else ()
  )

(* Restrict a set of locations along a set of addresses in a given region *)

let restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Ghost (loc c)
  (requires (loc_region_only r `loc_includes` l))
  (ensures (fun _ -> True))
= let (Loc regions region_liveness_tags addrs aux_addrs aux_addrs_disjoint aux) = l in
  let regions' = ((Set.intersect (Ghost.reveal regions) (Set.singleton r))) in
  let addrs' (r' : HS.rid { Set.mem r' regions' } ) : GTot (Set.set nat) =
    if (* r' = r && *) Set.mem r (Ghost.reveal regions)
    then Set.intersect (addrs r) as
    else Set.empty
  in
  let aux_addrs' (r' : HS.rid { Set.mem r' regions' } ) : GTot (Set.set nat) =
    if (* r = r' && *) Set.mem r (Ghost.reveal regions)
    then Set.intersect (aux_addrs r') as
    else Set.empty
  in
    Loc
      (Ghost.hide regions')
      (Ghost.hide (if include_liveness_tag then Set.intersect (Ghost.reveal region_liveness_tags) (Set.singleton r) else Set.empty))
      addrs'
      aux_addrs'
      (fun r -> aux_addrs_disjoint r)
      (Ghost.hide (GSet.intersect (Ghost.reveal aux) (aloc_domain c (Ghost.hide regions') (aux_addrs')) `GSet.union` (aloc_domain c (Ghost.hide regions') addrs')))

let regions_of_loc_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (regions_of_loc (restrict_to_addresses l r include_liveness_tag as) == Set.intersect (regions_of_loc l) (Set.singleton r)))
  [SMTPat (regions_of_loc (restrict_to_addresses l r include_liveness_tag as))]
= assert (regions_of_loc (restrict_to_addresses l r include_liveness_tag as) `Set.equal` Set.intersect (regions_of_loc l) (Set.singleton r))

let addrs_of_loc_weak_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (addrs_of_loc_weak (restrict_to_addresses l r include_liveness_tag as) r' == (if r = r' then Set.intersect (addrs_of_loc_weak l r) as else Set.empty)))
  [SMTPat (addrs_of_loc_weak (restrict_to_addresses l r include_liveness_tag as) r')]
= assert (addrs_of_loc_weak (restrict_to_addresses l r include_liveness_tag as) r `Set.equal` Set.intersect (addrs_of_loc_weak l r) as)

let addrs_of_loc_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
  (r' : HS.rid)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (addrs_of_loc (restrict_to_addresses l r include_liveness_tag as) r' == (if r = r' then Set.intersect (addrs_of_loc l r) as else Set.empty)))
  [SMTPat (addrs_of_loc (restrict_to_addresses l r include_liveness_tag as) r')]
= assert (addrs_of_loc (restrict_to_addresses l r include_liveness_tag as) r `Set.equal` Set.intersect (addrs_of_loc l r) as);
  assert (r <> r' ==> addrs_of_loc (restrict_to_addresses l r include_liveness_tag as) r' `Set.equal` Set.empty)

let loc_includes_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes l (restrict_to_addresses l r include_liveness_tag as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset #c s1) s2)

let loc_includes_loc_union_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_equal (loc_union (restrict_to_addresses l r false as) (restrict_to_addresses l r true (Set.complement as))) l))
= ()

let loc_includes_loc_addresses_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes (loc_addresses r as) (restrict_to_addresses l r false as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset #c s1) s2)

#set-options "--z3rlimit 32"

let loc_disjoint_restrict_to_addresses
  (#c: class)
  (l: loc c)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_addresses r as `loc_disjoint` restrict_to_addresses l r true (Set.complement as)))
= ()

#reset-options

let modifies_only_live_addresses #c r a l h h' =
  let l_r = restrict_to_regions l (Set.singleton r) in
  let l_not_r = restrict_to_regions l (Set.complement (Set.singleton r)) in
  let l_a = restrict_to_addresses l_r r false a in
  let l_r_not_a = restrict_to_addresses l_r r true (Set.complement a) in
  let l_not_a = loc_union l_r_not_a l_not_r in
  let l' = loc_union (loc_addresses r a) l_not_a in
  loc_includes_loc_addresses_restrict_to_addresses l_r r a;
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_addresses l_r r a;
  loc_includes_trans (loc_union (loc_union l_a l_r_not_a) l_not_r) (loc_union l_r l_not_r) l;
  loc_includes_trans (loc_union l_a l_not_a) (loc_union (loc_union l_a l_r_not_a) l_not_r) l;
  loc_includes_trans l' (loc_union l_a l_not_a) l;
  modifies_loc_includes (loc_union (loc_addresses r a) l_not_a) h h' (loc_union (loc_addresses r a) l);
  loc_disjoint_restrict_to_addresses l_r r a;
  loc_includes_loc_regions_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_region_addresses #c (Set.singleton r) r a;
  loc_disjoint_regions #c (Set.singleton r) (Set.complement (Set.singleton r));
  loc_disjoint_includes (loc_region_only r) (loc_regions (Set.complement (Set.singleton r))) (loc_addresses r a) l_not_r;
  loc_disjoint_union_r (loc_addresses r a) l_r_not_a l_not_r;
  modifies_only_live_addresses_weak r a l_not_a h h';
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_restrict_to_addresses l_r r true (Set.complement a);
  modifies_loc_includes l h h' l_not_a


(* * Compositionality *)

noeq
type class_union_aloc (c: (bool -> Tot class)) (r: HS.rid) (n: nat) : Type0 =
  | ALOC_FALSE of (c false).aloc r n
  | ALOC_TRUE  of (c true).aloc r n

let bool_of_class_union_aloc (#c: (bool -> Tot class)) (#r: HS.rid) (#n: nat) (l: class_union_aloc c r n) : Tot bool =
  match l with
  | ALOC_FALSE _ -> false
  | ALOC_TRUE _ -> true

let aloc_of_class_union_aloc (#c: (bool -> Tot class)) (#r: HS.rid) (#n: nat) (l: class_union_aloc c r n) : Tot ((c (bool_of_class_union_aloc l)).aloc r n) =
  match l with
  | ALOC_FALSE x -> x
  | ALOC_TRUE x -> x

let make_class_union_aloc (c: (bool -> Tot class)) (b: bool) (#r: HS.rid) (#n: nat) (l: (c b).aloc r n) : Tot (class_union_aloc c r n) =
  if b
  then ALOC_TRUE l
  else ALOC_FALSE l

let class_union_aloc_includes
  (c: (bool -> Tot class))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: class_union_aloc c r a)
: GTot Type0 =
  bool_of_class_union_aloc larger == bool_of_class_union_aloc smaller /\
  (c (bool_of_class_union_aloc larger)).aloc_includes
    (aloc_of_class_union_aloc larger)
    (aloc_of_class_union_aloc smaller)

let class_union_aloc_disjoint
  (c: (bool -> Tot class))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: class_union_aloc c r a)
: GTot Type0 =
  bool_of_class_union_aloc larger == bool_of_class_union_aloc smaller /\
  (c (bool_of_class_union_aloc larger)).aloc_disjoint
    (aloc_of_class_union_aloc larger)
    (aloc_of_class_union_aloc smaller)

let class_union_aloc_preserved
  (c: (bool -> Tot class))
  (#r: HS.rid)
  (#a: nat)
  (x: class_union_aloc c r a)
  (h h' : HS.mem)
: GTot Type0
= (c (bool_of_class_union_aloc x)).aloc_preserved
    (aloc_of_class_union_aloc x)
    h
    h'

let class_union c = Class
  (class_union_aloc c)
  (class_union_aloc_includes c)
  (* aloc_includes_refl *)
  (fun #r #a x ->
    (c (bool_of_class_union_aloc x)).aloc_includes_refl (aloc_of_class_union_aloc x))  
  (* aloc_includes_trans *)
  (fun #r #a x1 x2 x3 ->
    (c (bool_of_class_union_aloc x1)).aloc_includes_trans
      (aloc_of_class_union_aloc x1)
      (aloc_of_class_union_aloc x2)
      (aloc_of_class_union_aloc x3)
  )
  (class_union_aloc_disjoint c)
  (* aloc_disjoint_sym *)
  (fun #r #a x1 x2 ->
    if bool_of_class_union_aloc x1 = bool_of_class_union_aloc x2
    then
      (c (bool_of_class_union_aloc x1)).aloc_disjoint_sym
        (aloc_of_class_union_aloc x1)
        (aloc_of_class_union_aloc x2)
    else ()
  )
  (* aloc_disjoint_includes *)
  (fun #r #a larger1 larger2 smaller1 smaller2 ->
    (c (bool_of_class_union_aloc larger1)).aloc_disjoint_includes
      (aloc_of_class_union_aloc larger1)
      (aloc_of_class_union_aloc larger2)
      (aloc_of_class_union_aloc smaller1)
      (aloc_of_class_union_aloc smaller2)
  )
  (class_union_aloc_preserved c)
  (* aloc_preserved_refl *)
  (fun #r #a x h ->
    (c (bool_of_class_union_aloc x)).aloc_preserved_refl
      (aloc_of_class_union_aloc x)
      h
  )
  (* aloc_preserved_trans *)
  (fun #r #a x h1 h2 h3 ->
    (c (bool_of_class_union_aloc x)).aloc_preserved_trans
      (aloc_of_class_union_aloc x)
      h1
      h2
      h3
  )
  (* same_mreference_aloc_preserved *)
  (fun #r #a b h1 h2 f ->
    (c (bool_of_class_union_aloc b)).same_mreference_aloc_preserved
      (aloc_of_class_union_aloc b)
      h1
      h2
      f
  )
  (* aloc_disjoint_self_preserved *)
  (fun #r #a b h1 h2 ->
    (c (bool_of_class_union_aloc b)).aloc_disjoint_self_preserved
      (aloc_of_class_union_aloc b)
      h1
      h2
  )

let union_aux_of_aux_left
  (c: (bool -> Tot class))
  (b: bool)
  (s: GSet.set (aloc (c b)))
: Tot (GSet.set (aloc (class_union c)))
= GSet.comprehend (fun x ->
      let ALoc region addr loc = x in
      b = bool_of_class_union_aloc #c #region #addr loc &&
      GSet.mem (ALoc region addr (aloc_of_class_union_aloc #c #region #addr loc)) s
    )

let union_loc_of_loc c b l =
  let (Loc regions region_liveness_tags addrs aux_addrs aux_addrs_disjoint aux) = l in
  let aux' =
    union_aux_of_aux_left c b (Ghost.reveal aux)
    `GSet.union`
    (aloc_domain (class_union c) regions addrs)
  in
  Loc
    #(class_union c)
    regions
    region_liveness_tags
    addrs
    aux_addrs
    aux_addrs_disjoint
    (Ghost.hide aux')

let mem_union_aux_of_aux_left_intro
  (c: (bool -> Tot class))
  (b: bool)
  (x: aloc (c b))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x aux <==> GSet.mem (ALoc x.region x.addr (make_class_union_aloc c b x.loc)) (union_aux_of_aux_left c b aux))
  [SMTPat (GSet.mem x aux)]
= ()

let mem_union_aux_of_aux_left_elim
  (c: (bool -> Tot class))
  (b: bool)
  (x: aloc (class_union c))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x (union_aux_of_aux_left c b aux) <==> (bool_of_class_union_aloc x.loc == b /\ GSet.mem (ALoc x.region x.addr (aloc_of_class_union_aloc x.loc)) aux))
  [SMTPat (GSet.mem x (union_aux_of_aux_left c b aux))]
= ()

let union_loc_of_loc_none c b =
  assert (loc_equal #(class_union c) (union_loc_of_loc c b (loc_none #(c b)))  (loc_none #(class_union c)))

let union_loc_of_loc_union c b l1 l2 =
  assert (loc_equal #(class_union c) (union_loc_of_loc c b (loc_union #(c b) l1 l2)) (loc_union #(class_union c) (union_loc_of_loc c b l1) (union_loc_of_loc c b l2)))

let union_loc_of_loc_addresses c b r n =
  assert (loc_equal #(class_union c) (union_loc_of_loc c b (loc_addresses #(c b) r n)) (loc_addresses #(class_union c) r n))

let union_loc_of_loc_regions c b r =
  assert (loc_equal #(class_union c) (union_loc_of_loc c b (loc_regions #(c b) r)) (loc_regions #(class_union c) r))

let union_loc_of_loc_includes_intro
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_includes` smaller))
  (ensures (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
= let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  assert (auxl `loc_aux_includes` auxs);
  let doml = aloc_domain (class_union c) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (class_union c) (Loc?.regions smaller) (Loc?.addrs smaller) in
  assert (doml `loc_aux_includes` doms)

let union_loc_of_loc_includes_elim
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
  (ensures (larger `loc_includes` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  let doml' = aloc_domain (class_union c) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms' = aloc_domain (class_union c) (Loc?.regions smaller) (Loc?.addrs smaller) in
  let doml = aloc_domain (c b) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (c b) (Loc?.regions smaller) (Loc?.addrs smaller) in
  assert_spinoff (* assert FAILS *) (forall (r: HS.rid) (a: nat) (x: aloc (c b)) .
    GSet.mem x auxs ==> (
    if Set.mem x.addr (addrs_of_loc_weak smaller x.region)
    then
      GSet.mem x (GSet.union auxl doml)
    else
      let ALoc xr xa xl = x in
      let xloc' = make_class_union_aloc c b xl in
      let x' = ALoc xr xa xloc' in (
      exists (y' : aloc (class_union c)) . (
      GSet.mem y' (GSet.union auxl' doml') /\
      y' `aloc_includes` x' /\ (
      let ALoc yr' ya' yloc' = y' in
      let yloc = aloc_of_class_union_aloc yloc' in
      let y: aloc (c b) = ALoc yr' ya' yloc in
      y `aloc_includes` x /\
      GSet.mem y auxl
    )))))

let union_loc_of_loc_includes c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_includes_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_includes_intro c b s1) s2

let union_loc_of_loc_disjoint_intro
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_disjoint` smaller))
  (ensures (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
= let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  assert (forall x . GSet.mem x auxl ==> bool_of_class_union_aloc #c #x.region #x.addr x.loc == b);
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> (bool_of_class_union_aloc #c #xl.region #xl.addr xl.loc == b /\ bool_of_class_union_aloc #c #xs.region #xs.addr xs.loc == b /\  aloc_disjoint (ALoc xl.region xl.addr (aloc_of_class_union_aloc #c #xl.region #xl.addr xl.loc)) (ALoc xs.region xs.addr (aloc_of_class_union_aloc #c #xs.region #xs.addr xs.loc))));
  assert (forall (xl xs: aloc (class_union c)) . (bool_of_class_union_aloc #c #xl.region #xl.addr xl.loc == b /\ bool_of_class_union_aloc #c #xs.region #xs.addr xs.loc == b /\  aloc_disjoint (ALoc xl.region xl.addr (aloc_of_class_union_aloc #c #xl.region #xl.addr xl.loc)) (ALoc xs.region xs.addr (aloc_of_class_union_aloc #c #xs.region #xs.addr xs.loc))) ==> aloc_disjoint xl xs);
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> aloc_disjoint xl xs);
  assert (auxl `loc_aux_disjoint` auxs)

let union_loc_of_loc_disjoint_elim
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
  (ensures (larger `loc_disjoint` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  assert (forall x y . (GSet.mem x auxl /\ GSet.mem y auxs) ==> (
    let x' = ALoc x.region x.addr (make_class_union_aloc c b x.loc) in
    let y' = ALoc y.region y.addr (make_class_union_aloc c b y.loc) in
    GSet.mem x' auxl' /\ GSet.mem y' auxs' /\ (aloc_disjoint x' y' ==> aloc_disjoint x y))); 
  assert (auxl `loc_aux_disjoint` auxs)

let union_loc_of_loc_disjoint c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_disjoint_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_disjoint_intro c b s1) s2

(*
  assert (forall x . GSet.mem x auxl ==> bool_of_class_union_aloc #c #x.region #x.addr x.loc == b);
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> (bool_of_class_union_aloc #c #xl.region #xl.addr xl.loc == b /\ bool_of_class_union_aloc #c #xs.region #xs.addr xs.loc == b /\  aloc_disjoint (ALoc xl.region xl.addr (aloc_of_class_union_aloc #c #xl.region #xl.addr xl.loc)) (ALoc xs.region xs.addr (aloc_of_class_union_aloc #c #xs.region #xs.addr xs.loc))));
  assert (forall (xl xs: aloc (class_union c)) . (bool_of_class_union_aloc #c #xl.region #xl.addr xl.loc == b /\ bool_of_class_union_aloc #c #xs.region #xs.addr xs.loc == b /\  aloc_disjoint (ALoc xl.region xl.addr (aloc_of_class_union_aloc #c #xl.region #xl.addr xl.loc)) (ALoc xs.region xs.addr (aloc_of_class_union_aloc #c #xs.region #xs.addr xs.loc))) ==> aloc_disjoint xl xs);
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> aloc_disjoint xl xs);
  assert (auxl `loc_aux_disjoint` auxs)

(*
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> aloc_disjoint xl xs);
  assert (larger `loc_disjoint` smaller ==> auxl `loc_aux_disjoint` auxs)

#set-options "--z3rlimit 32"

let union_loc_of_loc_includes_disjoint
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (larger `loc_disjoint` smaller ==> union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller)
= ()

let union_loc_of_loc_includes_elim
  (c: (bool -> Tot class))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
  (ensures (larger `loc_includes` smaller))
= let auxl =  (Ghost.reveal (Loc?.aux larger)) in
  let auxs = (Ghost.reveal (Loc?.aux smaller)) in
  assert (
  assume (auxl `loc_aux_includes` auxs);
  let doml = aloc_domain (c b) (Loc?.regions larger) (Loc?.addrs larger) in
  let doms = aloc_domain (c b) (Loc?.regions smaller) (Loc?.addrs smaller) in
  assert (doml `loc_aux_includes` doms)

let modifies_union_loc_of_loc_elim
  (c: (bool -> Tot class))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies #(class_union c) (union_loc_of_loc c b l) h1 h2))
  (ensures (modifies #(c b) l h1 h2))
= assert (modifies_preserves_regions l h1 h2);
  assert (modifies_preserves_mreferences l h1 h2);
  modifies_preserves_alocs_intro #(c b) l h1 h2 () (fun r' a' b' ->
    let g
      (x: aloc (class_union c))
    : Lemma
      (requires (
        Set.mem a' (addrs_of_loc_aux #(class_union c) (union_loc_of_loc c b l) r') /\
        GSet.mem x (Ghost.reveal (Loc?.aux #(class_union c) (union_loc_of_loc c b l)))
      ))
      (ensures (
        aloc_disjoint #(class_union c) x (ALoc #(class_union c) r' a' (make_class_union_aloc c b b'))))
    = if r' = x.region && a' = x.addr
      then begin
        let x' = (ALoc #(c b) r' a' (aloc_of_class_union_aloc x.loc)) in
        assert (aloc_disjoint #(c b) x' (ALoc r' a' b'));
        ()
      end else
        ()
    in
    Classical.forall_intro (Classical.move_requires g);
    assert ((class_union c).aloc_preserved (make_class_union_aloc c b b') h1 h2)
  )

(*
  assert (forall (s: GSet.set (aloc (class_union c))) (x: aloc (class_union c)) . GSet.mem x s ==> GSet.mem (ALoc x.region x.addr (make_class_union_aloc c b x.loc)) (
  assert (forall (r: HS.rid) (a: nat) (x: (c b).aloc r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r a x)) ==>
    loc_aux_disjoint #(class_union c) (Ghost.reveal (Loc?.aux #(class_union c) (union_loc_of_loc c b l))) (GSet.singleton (ALoc #(class_union c) r a (make_class_union_aloc c b x)))
  );
  assume (modifies_preserves_alocs l h1 h2)

let modifies_union_loc_of_loc c b l h1 h2 = ()
