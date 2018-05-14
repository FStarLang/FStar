module LowStar.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32

noeq
type abuffer = | ABuffer:
  (region: HS.rid) ->
  (addr: nat) ->
  (buffer: B.abuffer region addr) ->
  abuffer

let abuffer_domain (regions: Ghost.erased (Set.set HS.rid)) (addrs: ((r: HS.rid { Set.mem r (Ghost.reveal regions) } ) -> GTot (Set.set nat))) : GTot (GSet.set abuffer) =
  GSet.comprehend (fun a -> Set.mem a.region (Ghost.reveal regions) && Set.mem a.addr (addrs a.region))

noeq
type loc' : Type =
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
      (aux: Ghost.erased (GSet.set abuffer) {
        abuffer_domain regions addrs `GSet.subset` Ghost.reveal aux /\
        Ghost.reveal aux `GSet.subset` (abuffer_domain regions addrs `GSet.union` abuffer_domain regions aux_addrs)
      } ) ->
      loc'

let loc = loc'

let loc_none = Loc
  (Ghost.hide (Set.empty))
  (Ghost.hide (Set.empty))
  (fun _ -> Set.empty)
  (fun _ -> Set.empty)
  (fun _ -> ())
  (Ghost.hide GSet.empty)

let regions_of_loc
  (s: loc)
: GTot (Set.set HS.rid)
= Ghost.reveal (Loc?.regions s)

let addrs_of_loc_weak
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.addrs l r
  else Set.empty

let addrs_of_loc_aux
  (l: loc)
  (r: HS.rid)
: GTot (y: Set.set nat { Set.subset (Set.intersect y (addrs_of_loc_weak l r)) Set.empty } )
= if Set.mem r (regions_of_loc l)
  then (Loc?.aux_addrs_disjoint l r; Loc?.aux_addrs l r)
  else Set.empty

let addrs_of_loc
  (l: loc)
  (r: HS.rid)
: GTot (Set.set nat)
= Set.union
    (addrs_of_loc_weak l r)
    (addrs_of_loc_aux l r)

let addrs_of_loc_aux_prop
  (l: loc)
  (r: HS.rid)
: Lemma
  (Set.subset (Set.intersect (addrs_of_loc_aux l r) (addrs_of_loc_weak l r)) Set.empty)
  [SMTPatOr [
    [SMTPat (addrs_of_loc_aux l r)];
    [SMTPat (addrs_of_loc_weak l r)];
    [SMTPat (addrs_of_loc l r)];
  ]]
= ()

let loc_union s1 s2 =
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

let loc_equal (s1 s2: loc) : GTot Type0 =
  let Loc regions1 region_liveness_tags1 addrs1 aux_addrs1 _ aux1 = s1 in
  let Loc regions2 region_liveness_tags2 addrs2 aux_addrs2 _ aux2 = s2 in
  Ghost.reveal regions1 `Set.equal` Ghost.reveal regions2 /\
  Ghost.reveal region_liveness_tags1 `Set.equal` Ghost.reveal region_liveness_tags2 /\
  fun_set_equal (Loc?.addrs s1) (Loc?.addrs s2) /\
  fun_set_equal (Loc?.aux_addrs s1) (Loc?.aux_addrs s2) /\
  Ghost.reveal (Loc?.aux s1) `GSet.equal` Ghost.reveal (Loc?.aux s2)

let loc_equal_elim (s1 s2: loc) : Lemma
  (requires (loc_equal s1 s2))
  (ensures (s1 == s2))
  [SMTPat (s1 `loc_equal` s2)]
= assert (Loc?.aux_addrs_disjoint s1 `FunctionalExtensionality.gfeq` Loc?.aux_addrs_disjoint s2)

let loc_union_idem s =
  assert (loc_union s s `loc_equal` s)

let loc_union_comm s1 s2 =
  assert (loc_union s1 s2 `loc_equal` loc_union s2 s1)

let loc_union_assoc s1 s2 s3 =
  assert (loc_union s1 (loc_union s2 s3) `loc_equal` loc_union (loc_union s1 s2) s3)

let loc_union_loc_none_l s =
  assert (loc_union loc_none s `loc_equal` s)

let loc_union_loc_none_r s =
  assert (loc_union s loc_none `loc_equal` s)


let loc_buffer #t b =
    Loc
      (Ghost.hide (Set.singleton (B.frameOf b)))
      (Ghost.hide Set.empty)
      (fun _ -> Set.empty)
      (fun _ -> Set.singleton (B.as_addr b))
      (fun _ -> ())
      (Ghost.hide (GSet.singleton (ABuffer (B.frameOf b) (B.as_addr b) (B.abuffer_of_buffer b))))

let loc_addresses r n =
  let regions = (Ghost.hide (Set.singleton r)) in
  Loc
    regions
    (Ghost.hide Set.empty)
    (fun _ -> n)
    (fun _ -> Set.empty)
    (fun _ -> ())
    (Ghost.hide (abuffer_domain regions (fun _ -> n)))

let loc_regions r =
  let addrs (r' : HS.rid { Set.mem r' r } ) : GTot (Set.set nat) =
    Set.complement Set.empty
  in
  Loc
    (Ghost.hide r)
    (Ghost.hide r)
    addrs
    (fun _ -> Set.empty)
    (fun _ -> ())
    (Ghost.hide (abuffer_domain (Ghost.hide r) addrs))

let abuffer_includes (b0 b: abuffer) : GTot Type0 =
  b0.region == b.region /\ b0.addr = b.addr /\ b0.buffer `B.abuffer_includes` b.buffer

let loc_aux_includes_buffer
  (s: GSet.set abuffer)
  (b: abuffer)
: GTot Type0
  (decreases s)
= exists (b0 : abuffer) . b0 `GSet.mem` s /\ b0 `abuffer_includes` b

let loc_aux_includes
  (s1 s2: GSet.set abuffer)
: GTot Type0
  (decreases s2)
= forall (b2: abuffer) . GSet.mem b2 s2 ==> loc_aux_includes_buffer s1 b2

let loc_aux_includes_union_l
  (s1 s2 s: GSet.set abuffer)
: Lemma
  (requires (loc_aux_includes s1 s \/ loc_aux_includes s2 s))
  (ensures (loc_aux_includes (GSet.union s1 s2) s))
  (decreases s)
= ()

let loc_aux_includes_refl
  (s: GSet.set abuffer)
: Lemma
  (loc_aux_includes s s)
= Classical.forall_intro_3 (fun r a b -> B.abuffer_includes_refl #r #a b)

let loc_aux_includes_subset
  (s1 s2: GSet.set abuffer)
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
= Classical.forall_intro_3 (fun r a b -> B.abuffer_includes_refl #r #a b)

let loc_aux_includes_subset'
  (s1 s2: GSet.set abuffer)
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
  [SMTPatOr [
    [SMTPat (s1 `GSet.subset` s2)];
    [SMTPat (loc_aux_includes s2 s1)];
  ]]
= loc_aux_includes_subset s1 s2

let loc_aux_includes_union_l_r
  (s s': GSet.set abuffer)
: Lemma
  (loc_aux_includes (GSet.union s s') s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s s' s

let loc_aux_includes_union_l_l
  (s s': GSet.set abuffer)
: Lemma
  (loc_aux_includes (GSet.union s' s) s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s' s s

let loc_aux_includes_buffer_includes
  (s: GSet.set abuffer)
  (b1 b2: abuffer)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `abuffer_includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (B.abuffer_includes_trans #r #a b1 b2) b3))

let loc_aux_includes_loc_aux_includes_buffer
  (s1 s2: GSet.set abuffer)
  (b: abuffer)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
= Classical.forall_intro_3 (fun s b1 b2 -> Classical.move_requires (loc_aux_includes_buffer_includes s b1) b2)

let loc_aux_includes_trans
  (s1 s2 s3: GSet.set abuffer)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (B.abuffer_includes_trans #r #a b1 b2) b3))

let addrs_of_loc_weak_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc_weak (loc_union l1 l2) r) (Set.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc_union
  (l1 l2: loc)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (Set.equal (addrs_of_loc (loc_union l1 l2) r) (Set.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

let loc_includes s1 s2 =
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

let loc_includes_refl s =
  loc_aux_includes_refl (Ghost.reveal (Loc?.aux s))

let loc_includes_trans s1 s2 s3 =
  loc_aux_includes_trans (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s3))

let loc_includes_union_r s s1 s2 = ()

let loc_includes_union_l s1 s2 s =
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

let loc_includes_none s = ()

let loc_includes_buffer #t b1 b2 =
  B.includes_frameOf_as_addr b1 b2;
  begin
    B.abuffer_includes_intro b1 b2;
    // FIXME: WHY WHY WHY do I need this assert?
    assert (Ghost.reveal (Loc?.aux (loc_buffer b1)) `loc_aux_includes` Ghost.reveal (Loc?.aux (loc_buffer b2)))
  end

let loc_includes_gsub_buffer_r l #t b i len =
  loc_includes_trans l (loc_buffer b) (loc_buffer (B.gsub b i len))

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  B.gsub_gsub b i1 len1 (U32.sub i2 i1) len2

let loc_includes_addresses_buffer #t r s p = ()

let loc_includes_region_buffer #t s b = ()

let loc_includes_region_addresses s r a = ()


let loc_includes_region_region s1 s2 = ()

#set-options "--z3rlimit 16"

let loc_includes_region_union_l l s1 s2 = ()

#reset-options


(* Disjointness of two memory locations *)

let abuffer_disjoint (b1 b2: abuffer) : GTot Type0 =
  if b1.region = b2.region && b1.addr = b2.addr
  then B.abuffer_disjoint b1.buffer b2.buffer
  else True

let abuffer_disjoint_sym (b1 b2: abuffer) : Lemma
  (abuffer_disjoint b1 b2 <==> abuffer_disjoint b2 b1)
= Classical.forall_intro_2 (fun r a -> Classical.forall_intro_2 (fun b1 b2 -> B.abuffer_disjoint_sym #r #a b1 b2))

let loc_aux_disjoint
  (l1 l2: GSet.set abuffer)
: GTot Type0
= forall (b1 b2: abuffer) . (GSet.mem b1 l1 /\ GSet.mem b2 l2) ==> abuffer_disjoint b1 b2

let rec loc_aux_disjoint_union_l
  (ll1 lr1 l2: GSet.set abuffer)
: Lemma
  (ensures (loc_aux_disjoint (GSet.union ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
= ()

let loc_aux_disjoint_union_r
  (l1 ll2 lr2: GSet.set abuffer)
: Lemma
  (loc_aux_disjoint l1 (GSet.union ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let loc_aux_disjoint_sym
  (l1 l2: GSet.set abuffer)
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
= Classical.forall_intro_2 abuffer_disjoint_sym

let regions_of_loc_loc_union
  (s1 s2: loc)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (s1 s2: loc)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint_region_liveness_tags (l1 l2: loc) : GTot Type0 =
  Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty

let loc_disjoint_addrs (l1 l2: loc) : GTot Type0 =
  (forall (r: HS.rid) .
      Set.subset (Set.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) Set.empty /\
      Set.subset (Set.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) Set.empty
  )

let loc_disjoint_aux (l1 l2: loc) : GTot Type0 =
  loc_aux_disjoint (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2))

let loc_disjoint'
  (l1 l2: loc)
: GTot Type0
= loc_disjoint_region_liveness_tags l1 l2 /\
  loc_disjoint_addrs l1 l2 /\
  loc_disjoint_aux l1 l2

let loc_disjoint = loc_disjoint'

let loc_disjoint_sym l1 l2 =
  Classical.forall_intro_2 loc_aux_disjoint_sym

let loc_disjoint_none_r s = ()

let loc_disjoint_union_r s s1 s2 = ()

(*
let rec loc_aux_disjoint_buffer_includes
  (#r: HS.rid)
  (#a: nat)
  (l: loc_aux r a)
  (p1: B.abuffer r a)
  (p2: B.abuffer r a)
: Lemma
  (requires (loc_aux_disjoint_buffer l p1 /\ p1 `B.abuffer_includes` p2))
  (ensures (loc_aux_disjoint_buffer l p2))
  (decreases l)
= match l with
  | LocUnion ll lr ->
    loc_aux_disjoint_buffer_includes ll p1 p2;
    loc_aux_disjoint_buffer_includes lr p1 p2
  | LocBuffer b ->
    B.abuffer_includes_refl b;
    B.abuffer_disjoint_includes b p1 b p2

let rec loc_aux_disjoint_loc_aux_includes_buffer
  (#r: HS.rid)
  (#a: nat)
  (l1 l2: loc_aux r a)
  (b3: B.abuffer r a)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes_buffer l2 b3))
  (ensures (loc_aux_disjoint_buffer l1 b3))
  (decreases l2)
= match l2 with
  | LocUnion l2l l2r ->
    Classical.or_elim
      #(loc_aux_includes_buffer l2l b3)
      #(loc_aux_includes_buffer l2r b3)
      #(fun _ -> loc_aux_disjoint_buffer l1 b3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_buffer l1 l2l b3)
      (fun _ -> loc_aux_disjoint_loc_aux_includes_buffer l1 l2r b3)
  | LocBuffer b2 -> loc_aux_disjoint_buffer_includes l1 b2 b3
*)

let abuffer_disjoint_includes (b1 b2 b3 : abuffer) : Lemma
  (requires (abuffer_disjoint b1 b2 /\ abuffer_includes b2 b3))
  (ensures (abuffer_disjoint b1 b3))
= if b1.region = b2.region && b1.addr = b2.addr
  then begin
    B.abuffer_includes_refl b1.buffer;
    B.abuffer_disjoint_includes b1.buffer b2.buffer b1.buffer b3.buffer
  end
  else ()

let loc_aux_disjoint_loc_aux_includes
  (l1 l2 l3: GSet.set abuffer)
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= // FIXME: WHY WHY WHY do I need this assert?
  assert (forall (b1 b3: abuffer) . (GSet.mem b1 l1 /\ GSet.mem b3 l3) ==> (exists (b2: abuffer) . GSet.mem b2 l2 /\ abuffer_disjoint b1 b2 /\ abuffer_includes b2 b3));
  Classical.forall_intro_3 (fun b1 b2 b3 -> Classical.move_requires (abuffer_disjoint_includes b1 b2) b3)

let loc_disjoint_includes p1 p2 p1' p2' =
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

let loc_disjoint_buffer #t1 #t2 b1 b2 =
  if B.frameOf b1 = B.frameOf b2 && B.as_addr b1 = B.as_addr b2
  then
    B.abuffer_disjoint_intro b1 b2
  else ()

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 = ()

let loc_disjoint_addresses r1 r2 n1 n2 = ()

let loc_disjoint_buffer_addresses #t p r n = ()

let loc_disjoint_regions rs1 rs2 = ()


(** The modifies clause proper *)

let modifies_preserves_mreferences
  (s: loc)
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
  (s: loc)
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

let modifies_preserves_buffers
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (r: HS.rid) (a: nat) (b: B.abuffer r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ABuffer r a b))
    ==>
    B.abuffer_preserved b h1 h2
  )

let modifies_preserves_buffers_intro
  (s: loc)
  (h1 h2: HS.mem)
  (u: unit { modifies_preserves_mreferences s h1 h2 } )
  (f: (
    (r: HS.rid) ->
    (a: nat) ->
    (b: B.abuffer r a) ->
    Lemma
    (requires (
      Set.mem r (regions_of_loc s) /\ 
      (~ (Set.mem a (addrs_of_loc_weak s r))) /\
      (Set.mem a (addrs_of_loc_aux s r) ==> loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ABuffer r a b)))
    ))
    (ensures (B.abuffer_preserved b h1 h2))
  ))
: Lemma
  (modifies_preserves_buffers s h1 h2)
= let f'
    (r: HS.rid)
    (a: nat)
    (b: B.abuffer r a)
  : Lemma
    (requires (loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ABuffer r a b))))
    (ensures (B.abuffer_preserved b h1 h2))
  = if Set.mem r (regions_of_loc s) && (not (Set.mem a (addrs_of_loc_weak s r)))
    then
      Classical.move_requires (f r a) b
    else if Set.mem r (regions_of_loc s)
    then begin
      assert (Set.mem a (addrs_of_loc_weak s r));
      assert (GSet.mem (ABuffer r a b) (Ghost.reveal (Loc?.aux s)));
      assert (abuffer_disjoint (ABuffer r a b) (ABuffer r a b));
      B.abuffer_disjoint_self_preserved b h1 h2
    end
    else
      B.same_mreference_abuffer_preserved b h1 h2 (fun a' pre' r' -> ())
  in
  Classical.forall_intro_3 (fun r a b -> Classical.move_requires (f' r a) b)

let modifies_preserves_regions
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= forall (r: HS.rid) . (HS.live_region h1 r /\ ~ (Set.mem r (Ghost.reveal (Loc?.region_liveness_tags s)))) ==> HS.live_region h2 r

let modifies'
  (s: loc)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_regions s h1 h2 /\
  modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_buffers s h1 h2

let modifies = modifies'

let modifies_live_region s h1 h2 r = ()

let modifies_mreference_elim #t #pre b p h h' = ()

let modifies_buffer_elim #t1 b p h h' =
  if B.length b = 0
  then
    assert (B.as_seq h b `Seq.equal` B.as_seq h' b)
  else
    B.abuffer_preserved_elim b h h'

let modifies_refl s h =
  Classical.forall_intro_3 (fun r a b -> B.abuffer_preserved_refl #r #a b h)

let modifies_loc_includes s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro_2 loc_aux_disjoint_sym;
  Classical.forall_intro_3 (fun l1 l2 l3 -> Classical.move_requires (loc_aux_disjoint_loc_aux_includes l1 l2) l3);
  assert (modifies_preserves_buffers s1 h h')

let modifies_trans'
  (s: loc)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (B.abuffer_preserved_trans #r #a b h1 h2) h3)

let modifies_trans s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

let modifies_only_live_regions_weak
  (rs: Set.set HS.rid)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions rs) l) h h' /\
    loc_disjoint (loc_regions rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (B.addr_unused_in_abuffer_preserved #r #a b h) h')

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: GTot loc
= let (Loc regions region_liveness_tags addrs aux_addrs aux_addrs_disjoint aux) = l in
  Loc
    (Ghost.hide (Set.intersect (Ghost.reveal regions) rs))
    (Ghost.hide (Set.intersect (Ghost.reveal region_liveness_tags) rs))
    (fun r -> addrs r)
    (fun r -> aux_addrs r)
    (fun r -> aux_addrs_disjoint r)
    (Ghost.hide (GSet.intersect (Ghost.reveal aux) (abuffer_domain (Ghost.hide rs) (fun r -> Set.complement Set.empty))))

let regions_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else Set.empty))

let addrs_of_loc_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else Set.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (Set.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else Set.empty))

let loc_includes_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl)

let loc_includes_loc_union_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_equal (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= ()

let loc_includes_loc_regions_restrict_to_regions
  (l: loc)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions rs) (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl)

let modifies_only_live_regions rs l h h' =
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
  loc_disjoint_regions rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let modifies_fresh_frame_popped h0 h1 s h2 h3 =
  let f01 (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (B.abuffer_preserved b h0 h1)
  = B.same_mreference_abuffer_preserved #r #a b h0 h1 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 f01;
  modifies_loc_includes s h0 h1 loc_none;
  let s' = loc_union (loc_all_regions_from h1.HS.tip) s in
  let f23 (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (requires (r <> h2.HS.tip))
    (ensures (B.abuffer_preserved b h2 h3))
  = B.same_mreference_abuffer_preserved #r #a b h2 h3 (fun a' pre r' -> ())
  in
  let s23 = loc_region_only h2.HS.tip in
  assert (modifies_preserves_mreferences s23 h2 h3);
  modifies_preserves_buffers_intro s23 h2 h3 () (fun r a b ->
    f23 r a b
  );
  modifies_loc_includes s' h2 h3 s23;
  modifies_trans' s' h1 h2 h3;
  modifies_only_live_regions (HS.mod_set (Set.singleton h1.HS.tip)) s h0 h3

let modifies_loc_regions_intro rs h1 h2 =
  let f (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (requires (not (Set.mem r rs)))
    (ensures (B.abuffer_preserved b h1 h2))
  = B.same_mreference_abuffer_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  assert (modifies_preserves_mreferences (loc_regions rs) h1 h2);
  modifies_preserves_buffers_intro (loc_regions rs) h1 h2 () (fun r a b ->
    f r a b
  )

let modifies_loc_addresses_intro_weak
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc)
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
  let f (a: nat) (b: B.abuffer r a) : Lemma
    (requires (not (Set.mem a s)))
    (ensures (B.abuffer_preserved b h1 h2))
  = B.same_mreference_abuffer_preserved #r #a b h1 h2 (fun a' pre r_ -> ())
  in
  modifies_preserves_buffers_intro (loc_union (loc_addresses r s) l) h1 h2 () (fun r' a b -> if r = r' then f a b else ()
  )

let modifies_loc_addresses_intro r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  modifies_loc_addresses_intro_weak r s (restrict_to_regions l (Set.complement (Set.singleton r))) h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))

let modifies_ralloc_post #a #rel i init h x h' =
  let g (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (B.abuffer_preserved b h h')
  = B.same_mreference_abuffer_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_salloc_post #a #rel init h x h' =
  let g (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (B.abuffer_preserved b h h')
  = B.same_mreference_abuffer_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_free #a #rel r m =
  let g (r': HS.rid) (a: nat) (b: B.abuffer r' a) : Lemma
    (requires (r' <> HS.frameOf r \/ a <> HS.as_addr r))
    (ensures (B.abuffer_preserved b m (HS.free r m)))
  = B.same_mreference_abuffer_preserved #r' #a b m (HS.free r m) (fun a' pre r' -> ())
  in
  modifies_preserves_buffers_intro (loc_mreference r) m (HS.free r m) () (fun r a b -> g r a b)

let modifies_none_modifies h1 h2
= let g (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (B.abuffer_preserved b h1 h2)
  = B.same_mreference_abuffer_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_0_modifies h1 h2
= Classical.forall_intro (Classical.move_requires (B.modifies_0_live_region h1 h2));
  Classical.forall_intro_3 (fun a pre r ->
    Classical.move_requires (B.modifies_0_mreference #a #pre h1 h2) r
  );
  let g (r: HS.rid) (a: nat) (b: B.abuffer r a) : Lemma
    (B.abuffer_preserved b h1 h2)
  = B.modifies_0_abuffer b h1 h2
  in
  Classical.forall_intro_3 g

let modifies_1_modifies #t b h1 h2 =
  Classical.forall_intro (Classical.move_requires (B.modifies_1_live_region b h1 h2));
  let r = B.frameOf b in
  let a = B.as_addr b in
  let s = loc_buffer b in
  assert (regions_of_loc s == Set.singleton r);
  assert (addrs_of_loc s r `Set.equal` Set.singleton a);
  modifies_preserves_mreferences_intro s h1 h2 (fun t' pre p ->
    B.modifies_1_mreference #t b h1 h2 #t' #pre p
  );
  let g
    (r' : HS.rid)
    (a' : nat)
    (b': B.abuffer r' a')
  : Lemma
    (requires ((r == r' /\ a == a') ==> B.abuffer_disjoint #r #a (B.abuffer_of_buffer b) b'))
    (ensures (B.abuffer_preserved b' h1 h2))
  = if r = r' && a = a'
    then B.modifies_1_abuffer #t b h1 h2 b'
    else B.same_mreference_abuffer_preserved #r' #a' b' h1 h2 (fun a_ pre_ r_ -> ())
  in
  modifies_preserves_buffers_intro s h1 h2 () (fun r' a' b' -> 
    Classical.forall_intro_2 loc_aux_disjoint_sym;
    assert (abuffer_disjoint (ABuffer r' a' b') (ABuffer r a (B.abuffer_of_buffer b)));
    Classical.forall_intro_2 (B.abuffer_disjoint_sym #r #a);
    g r' a' b'
  )
 
let mreference_live_buffer_unused_in_disjoint #t1 #pre #t2 h b1 b2 =
  B.unused_in_equiv b2 h

let buffer_live_mreference_unused_in_disjoint #t1 #t2 #pre h b1 b2 =
    B.unused_in_equiv b1 h;
    Classical.move_requires (B.live_not_unused_in #t1 h) b1


let does_not_contain_addr' (h: HS.mem) (ra: HS.rid * nat) : GTot Type0 =
  forall (a: Type) (rel: Preorder.preorder a) (r: HS.mreference a rel) . {:pattern (h `HS.contains` r) } (HS.frameOf r == fst ra /\ HS.as_addr r == snd ra /\ h `HS.contains` r) ==> False

let does_not_contain_addr = does_not_contain_addr'

let not_live_region_does_not_contain_addr h ra = ()

let unused_in_does_not_contain_addr h #a #rel r = ()

let addr_unused_in_does_not_contain_addr h ra = ()

let free_does_not_contain_addr #a #rel r m x = ()

let does_not_contain_addr_elim #a #rel r m x = ()

let modifies_only_live_addresses_weak
  (r: HS.rid)
  (a: Set.set nat)
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_addresses r a) l) h h' /\
    loc_disjoint (loc_addresses r a) l /\
    (forall x . Set.mem x a ==> h `does_not_contain_addr` (r, x))
  ))
  (ensures (modifies l h h'))
= assert (modifies_preserves_mreferences l h h');
  modifies_preserves_buffers_intro l h h' () (fun r' a' b' ->
    if r = r' && Set.mem a' a
    then B.same_mreference_abuffer_preserved #r' #a' b' h h' (fun a_ pre_ r_ -> ())
    else ()
  )

(* Restrict a set of locations along a set of addresses in a given region *)

let restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Ghost loc
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
      (Ghost.hide (GSet.intersect (Ghost.reveal aux) (abuffer_domain (Ghost.hide regions') (aux_addrs')) `GSet.union` (abuffer_domain (Ghost.hide regions') addrs')))

let regions_of_loc_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (regions_of_loc (restrict_to_addresses l r include_liveness_tag as) == Set.intersect (regions_of_loc l) (Set.singleton r)))
  [SMTPat (regions_of_loc (restrict_to_addresses l r include_liveness_tag as))]
= assert (regions_of_loc (restrict_to_addresses l r include_liveness_tag as) `Set.equal` Set.intersect (regions_of_loc l) (Set.singleton r))

let addrs_of_loc_weak_restrict_to_addresses
  (l: loc)
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
  (l: loc)
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
  (l: loc)
  (r: HS.rid)
  (include_liveness_tag: bool)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes l (restrict_to_addresses l r include_liveness_tag as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset s1) s2)

let loc_includes_loc_union_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_equal (loc_union (restrict_to_addresses l r false as) (restrict_to_addresses l r true (Set.complement as))) l))
= ()

let loc_includes_loc_addresses_restrict_to_addresses
  (l: loc)
  (r: HS.rid)
  (as: Set.set nat)
: Lemma
  (requires (loc_region_only r `loc_includes` l))
  (ensures (loc_includes (loc_addresses r as) (restrict_to_addresses l r false as)))
= Classical.forall_intro_2 (fun s1 s2 -> Classical.move_requires (loc_aux_includes_subset s1) s2)

#set-options "--z3rlimit 64"

let modifies_only_live_addresses r a l h h' =
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
  assert (loc_disjoint (loc_addresses r a) l_r_not_a);
  assert (loc_disjoint (loc_addresses r a) l_not_r);
  modifies_only_live_addresses_weak r a l_not_a h h';
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_includes_restrict_to_addresses l_r r true (Set.complement a);
  modifies_loc_includes l h h' l_not_a

#reset-options
