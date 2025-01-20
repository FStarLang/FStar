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
module FStar.ModifiesGen

#set-options "--split_queries no --ext 'context_pruning='"
#set-options "--using_facts_from '*,-FStar.Tactics,-FStar.Reflection,-FStar.List'"

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

noeq
type aloc (#al: aloc_t) (c: cls al) = | ALoc:
  (region: HS.rid) ->
  (addr: nat) ->
  (loc: option (al region addr)) ->
  aloc c

let aloc_domain (#al: aloc_t) (c: cls al) (regions: Ghost.erased (Set.set HS.rid)) (addrs: ((r: HS.rid { Set.mem r (Ghost.reveal regions) } ) -> GTot (GSet.set nat))) : GTot (GSet.set (aloc c)) =
  GSet.comprehend (fun a -> Set.mem a.region (Ghost.reveal regions) && GSet.mem a.addr (addrs a.region))

module F = FStar.FunctionalExtensionality

[@@(unifier_hint_injective)]
let i_restricted_g_t = F.restricted_g_t

let addrs_dom regions =
    (r: HS.rid { Set.mem r (Ghost.reveal regions) } )

let non_live_addrs_codom
      (regions: Ghost.erased (Set.set HS.rid))
      (region_liveness_tags: Ghost.erased (Set.set HS.rid) { Ghost.reveal region_liveness_tags `Set.subset` Ghost.reveal regions } )
      (r:addrs_dom regions) =
      (y: GSet.set nat { r `Set.mem` (Ghost.reveal region_liveness_tags) ==> GSet.subset (GSet.complement GSet.empty) y })

let live_addrs_codom
      (regions: Ghost.erased (Set.set HS.rid))
      (region_liveness_tags: Ghost.erased (Set.set HS.rid) { Ghost.reveal region_liveness_tags `Set.subset` Ghost.reveal regions } )
      (non_live_addrs:
        i_restricted_g_t
          (addrs_dom regions)
          (non_live_addrs_codom regions region_liveness_tags))
      (r:addrs_dom regions) = (y: GSet.set nat { GSet.subset (non_live_addrs r) y } )

[@@erasable]
noeq
type loc' (#al: aloc_t u#x) (c: cls al) : Type u#x =
  | Loc:
      (regions: Ghost.erased (Set.set HS.rid)) ->
      (region_liveness_tags: Ghost.erased (Set.set HS.rid) { Ghost.reveal region_liveness_tags `Set.subset` Ghost.reveal regions } ) ->
      (non_live_addrs:
        i_restricted_g_t
          (addrs_dom regions)
          (non_live_addrs_codom regions region_liveness_tags)) ->
      (live_addrs:
        i_restricted_g_t
          (addrs_dom regions)
          (live_addrs_codom regions region_liveness_tags non_live_addrs)) ->
      (aux: Ghost.erased (GSet.set (aloc c)) {
        aloc_domain c regions live_addrs `GSet.subset` Ghost.reveal aux /\
        Ghost.reveal aux `GSet.subset` (aloc_domain c regions (fun _ -> GSet.complement GSet.empty))
      } ) ->
      loc' c

let loc = loc'

let mk_non_live_addrs (#regions:_) (#region_liveness_tags:_)
                      (f: (x:addrs_dom regions -> GTot (non_live_addrs_codom regions region_liveness_tags x)))
    : i_restricted_g_t
          (addrs_dom regions)
          (non_live_addrs_codom regions region_liveness_tags) =
    F.on_dom_g _ f

let mk_live_addrs (#regions:_) (#region_liveness_tags:_)
                  (#non_live_addrs_codom: _)
                  (f: (x:addrs_dom regions -> GTot (live_addrs_codom regions region_liveness_tags non_live_addrs_codom x)))
    : i_restricted_g_t
          (addrs_dom regions)
          (live_addrs_codom regions region_liveness_tags non_live_addrs_codom) =
    F.on_dom_g _ f

let loc_none #a #c =
  Loc
    (Ghost.hide (Set.empty))
    (Ghost.hide (Set.empty))
    (mk_non_live_addrs (fun _ -> GSet.empty))
    (mk_live_addrs (fun _ -> GSet.empty))
    (Ghost.hide GSet.empty)

let regions_of_loc
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
: GTot (Set.set HS.rid)
= Ghost.reveal (Loc?.regions s)

let addrs_of_loc_liveness_not_preserved
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (GSet.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.non_live_addrs l r
  else GSet.empty

let addrs_of_loc_weak
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (GSet.set nat)
= if Set.mem r (regions_of_loc l)
  then Loc?.live_addrs l r
  else GSet.empty

let addrs_of_loc_aux_pred
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
  (addr: nat)
: GTot bool
= StrongExcludedMiddle.strong_excluded_middle (exists a . GSet.mem a (Ghost.reveal (Loc?.aux l)) /\ a.region == r /\ a.addr == addr)

let addrs_of_loc_aux
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (y: GSet.set nat { GSet.subset (GSet.intersect y (addrs_of_loc_weak l r)) GSet.empty } )
= GSet.comprehend (addrs_of_loc_aux_pred l r)
    `GSet.intersect` (GSet.complement (addrs_of_loc_weak l r))

let addrs_of_loc
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: GTot (GSet.set nat)
= GSet.union
    (addrs_of_loc_weak l r)
    (addrs_of_loc_aux l r)

let addrs_of_loc_aux_prop
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (r: HS.rid)
: Lemma
  (GSet.subset (GSet.intersect (addrs_of_loc_aux l r) (addrs_of_loc_weak l r)) GSet.empty)
  [SMTPatOr [
    [SMTPat (addrs_of_loc_aux l r)];
    [SMTPat (addrs_of_loc_weak l r)];
    [SMTPat (addrs_of_loc l r)];
  ]]
= ()

let loc_union #al #c s1 s2 =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in
  let regions = Set.union regions1 regions2 in
  let region_liveness_tags : Ghost.erased (Set.set HS.rid) = (Ghost.hide (Set.union (Ghost.reveal (Loc?.region_liveness_tags s1)) (Ghost.reveal (Loc?.region_liveness_tags s2)))) in
  let gregions = Ghost.hide regions in
  let non_live_addrs =
    F.on_dom_g (addrs_dom gregions) #(non_live_addrs_codom gregions region_liveness_tags)
    (fun r ->
    GSet.union
      (if Set.mem r regions1 then Loc?.non_live_addrs s1 r else GSet.empty)
      (if Set.mem r regions2 then Loc?.non_live_addrs s2 r else GSet.empty))
  in
  let live_addrs =
    F.on_dom_g (addrs_dom gregions) #(live_addrs_codom gregions region_liveness_tags non_live_addrs)
      (fun r ->
        GSet.union
          (if Set.mem r regions1 then addrs_of_loc_weak s1 r else GSet.empty)
          (if Set.mem r regions2 then addrs_of_loc_weak s2 r else GSet.empty))
  in
  let aux = Ghost.hide
      (Ghost.reveal (Loc?.aux s1) `GSet.union` Ghost.reveal (Loc?.aux s2))
  in
  Loc
    (Ghost.hide regions)
    region_liveness_tags
    non_live_addrs
    live_addrs
    aux

let fun_set_equal (#t: Type) (#t': Type)
                  (#p:(t -> GSet.set t' -> Type))
                  (f1 f2: i_restricted_g_t t (fun x -> g:GSet.set t'{p x g})) :Tot Type0 =
  forall (x: t) . {:pattern (f1 x) \/ (f2 x) } f1 x `GSet.equal` f2 x

let fun_set_equal_elim (#t: Type) (#t': Type)
                       (#p:(t -> GSet.set t' -> Type))
                       (f1 f2: i_restricted_g_t t (fun x -> g:GSet.set t'{p x g})) : Lemma
  (requires (fun_set_equal f1 f2))
  (ensures (f1 == f2))
//  [SMTPat (fun_set_equal f1 f2)]
= assert (f1 `FunctionalExtensionality.feq_g` f2)

let loc_equal (#al: aloc_t) (#c: cls al) (s1 s2: loc c) : GTot Type0 =
  let Loc regions1 region_liveness_tags1 _ _ aux1 = s1 in
  let Loc regions2 region_liveness_tags2 _ _ aux2 = s2 in
  Ghost.reveal regions1 `Set.equal` Ghost.reveal regions2 /\
  Ghost.reveal region_liveness_tags1 `Set.equal` Ghost.reveal region_liveness_tags2 /\
  fun_set_equal (Loc?.non_live_addrs s1) (Loc?.non_live_addrs s2) /\
  fun_set_equal (Loc?.live_addrs s1) (Loc?.live_addrs s2) /\
  Ghost.reveal (Loc?.aux s1) `GSet.equal` Ghost.reveal (Loc?.aux s2)

let loc_equal_elim (#al: aloc_t) (#c: cls al) (s1 s2: loc c) : Lemma
  (requires (loc_equal s1 s2))
  (ensures (s1 == s2))
  [SMTPat (s1 `loc_equal` s2)]
= fun_set_equal_elim (Loc?.non_live_addrs s1) (Loc?.non_live_addrs s2);
  fun_set_equal_elim (Loc?.live_addrs s1) (Loc?.live_addrs s2)


let loc_union_idem #al #c s =
  assert (loc_union s s `loc_equal` s)

let loc_union_comm #al #c s1 s2 =
  assert (loc_union s1 s2 `loc_equal` loc_union s2 s1)

let loc_union_assoc #al #c s1 s2 s3 =
  assert (loc_union s1 (loc_union s2 s3) `loc_equal` loc_union (loc_union s1 s2) s3)

let loc_union_loc_none_l #al #c s =
  assert (loc_union loc_none s `loc_equal` s)

let loc_union_loc_none_r #al #c s =
  assert (loc_union s loc_none `loc_equal` s)

let loc_of_aloc #al #c #r #n b =
  let regions =        (Ghost.hide (Set.singleton r)) in
  let region_liveness_tags = (Ghost.hide (Set.empty)) in
  Loc
    regions
    region_liveness_tags
    (mk_non_live_addrs (fun _ -> GSet.empty))
    (mk_live_addrs (fun _ -> GSet.empty))
    (Ghost.hide (GSet.singleton (ALoc r n (Some b))))

let loc_of_aloc_not_none #al #c #r #n b = ()

let loc_addresses #al #c preserve_liveness r n =
  let regions = (Ghost.hide (Set.singleton r)) in
  Loc
    regions
    (Ghost.hide Set.empty)
    (mk_non_live_addrs (fun _ -> if preserve_liveness then GSet.empty else GSet.of_set n))
    (mk_live_addrs (fun _ -> GSet.of_set n))
    (Ghost.hide (aloc_domain c regions (fun _ -> GSet.of_set n)))

let loc_regions_region_liveness_tags (preserve_liveness: bool) (r: Set.set HS.rid) : Tot (Ghost.erased (Set.set HS.rid)) =
  if preserve_liveness then Ghost.hide Set.empty else Ghost.hide r

let loc_regions #al #c preserve_liveness r =
  let region_liveness_tags = loc_regions_region_liveness_tags preserve_liveness r in
  let addrs (r' : HS.rid { Set.mem r' r } ) : GTot (y: GSet.set nat { r' `Set.mem` (Ghost.reveal region_liveness_tags) ==> GSet.subset (GSet.complement GSet.empty) y } ) =
    GSet.complement GSet.empty
  in
  let live_addrs (r' : HS.rid { Set.mem r' r } ) : GTot (y: GSet.set nat { addrs r' `GSet.subset` y } ) =
    addrs r'
  in
  Loc
    (Ghost.hide r)
    region_liveness_tags
    (mk_non_live_addrs addrs)
    (mk_live_addrs live_addrs)
    (Ghost.hide (aloc_domain c (Ghost.hide r) addrs))

let aloc_includes (#al: aloc_t) (#c: cls al) (b0 b: aloc c) : GTot Type0 =
  b0.region == b.region /\ b0.addr == b.addr /\ Some? b0.loc == Some? b.loc /\ (if Some? b0.loc && Some? b.loc then c.aloc_includes (Some?.v b0.loc) (Some?.v b.loc) else True)

let loc_aux_includes_buffer
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
  (b: aloc c)
: GTot Type0
  (decreases s)
= exists (b0 : aloc c) . b0 `GSet.mem` s /\ b0 `aloc_includes` b

let loc_aux_includes
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
: GTot Type0
  (decreases s2)
= forall (b2: aloc c) . GSet.mem b2 s2 ==> loc_aux_includes_buffer s1 b2

let loc_aux_includes_union_l
  (#al: aloc_t) (#c: cls al)
  (s1 s2 s: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s \/ loc_aux_includes s2 s))
  (ensures (loc_aux_includes (GSet.union s1 s2) s))
  (decreases s)
= ()

let loc_aux_includes_refl
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
: Lemma
  (loc_aux_includes s s)
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
: Lemma
  (requires (s1 `GSet.subset` s2))
  (ensures (loc_aux_includes s2 s1))
= Classical.forall_intro_3 (fun r a b -> c.aloc_includes_refl #r #a b)

let loc_aux_includes_subset'
  (#al: aloc_t) (#c: cls al)
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
  (#al: aloc_t) (#c: cls al)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s s') s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s s' s

let loc_aux_includes_union_l_l
  (#al: aloc_t) (#c: cls al)
  (s s': GSet.set (aloc c))
: Lemma
  (loc_aux_includes (GSet.union s' s) s)
= loc_aux_includes_refl s;
  loc_aux_includes_union_l s' s s

let loc_aux_includes_buffer_includes
  (#al: aloc_t) (#c: cls al)
  (s: GSet.set (aloc c))
  (b1 b2: aloc c)
: Lemma
  (requires (loc_aux_includes_buffer s b1 /\ b1 `aloc_includes` b2))
  (ensures (loc_aux_includes_buffer s b2))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let loc_aux_includes_loc_aux_includes_buffer
  (#al: aloc_t) (#c: cls al)
  (s1 s2: GSet.set (aloc c))
  (b: aloc c)
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes_buffer s2 b))
  (ensures (loc_aux_includes_buffer s1 b))
= Classical.forall_intro_3 (fun s b1 b2 -> Classical.move_requires (loc_aux_includes_buffer_includes #al #c s b1) b2)

let loc_aux_includes_trans
  (#al: aloc_t) (#c: cls al)
  (s1 s2 s3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_includes s1 s2 /\ loc_aux_includes s2 s3))
  (ensures (loc_aux_includes s1 s3))
= Classical.forall_intro_3 (fun r a b1 -> Classical.forall_intro_2 (fun b2 b3 -> Classical.move_requires (c.aloc_includes_trans #r #a b1 b2) b3))

let addrs_of_loc_weak_loc_union
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (loc_union l1 l2) r == GSet.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r))
  [SMTPat (addrs_of_loc_weak (loc_union l1 l2) r)]
= assert (GSet.equal (addrs_of_loc_weak (loc_union l1 l2) r) (GSet.union (addrs_of_loc_weak l1 r) (addrs_of_loc_weak l2 r)))

let addrs_of_loc_union
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l1 l2) r == GSet.union (addrs_of_loc l1 r) (addrs_of_loc l2 r))
  [SMTPat (addrs_of_loc (loc_union l1 l2) r)]
= assert (GSet.equal (addrs_of_loc (loc_union l1 l2) r) (GSet.union (addrs_of_loc l1 r) (addrs_of_loc l2 r)))

unfold
let loc_includes' #al (#c: cls al) (s1 s2: loc c) =
  let regions1 = Ghost.reveal (Loc?.regions s1) in
  let regions2 = Ghost.reveal (Loc?.regions s2) in (
    Set.subset regions2 regions1 /\
    Set.subset (Ghost.reveal (Loc?.region_liveness_tags s2)) (Ghost.reveal (Loc?.region_liveness_tags s1)) /\
    (
      forall (r: HS.rid { Set.mem r regions2 } ) .
      GSet.subset (Loc?.non_live_addrs s2 r) (Loc?.non_live_addrs s1 r)
    ) /\
    (
      forall (r: HS.rid) .
      GSet.subset (addrs_of_loc_weak s2 r) (addrs_of_loc_weak s1 r)
    ) /\ (
      forall (r: HS.rid) .
      GSet.subset (addrs_of_loc s2 r) (addrs_of_loc s1 r)
    ) /\ (
      (Ghost.reveal (Loc?.aux s1)) `loc_aux_includes` (Ghost.reveal (Loc?.aux s2))
    )
  )

let loc_includes #al #c s1 s2 =
  loc_includes' s1 s2

let loc_includes_refl #al #c s =
  loc_aux_includes_refl (Ghost.reveal (Loc?.aux s))

let loc_includes_refl'
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]
= loc_includes_refl s

let loc_includes_trans #al #c s1 s2 s3 =
  loc_aux_includes_trans (Ghost.reveal (Loc?.aux s1)) (Ghost.reveal (Loc?.aux s2)) (Ghost.reveal (Loc?.aux s3))

let loc_includes_union_r #al #c s s1 s2 = ()

let loc_includes_union_l #al #c s1 s2 s =
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

let loc_includes_none #al #c s = ()

let loc_includes_none_elim #al #c s =
  assert (s `loc_equal` loc_none)

let loc_includes_aloc #al #c #r #n b1 b2 = ()

let loc_includes_aloc_elim #aloc #c #r1 #r2 #n1 #n2 b1 b2 = ()

let addrs_of_loc_loc_of_aloc
  (#al: aloc_t)
  (#c: cls al)
  (#r: HS.rid)
  (#a: nat)
  (p: al r a)
  (r': HS.rid)
: Lemma
  (addrs_of_loc (loc_of_aloc #_ #c p) r' `GSet.equal` (if r = r' then GSet.singleton a else GSet.empty))
  [SMTPat (addrs_of_loc (loc_of_aloc #_ #c p) r')]
= ()

let loc_includes_addresses_aloc #al #c preserve_liveness r s #a p = ()

let loc_includes_region_aloc #al #c preserve_liveness s #r #a b = ()

let loc_includes_region_addresses #al #c s preserve_liveness1 preserve_liveness2 r a = ()

let loc_includes_region_region #al #c preserve_liveness1 preserve_liveness2 s1 s2 = ()

let loc_includes_region_union_l #al #c preserve_liveness l s1 s2 =
  assert ((loc_regions #_ #c preserve_liveness (Set.intersect s2 (Set.complement s1)) `loc_union` loc_regions #_ #c preserve_liveness (Set.intersect s2 s1)) `loc_equal` loc_regions preserve_liveness s2);
  loc_includes_region_region #_ #c preserve_liveness preserve_liveness s1 (Set.intersect s2 s1);
  loc_includes_union_l (loc_regions preserve_liveness s1) l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)));
  loc_includes_union_l (loc_regions preserve_liveness s1) l (loc_regions preserve_liveness (Set.intersect s2 s1));
  loc_includes_union_r (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1))) (loc_regions preserve_liveness (Set.intersect s2 s1))

let loc_includes_addresses_addresses #al c preserve_liveness1 preserve_liveness2 r s1 s2 = ()

(* Disjointness of two memory locations *)

let aloc_disjoint (#al: aloc_t) (#c: cls al) (b1 b2: aloc c) : GTot Type0 =
  if b1.region = b2.region && b1.addr = b2.addr
  then Some? b1.loc /\ Some? b2.loc /\ c.aloc_disjoint (Some?.v b1.loc) (Some?.v b2.loc)
  else True

let aloc_disjoint_sym (#al: aloc_t) (#c: cls al) (b1 b2: aloc c) : Lemma
  (aloc_disjoint b1 b2 <==> aloc_disjoint b2 b1)
= Classical.forall_intro_2 (fun r a -> Classical.forall_intro_2 (fun b1 b2 -> c.aloc_disjoint_sym #r #a b1 b2))

let loc_aux_disjoint
  (#al: aloc_t) (#c: cls al)
  (l1 l2: GSet.set (aloc c))
: GTot Type0
= forall (b1 b2: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b2 l2) ==> aloc_disjoint b1 b2

let loc_aux_disjoint_union_l
  (#al: aloc_t) (#c: cls al)
  (ll1 lr1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint (GSet.union ll1 lr1) l2 <==> (loc_aux_disjoint ll1 l2 /\ loc_aux_disjoint lr1 l2)))
= ()

let loc_aux_disjoint_union_r
  (#al: aloc_t) (#c: cls al)
  (l1 ll2 lr2: GSet.set (aloc c))
: Lemma
  (loc_aux_disjoint l1 (GSet.union ll2 lr2) <==> (loc_aux_disjoint l1 ll2 /\ loc_aux_disjoint l1 lr2))
= ()

let loc_aux_disjoint_sym
  (#al: aloc_t) (#c: cls al)
  (l1 l2: GSet.set (aloc c))
: Lemma
  (ensures (loc_aux_disjoint l1 l2 <==> loc_aux_disjoint l2 l1))
= Classical.forall_intro_2 (aloc_disjoint_sym #al #c)

let regions_of_loc_loc_union
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (regions_of_loc (loc_union s1 s2) == regions_of_loc s1 `Set.union` regions_of_loc s2)
  [SMTPat (regions_of_loc (loc_union s1 s2))]
= assert (regions_of_loc (loc_union s1 s2) `Set.equal` (regions_of_loc s1 `Set.union` regions_of_loc s2))

let regions_of_loc_monotonic
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (requires (loc_includes s1 s2))
  (ensures (Set.subset (regions_of_loc s2) (regions_of_loc s1)))
= ()

let loc_disjoint_region_liveness_tags (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty

let loc_disjoint_addrs (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  (forall (r: HS.rid) .
      GSet.subset (GSet.intersect (addrs_of_loc_weak l1 r) (addrs_of_loc l2 r)) GSet.empty /\
      GSet.subset (GSet.intersect (addrs_of_loc l1 r) (addrs_of_loc_weak l2 r)) GSet.empty
  )

let loc_disjoint_aux (#al: aloc_t) (#c: cls al) (l1 l2: loc c) : GTot Type0 =
  loc_aux_disjoint (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2))

let loc_disjoint
  (#al: aloc_t) (#c: cls al)
  (l1 l2: loc c)
: GTot Type0
= loc_disjoint_region_liveness_tags l1 l2 /\
  loc_disjoint_addrs l1 l2 /\
  loc_disjoint_aux l1 l2

let loc_disjoint_sym #al #c l1 l2 =
  Classical.forall_intro_2 (loc_aux_disjoint_sym #al #c)

let loc_disjoint_sym'
  (#al: aloc_t) (#c: cls al)
  (s1 s2: loc c)
: Lemma
  (requires (loc_disjoint s1 s2))
  (ensures (loc_disjoint s2 s1))
  [SMTPat (loc_disjoint s1 s2)]
= loc_disjoint_sym s1 s2

let loc_disjoint_none_r #al #c s = ()

let loc_disjoint_union_r #al #c s s1 s2 = ()

let aloc_disjoint_includes (#al: aloc_t) (#c: cls al) (b1 b2 b3 : aloc c) : Lemma
  (requires (aloc_disjoint b1 b2 /\ aloc_includes b2 b3))
  (ensures (aloc_disjoint b1 b3))
= if b1.region = b2.region && b1.addr = b2.addr
  then begin
    c.aloc_includes_refl (Some?.v b1.loc);
    c.aloc_disjoint_includes (Some?.v b1.loc) (Some?.v b2.loc) (Some?.v b1.loc) (Some?.v b3.loc)
  end
  else ()

let loc_aux_disjoint_loc_aux_includes
  (#al: aloc_t) (#c: cls al)
  (l1 l2 l3: GSet.set (aloc c))
: Lemma
  (requires (loc_aux_disjoint l1 l2 /\ loc_aux_includes l2 l3))
  (ensures (loc_aux_disjoint l1 l3))
= // FIXME: WHY WHY WHY do I need this assert?
  assert (forall (b1 b3: aloc c) . (GSet.mem b1 l1 /\ GSet.mem b3 l3) ==> (exists (b2: aloc c) . GSet.mem b2 l2 /\ aloc_disjoint b1 b2 /\ aloc_includes b2 b3));
  Classical.forall_intro_3 (fun b1 b2 b3 -> Classical.move_requires (aloc_disjoint_includes #al #c b1 b2) b3)

let loc_disjoint_includes #al #c p1 p2 p1' p2' =
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

let loc_disjoint_aloc_intro #al #c #r1 #a1 #r2 #a2 b1 b2 = ()

let loc_disjoint_aloc_elim #al #c #r1 #a1 #r2 #a2 b1 b2 =
  // FIXME: WHY WHY WHY this assert?
  assert (aloc_disjoint (ALoc #_ #c r1 a1 (Some b1)) (ALoc #_ #c r2 a2 (Some b2)))

#push-options "--z3rlimit 15"
let loc_disjoint_addresses_intro #al #c preserve_liveness1 preserve_liveness2 r1 r2 n1 n2 =
  // FIXME: WHY WHY WHY this assert?
  assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_addresses #_ #c preserve_liveness1 r1 n1))) (Ghost.reveal (Loc?.aux (loc_addresses #_ #c preserve_liveness2 r2 n2))))
#pop-options

let loc_disjoint_addresses_elim #al #c preserve_liveness1 preserve_liveness2 r1 r2 n1 n2 = ()

let loc_disjoint_aloc_addresses_intro #al #c #r' #a' p preserve_liveness r n = ()

let loc_disjoint_aloc_addresses_elim #al #c #r' #a' p preserve_liveness r n = ()

#push-options "--z3rlimit 15"
let loc_disjoint_regions #al #c preserve_liveness1 preserve_liveness2 rs1 rs2 =
  // FIXME: WHY WHY WHY this assert?
  assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_regions #_ #c preserve_liveness1 rs1))) (Ghost.reveal (Loc?.aux (loc_regions #_ #c preserve_liveness2 rs2))))
#pop-options

let loc_none_in_some_region #a (c: cls a) (r: HS.rid) : GTot (loc c) =
  Loc
    (Ghost.hide (Set.singleton r))
    (Ghost.hide (Set.empty))
    (mk_non_live_addrs (fun _ -> GSet.empty))
    (mk_live_addrs (fun _ -> GSet.empty))
    (Ghost.hide GSet.empty)

(** Liveness-insensitive memory locations *)

let address_liveness_insensitive_locs #al c =
  Loc
    (Ghost.hide (Set.complement Set.empty))
    (Ghost.hide Set.empty)
    (mk_non_live_addrs (fun _ -> GSet.empty))
    (mk_live_addrs (fun _ -> GSet.complement GSet.empty))
    (Ghost.hide (aloc_domain c (Ghost.hide (Set.complement Set.empty)) (fun _ -> GSet.complement GSet.empty)))

let loc_includes_address_liveness_insensitive_locs_aloc #al #c #r #n a = ()

let loc_includes_address_liveness_insensitive_locs_addresses #al c r a = ()

let region_liveness_insensitive_locs #al c =
  Loc
    (Ghost.hide (Set.complement Set.empty))
    (Ghost.hide Set.empty)
    (mk_non_live_addrs (fun _ -> GSet.complement GSet.empty))
    (mk_live_addrs (fun _ -> GSet.complement GSet.empty))
    (Ghost.hide (aloc_domain c (Ghost.hide (Set.complement Set.empty)) (fun _ -> GSet.complement GSet.empty)))

let loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs #al c = ()

let loc_includes_region_liveness_insensitive_locs_loc_regions #al c r = ()

let loc_includes_region_liveness_insensitive_locs_loc_addresses #al c preserve_liveness r a = ()

let loc_includes_region_liveness_insensitive_locs_loc_of_aloc #al c #r #a x = ()

(** The modifies clause proper *)

let modifies_preserves_livenesses
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (Loc?.non_live_addrs s r)))
    ) ==> (
      HS.contains h2 p
  ))

let modifies_preserves_livenesses_elim
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (p: HS.mreference t pre)
: Lemma
  (requires (modifies_preserves_livenesses s h1 h2 /\ HS.contains h1 p /\ (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (Loc?.non_live_addrs s (HS.frameOf p))))))
  (ensures (HS.contains h2 p))
= ()

let modifies_preserves_livenesses_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (f: (
    (t: Type) ->
    (pre: Preorder.preorder t) ->
    (p: HS.mreference t pre) ->
    Lemma
    (requires (
      HS.contains h1 p /\
      (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (Loc?.non_live_addrs s (HS.frameOf p))))
    ))
    (ensures (HS.contains h2 p))
  ))
: Lemma
  (modifies_preserves_livenesses s h1 h2)
= let f'
    (t : Type)
    (pre: Preorder.preorder t)
    (p : HS.mreference t pre)
  : Lemma
    (
  (HS.contains h1 p /\ (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (Loc?.non_live_addrs s (HS.frameOf p))))) ==>
    (h2 `HS.contains` p))
  = Classical.move_requires (f t pre) p
  in
  Classical.forall_intro_3 f'

let modifies_preserves_mreferences
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (t: Type) (pre: Preorder.preorder t) (p: HS.mreference t pre) .
    let r = HS.frameOf p in (
      HS.contains h1 p /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s r)))
    ) ==> (
      HS.contains h2 p /\
      HS.sel h2 p == HS.sel h1 p
  ))

let modifies_preserves_mreferences_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (f: (
    (t: Type) ->
    (pre: Preorder.preorder t) ->
    (p: HS.mreference t pre) ->
    Lemma
    (requires (
      HS.contains h1 p /\
      (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))
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
  (HS.contains h1 p /\ (Set.mem (HS.frameOf p) (regions_of_loc s) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc s (HS.frameOf p))))) ==>
    (h2 `HS.contains` p /\ h2 `HS.sel` p == h1 `HS.sel` p))
  = Classical.move_requires (f t pre) p
  in
  Classical.forall_intro_3 f'

let modifies_preserves_alocs
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (r: HS.rid) (a: nat) (b: al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b)))
    ==>
    c.aloc_preserved b h1 h2
  )

let modifies_preserves_alocs_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (u: unit { modifies_preserves_mreferences s h1 h2 } )
  (f: (
    (r: HS.rid) ->
    (a: nat) ->
    (b: al r a) ->
    Lemma
    (requires (
      Set.mem r (regions_of_loc s) /\
      (~ (GSet.mem a (addrs_of_loc_weak s r))) /\
      (GSet.mem a (addrs_of_loc_aux s r) /\ loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b))))
    ))
    (ensures (c.aloc_preserved b h1 h2))
  ))
: Lemma
  (modifies_preserves_alocs s h1 h2)
= let f'
    (r: HS.rid)
    (a: nat)
    (b: al r a)
  : Lemma
    (requires (loc_aux_disjoint (Ghost.reveal (Loc?.aux s)) (GSet.singleton (ALoc r a (Some b)))))
    (ensures (c.aloc_preserved b h1 h2))
  = if Set.mem r (regions_of_loc s) && (not (GSet.mem a (addrs_of_loc_weak s r)))
    then begin
      if GSet.mem a (addrs_of_loc_aux s r)
      then
        Classical.move_requires (f r a) b
      else
        c.same_mreference_aloc_preserved b h1 h2 (fun a' pre' r' -> ())
    end else if Set.mem r (regions_of_loc s)
    then begin
      assert (GSet.mem a (addrs_of_loc_weak s r));
      assert (GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux s)));
      assert (aloc_disjoint #_ #c (ALoc r a None) (ALoc r a (Some b)));
      assert False
    end
    else
      c.same_mreference_aloc_preserved b h1 h2 (fun a' pre' r' -> ())
  in
  Classical.forall_intro_3 (fun r a b -> Classical.move_requires (f' r a) b)

let modifies_preserves_regions
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= forall (r: HS.rid) . (HS.live_region h1 r /\ ~ (Set.mem r (Ghost.reveal (Loc?.region_liveness_tags s)))) ==> HS.live_region h2 r


let modifies_preserves_not_unused_in
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= (forall (r: HS.rid) (n: nat) . (
      HS.live_region h1 r /\ HS.live_region h2 r /\
      n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r) /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem n (Loc?.non_live_addrs s r)))
    ) ==> (
      n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
  ))

let modifies_preserves_not_unused_in_intro
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (f: (
    (r: HS.rid) ->
    (n: nat) ->
    Lemma
    (requires (
      HS.live_region h1 r /\ HS.live_region h2 r /\
      n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r) /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem n (Loc?.non_live_addrs s r)))
    ))
    (ensures (
      n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
    ))
  ))
: Lemma
  (modifies_preserves_not_unused_in s h1 h2)
= let f'
    (r: HS.rid)
    (n: nat)
  : Lemma
    ((
      HS.live_region h1 r /\ HS.live_region h2 r /\
      n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r) /\
      (Set.mem r (regions_of_loc s) ==> ~ (GSet.mem n (Loc?.non_live_addrs s r)))
    ) ==> (
      n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)
    ))
  = Classical.move_requires (f r) n
  in
  Classical.forall_intro_2 f'

let modifies
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
: GTot Type0
= modifies_preserves_regions s h1 h2 /\
  modifies_preserves_not_unused_in s h1 h2 /\
  modifies_preserves_mreferences s h1 h2 /\
  modifies_preserves_livenesses s h1 h2 /\
  modifies_preserves_alocs s h1 h2

val modifies_intro_strong
  (#al: aloc_t) (#c: cls al) (l: loc c) (h h' : HS.mem)
  (regions: (
    (r: HS.rid) ->
    Lemma
    (requires (HS.live_region h r))
    (ensures (HS.live_region h' r))
  ))
  (mrefs: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires ((loc_disjoint (loc_mreference b) l) /\ HS.contains h b))
    (ensures (HS.contains h' b /\ HS.sel h' b == HS.sel h b))
  ))
  (livenesses: (
    (t: Type0) ->
    (pre: Preorder.preorder t) ->
    (b: HS.mreference t pre) ->
    Lemma
    (requires (HS.contains h b))
    (ensures (HS.contains h' b))
  ))
  (addr_unused_in: (
    (r: HS.rid) ->
    (n: nat) ->
    Lemma
    (requires (
      (Set.mem r (regions_of_loc l) ==> ~ (GSet.mem n (Loc?.non_live_addrs l r))) /\
      HS.live_region h r /\
      HS.live_region h' r /\ n `Heap.addr_unused_in` (HS.get_hmap h' `Map.sel` r)
    ))
    (ensures (n `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` r)))
  ))
  (alocs: (
    (r: HS.rid) ->
    (a: nat) ->
    (x: al r a) ->
    Lemma
    (requires (loc_disjoint (loc_of_aloc x) l))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (modifies l h h')

#push-options "--z3rlimit 20"
let modifies_intro_strong #al #c l h h' regions mrefs lives unused_ins alocs =
  Classical.forall_intro (Classical.move_requires regions);
  assert (modifies_preserves_regions l h h');

  let aux (t:Type) (pre:Preorder.preorder t) (p:HS.mreference t pre)
    :Lemma (requires (HS.contains h p /\
                      (Set.mem (HS.frameOf p) (regions_of_loc l) ==> ~ (GSet.mem (HS.as_addr p) (addrs_of_loc l (HS.frameOf p))))))
           (ensures  (HS.contains h' p /\ HS.sel h' p == HS.sel h p))
    =
    assert_norm (Loc?.region_liveness_tags (loc_mreference #_ #c p) == Ghost.hide Set.empty);
    assert (loc_disjoint_region_liveness_tags (loc_mreference p) l);
    // FIXME: WHY WHY WHY is this assert necessary?
    assert_spinoff (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_mreference p))) (Ghost.reveal (Loc?.aux l)));
    // FIXME: Now this one is too :)
    assert (loc_disjoint_addrs (loc_mreference p) l);
    assert ((loc_disjoint (loc_mreference p) l));
    mrefs t pre p
  in

  modifies_preserves_mreferences_intro l h h' aux;
  Classical.forall_intro_3 (fun t pre p -> Classical.move_requires (lives t pre) p);
  modifies_preserves_not_unused_in_intro l h h' (fun r n ->
    unused_ins r n
  );
  modifies_preserves_alocs_intro l h h' () (fun r a b ->
    loc_aux_disjoint_sym (Ghost.reveal (Loc?.aux l)) (Ghost.reveal (Loc?.aux (loc_of_aloc b)));
    alocs r a b
  )
#pop-options

let modifies_intro #al #c l h h'  regions mrefs lives unused_ins alocs =
  modifies_intro_strong l h h'
    regions
    mrefs
    lives
    (fun r n -> unused_ins r n)
    alocs

let modifies_none_intro #al #c h h' regions mrefs unused_ins =
  modifies_intro_strong #_ #c loc_none h h'
    (fun r -> regions r)
    (fun t pre b -> mrefs t pre b)
    (fun t pre b -> mrefs t pre b)
    (fun r n -> unused_ins r n)
    (fun r a x ->
      c.same_mreference_aloc_preserved x h h' (fun t pre b -> mrefs t pre b)
    )

let modifies_address_intro #al #c r n h h' regions mrefs unused_ins =
  Classical.forall_intro (Classical.move_requires regions);
  let l : loc c = loc_addresses #_ #c false r (Set.singleton n) in
  modifies_preserves_mreferences_intro l h h'
    (fun t pre p -> mrefs t pre p)
  ;
  modifies_preserves_livenesses_intro l h h'
    (fun t pre p -> mrefs t pre p)
  ;
  modifies_preserves_not_unused_in_intro l h h'
    (fun r n -> unused_ins r n)
  ;
  modifies_preserves_alocs_intro l h h' ()
    (fun r a b ->
      c.same_mreference_aloc_preserved b h h' (fun t pre p -> mrefs t pre p)
    )

let modifies_aloc_intro #al #c #r #n x h h' regions mrefs livenesses unused_ins alocs =
  modifies_intro_strong #_ #c (loc_of_aloc x) h h'
    (fun r -> regions r)
    (fun t pre b -> mrefs t pre b)
    (fun t pre b -> livenesses t pre b)
    (fun r n -> unused_ins r n)
    (fun r' n' z ->
      if r' = r && n' = n
      then begin
        loc_disjoint_aloc_elim #_ #c z x;
        alocs z
      end else
        c.same_mreference_aloc_preserved z h h' (fun t pre p ->
          mrefs t pre p
        )
    )

let modifies_live_region #al #c s h1 h2 r = ()

let modifies_mreference_elim #al #c #t #pre b p h h' = ()

let modifies_aloc_elim #al #c #r #a b p h h' = ()

let modifies_refl #al #c s h =
  Classical.forall_intro_3 (fun r a b -> c.aloc_preserved_refl #r #a b h)

let modifies_loc_includes #al #c s1 h h' s2 =
  assert (modifies_preserves_mreferences s1 h h');
  Classical.forall_intro_2 (loc_aux_disjoint_sym #al #c);
  Classical.forall_intro_3 (fun l1 l2 l3 -> Classical.move_requires (loc_aux_disjoint_loc_aux_includes #al #c l1 l2) l3);
  assert (modifies_preserves_alocs s1 h h')

let modifies_preserves_liveness #al #c s1 s2 h h' #t #pre r = ()

#push-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"
let modifies_preserves_liveness_strong #al #c s1 s2 h h' #t #pre r x =
  let rg = HS.frameOf r in
  let ad = HS.as_addr r in
  let la = loc_of_aloc #_ #c #rg #ad x in
  if Set.mem rg (regions_of_loc s2)
  then begin
    assert (Loc?.non_live_addrs s2 rg `GSet.subset` Loc?.non_live_addrs (address_liveness_insensitive_locs c) rg);
    assert (Loc?.non_live_addrs s2 rg `GSet.subset` GSet.empty);
    assert (~ (GSet.mem ad (Loc?.non_live_addrs s2 rg)));
    if Set.mem rg (regions_of_loc s1)
    then begin
      if GSet.mem ad (Loc?.non_live_addrs s1 rg)
      then begin
        assert (loc_disjoint_aux s1 la);
        assert (GSet.subset (Loc?.non_live_addrs s1 rg) (Loc?.live_addrs s1 rg));
        assert (aloc_domain c (Loc?.regions s1) (Loc?.live_addrs s1) `GSet.subset` (Ghost.reveal (Loc?.aux s1)));
        assert (GSet.mem (ALoc rg ad None) (Ghost.reveal (Loc?.aux s1)));
        assert (GSet.mem (ALoc rg ad (Some x)) (Ghost.reveal (Loc?.aux la)));
        assert (aloc_disjoint (ALoc rg ad None) (ALoc #_ #c rg ad (Some x)));
        ()
      end else ()
    end else ()
  end else ()
#pop-options

let modifies_preserves_region_liveness #al #c l1 l2 h h' r = ()

let modifies_preserves_region_liveness_reference #al #c l1 l2 h h' #t #pre r = ()

let modifies_preserves_region_liveness_aloc #al #c l1 l2 h h' #r #n x =
  if Set.mem r (Ghost.reveal (Loc?.region_liveness_tags l1))
  then begin
    assert (GSet.subset (GSet.complement GSet.empty) (Loc?.non_live_addrs l1 r));
    assert (GSet.subset (Loc?.non_live_addrs l1 r) (Loc?.live_addrs l1 r))
  end else ()

let modifies_trans'
  (#al: aloc_t) (#c: cls al)
  (s: loc c)
  (h1 h2: HS.mem)
  (h3: HS.mem)
: Lemma
  (requires (modifies s h1 h2 /\ modifies s h2 h3))
  (ensures (modifies s h1 h3))
= Classical.forall_intro_3 (fun r a b -> Classical.move_requires (c.aloc_preserved_trans #r #a b h1 h2) h3)

let modifies_trans #al #c s12 h1 h2 s23 h3 =
  let u = loc_union s12 s23 in
  modifies_loc_includes u h1 h2 s12;
  modifies_loc_includes u h2 h3 s23;
  modifies_trans' u h1 h2 h3

let addr_unused_in_aloc_preserved
    (#al: aloc_t) (#c: cls al)
    (#r: HS.rid)
    (#a: nat)
    (b: al r a)
    (h1: HS.mem)
    (h2: HS.mem)
  : Lemma
    (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))
    (ensures (c.aloc_preserved b h1 h2))
= c.same_mreference_aloc_preserved b h1 h2 (fun a' pre r' -> assert False)

#push-options "--z3rlimit 10"
let modifies_only_live_regions_weak
  (#al: aloc_t) (#c: cls al)
  (rs: Set.set HS.rid)
  (l: loc c)
  (h h' : HS.mem)
: Lemma
  (requires (
    modifies (loc_union (loc_regions false rs) l) h h' /\
    loc_disjoint (loc_regions false rs) l /\
    (forall r . Set.mem r rs ==> (~ (HS.live_region h r)))
  ))
  (ensures (modifies l h h'))
= assert (modifies_preserves_mreferences l h h'); // FIXME: WHY WHY WHY?
  Classical.forall_intro_3 (fun r a b -> Classical.move_requires (addr_unused_in_aloc_preserved #al #c #r #a b h) h')
#pop-options

(* Restrict a set of locations along a set of regions *)

let restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: GTot (loc c)
= let (Loc regions region_liveness_tags non_live_addrs live_addrs aux) = l in
  let regions' = (Ghost.hide (Set.intersect (Ghost.reveal regions) rs)) in
  Loc
    regions'
    (Ghost.hide (Set.intersect (Ghost.reveal region_liveness_tags) rs))
    (mk_non_live_addrs (fun (r: addrs_dom regions') -> (non_live_addrs r <: GSet.set nat)))
    (mk_live_addrs (fun (r: addrs_dom regions') -> (live_addrs r <: GSet.set nat)))
    (Ghost.hide (GSet.intersect (Ghost.reveal aux) (aloc_domain c (Ghost.hide rs) (fun r -> GSet.complement GSet.empty))))

let regions_of_loc_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (regions_of_loc (restrict_to_regions l rs) == Set.intersect (regions_of_loc l) rs)
  [SMTPat (regions_of_loc (restrict_to_regions l rs))]
= assert (Set.equal (regions_of_loc (restrict_to_regions l rs)) (Set.intersect (regions_of_loc l) rs))

let addrs_of_loc_weak_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc_weak (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc_weak l r else GSet.empty))
  [SMTPat (addrs_of_loc_weak (restrict_to_regions l rs) r)]
= assert (GSet.equal (addrs_of_loc_weak (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc_weak l r else GSet.empty))

let addrs_of_loc_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
  (r: HS.rid)
: Lemma
  (addrs_of_loc (restrict_to_regions l rs) r == (if Set.mem r rs then addrs_of_loc l r else GSet.empty))
  [SMTPat (addrs_of_loc (restrict_to_regions l rs) r)]
= assert (GSet.equal (addrs_of_loc (restrict_to_regions l rs) r) (if Set.mem r rs then addrs_of_loc l r else GSet.empty))

let loc_includes_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes l (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #al #c)

let loc_includes_loc_union_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_equal (loc_union (restrict_to_regions l rs) (restrict_to_regions l (Set.complement rs))) l)
= ()

let loc_includes_loc_regions_restrict_to_regions
  (#al: aloc_t) (#c: cls al)
  (l: loc c)
  (rs: Set.set HS.rid)
: Lemma
  (loc_includes (loc_regions false rs) (restrict_to_regions l rs))
= Classical.forall_intro (loc_aux_includes_refl #al #c)

let modifies_only_live_regions #al #c rs l h h' =
  let s = l in
  let c_rs = Set.complement rs in
  let s_rs = restrict_to_regions s rs in
  let s_c_rs = restrict_to_regions s c_rs in
  let lrs = loc_regions false rs in
  loc_includes_loc_regions_restrict_to_regions s rs;
  loc_includes_union_l lrs s_c_rs s_rs;
  loc_includes_refl s_c_rs;
  loc_includes_union_l lrs s_c_rs s_c_rs;
  loc_includes_union_r (loc_union lrs s_c_rs) s_rs s_c_rs;
  loc_includes_loc_union_restrict_to_regions s rs;
  loc_includes_trans (loc_union lrs s_c_rs) (loc_union s_rs s_c_rs) s;
  modifies_loc_includes (loc_union lrs s_c_rs) h h' (loc_union lrs s);
  loc_includes_loc_regions_restrict_to_regions s c_rs;
  loc_disjoint_regions #al #c false false rs c_rs;
  loc_includes_refl lrs;
  loc_disjoint_includes lrs (loc_regions false c_rs) lrs s_c_rs;
  modifies_only_live_regions_weak rs s_c_rs h h';
  loc_includes_restrict_to_regions s c_rs;
  modifies_loc_includes s h h' s_c_rs

let no_upd_fresh_region #al #c r l h0 h1 =
  modifies_only_live_regions (HS.mod_set (Set.singleton r)) l h0 h1

let fresh_frame_modifies #al c h0 h1 =
  modifies_intro_strong #_ #c loc_none h0 h1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r a x ->
      c.same_mreference_aloc_preserved #r #a x h0 h1 (fun _ _ _ -> ()))

let new_region_modifies #al c m0 r0 col
= let (_, m1) = HS.new_eternal_region m0 r0 col in
  modifies_intro_strong #_ #c loc_none m0 m1
    (fun _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ _ -> ())
    (fun _ _ -> ())
    (fun r a x ->
      c.same_mreference_aloc_preserved #r #a x m0 m1 (fun _ _ _ -> ()))

#push-options "--z3rlimit 20"
let popped_modifies #al c h0 h1 =
  let l = loc_region_only #_ #c false (HS.get_tip h0) in
  modifies_preserves_mreferences_intro l h0 h1 (fun t pre p ->
    assert_norm (Loc?.region_liveness_tags (loc_mreference #_ #c p) == Ghost.hide Set.empty);
    assert (loc_disjoint_region_liveness_tags (loc_mreference p) l );
    // FIXME: WHY WHY WHY is this assert necessary?
    assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_mreference p))) (Ghost.reveal (Loc?.aux l)));
    ()
  );
  modifies_preserves_alocs_intro l h0 h1 () (fun r a b ->
    loc_aux_disjoint_sym (Ghost.reveal (Loc?.aux l)) (Ghost.reveal (Loc?.aux (loc_of_aloc b)));
    ()
  )
#pop-options

let modifies_fresh_frame_popped #al #c h0 h1 s h2 h3 =
  fresh_frame_modifies c h0 h1;
  let r = loc_region_only #al #c false (HS.get_tip h2) in
  let rs = HS.mod_set (Set.singleton (HS.get_tip h1)) in
  let s' = loc_union (loc_regions false rs) s in
  modifies_trans' s' h0 h1 h2;
  assert (modifies_preserves_mreferences r h2 h3);
  let f23 (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (requires (r <> HS.get_tip h2))
    (ensures (c.aloc_preserved b h2 h3))
  = c.same_mreference_aloc_preserved #r #a b h2 h3 (fun a' pre r' -> ())
  in
  modifies_preserves_alocs_intro r h2 h3 () (fun r a b ->
    f23 r a b
  );
  modifies_trans' s' h0 h2 h3;
  modifies_only_live_regions rs s h0 h3

let modifies_loc_regions_intro #al #c rs h1 h2 =
  let f (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (requires (not (Set.mem r rs)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  assert (modifies_preserves_mreferences (loc_regions #al #c true rs) h1 h2);
  modifies_preserves_alocs_intro (loc_regions #_ #c true rs) h1 h2 () (fun r a b ->
    f r a b
  )

#push-options "--z3rlimit 20"
let modifies_loc_addresses_intro_weak
  (#al: aloc_t) (#c: cls al)
  (r: HS.rid)
  (s: Set.set nat)
  (l: loc c)
  (h1 h2: HS.mem)
: Lemma
  (requires (
    HS.live_region h2 r /\
    modifies (loc_union (loc_region_only false r) l) h1 h2 /\
    HS.modifies_ref r s h1 h2 /\
    loc_disjoint l (loc_region_only false r)
  ))
  (ensures (modifies (loc_union (loc_addresses true r s) l) h1 h2))
= modifies_preserves_mreferences_intro (loc_union (loc_addresses true r s) l) h1 h2 (fun r' a' b' ->
    ()
  );
  modifies_preserves_livenesses_intro (loc_union (loc_addresses true r s) l) h1 h2 (fun r' a' b' ->
    ()
  );
  modifies_preserves_not_unused_in_intro (loc_union (loc_addresses true r s) l) h1 h2 (fun r' n' ->
    ()
  );
  let f (a: nat) (b: al r a) : Lemma
    (requires (not (Set.mem a s)))
    (ensures (c.aloc_preserved b h1 h2))
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r_ -> ())
  in
  modifies_preserves_alocs_intro (loc_union (loc_addresses true r s) l) h1 h2 () (fun r' a b -> if r = r' then f a b else ()
  )

let modifies_loc_addresses_intro #al #c r s l h1 h2 =
  loc_includes_loc_regions_restrict_to_regions l (Set.singleton r);
  loc_includes_loc_union_restrict_to_regions l (Set.singleton r);
  assert (modifies (loc_union (loc_region_only false r) (loc_union (restrict_to_regions l (Set.singleton r)) (restrict_to_regions l (Set.complement (Set.singleton r))))) h1 h2);
  let l' = restrict_to_regions l (Set.complement (Set.singleton r)) in
  loc_includes_refl (loc_region_only #_ #c false r) ;
  loc_includes_loc_regions_restrict_to_regions l (Set.complement (Set.singleton r));
  loc_disjoint_regions #_ #c false false (Set.complement (Set.singleton r)) (Set.singleton r);
  loc_disjoint_includes (loc_regions #_ #c false (Set.complement (Set.singleton r))) (loc_region_only false r) l' (loc_region_only false r);
  modifies_loc_addresses_intro_weak r s l' h1 h2;
  loc_includes_restrict_to_regions l (Set.complement (Set.singleton r))
#pop-options

let modifies_ralloc_post #al #c #a #rel i init h x h' =
  let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_salloc_post #al #c #a #rel init h x h' =
  let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h h')
  = c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_free #al #c #a #rel r m =
  let g (r': HS.rid) (a: nat) (b: al r' a) : Lemma
    (requires (r' <> HS.frameOf r \/ a <> HS.as_addr r))
    (ensures (c.aloc_preserved b m (HS.free r m)))
  = c.same_mreference_aloc_preserved #r' #a b m (HS.free r m) (fun a' pre r' -> ())
  in
  modifies_preserves_alocs_intro (loc_freed_mreference #_ #c r) m (HS.free r m) () (fun r a b -> g r a b)

let modifies_none_modifies #al #c h1 h2
= let g (r: HS.rid) (a: nat) (b: al r a) : Lemma
    (c.aloc_preserved b h1 h2)
  = c.same_mreference_aloc_preserved #r #a b h1 h2 (fun a' pre r' -> ())
  in
  Classical.forall_intro_3 g

let modifies_upd #al #c #t #pre r v h =
  let h' = HS.upd h r v in
  modifies_intro #_ #c (loc_mreference r) h h'
    (fun r -> ())
    (fun t pre b -> ())
    (fun t pre b -> ())
    (fun r n -> ())
    (fun r a b -> c.same_mreference_aloc_preserved #r #a b h h' (fun a' pre' r' -> ()))

#push-options "--z3rlimit 15"
let addrs_of_loc_loc_union_loc_of_aloc_eq_loc_union_loc_addresses_singleton
  (#al: aloc_t) (#c: cls al) (l: loc c) (#r0: HS.rid) (#a0: nat) (al0: al r0 a0) (r: HS.rid)
: Lemma
  (addrs_of_loc (loc_union l (loc_of_aloc al0)) r == addrs_of_loc (loc_union l (loc_addresses true r0 (Set.singleton a0))) r)
= assert (addrs_of_loc (loc_union l (loc_of_aloc al0)) r `GSet.equal` addrs_of_loc (loc_union l (loc_addresses true r0 (Set.singleton a0))) r)
#pop-options

let addrs_of_loc_weak_loc_includes #al (#c: cls al) (l: loc c) (r0: HS.rid) (a0: nat) : Lemma
  (requires (a0 `GSet.mem` addrs_of_loc_weak l r0))
  (ensures (l `loc_includes` loc_addresses true r0 (Set.singleton a0)))
= ()

val modifies_strengthen'
  (#al: aloc_t) (#c: cls al) (l: loc c) (#r0: HS.rid) (#a0: nat) (al0: al r0 a0) (h h' : HS.mem)
  (alocs: (
    (f: ((t: Type) -> (pre: Preorder.preorder t) -> (m: HS.mreference t pre) -> Lemma
      (requires (HS.frameOf m == r0 /\ HS.as_addr m == a0 /\ HS.contains h m))
      (ensures (HS.contains h' m))
    )) ->
    (x: al r0 a0) ->
    Lemma
    (requires (c.aloc_disjoint x al0 /\ loc_disjoint (loc_of_aloc x) l))
    (ensures (c.aloc_preserved x h h'))
  ))
: Lemma
  (requires ((~ (a0 `GSet.mem` addrs_of_loc_weak l r0)) /\  modifies (loc_union l (loc_addresses true r0 (Set.singleton a0))) h h'))
  (ensures (modifies (loc_union l (loc_of_aloc al0)) h h'))

#push-options "--z3rlimit 25 --fuel 0 --ifuel 0"
let modifies_strengthen' #al #c l #r0 #a0 al0 h h' alocs =
  Classical.forall_intro (addrs_of_loc_loc_union_loc_of_aloc_eq_loc_union_loc_addresses_singleton l al0);
  assert (modifies_preserves_regions (loc_union l (loc_of_aloc al0)) h h');
  assert (modifies_preserves_mreferences (loc_union l (loc_of_aloc al0)) h h');
  assert (modifies_preserves_not_unused_in (loc_union l (loc_of_aloc al0)) h h');
  assert (modifies_preserves_livenesses (loc_union l (loc_of_aloc al0)) h h');
  modifies_preserves_alocs_intro (loc_union l (loc_of_aloc al0)) h h' () (fun r a b ->
    if r = r0 && a = a0
    then begin
      assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux (loc_union l (loc_of_aloc al0)))) (GSet.singleton (ALoc r0 a0 (Some b))));
      assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r0 a0 (Some b))));
      assert (loc_disjoint l (loc_of_aloc b));
      loc_disjoint_sym l (loc_of_aloc b);
      assert (loc_aux_disjoint #_ #c (Ghost.reveal (Loc?.aux (loc_of_aloc al0))) (GSet.singleton (ALoc r0 a0 (Some b))));
      assert (loc_aux_disjoint #_ #c (GSet.singleton (ALoc r0 a0 (Some al0))) (GSet.singleton (ALoc r0 a0 (Some b))));
      assert (GSet.mem (ALoc r0 a0 (Some al0)) (GSet.singleton (ALoc #_ #c r0 a0 (Some al0))));
      assert (GSet.mem (ALoc r0 a0 (Some b)) (GSet.singleton (ALoc #_ #c r0 a0 (Some b))));
      assert (aloc_disjoint #_ #c (ALoc r0 a0 (Some al0)) (ALoc r0 a0 (Some b)));
      assert (c.aloc_disjoint al0 b);
      c.aloc_disjoint_sym al0 b;
      alocs (fun t pre m -> ()) b
    end
    else begin
      assert (loc_disjoint (loc_union l (loc_addresses true r0 (Set.singleton a0))) (loc_of_aloc b))
          by (let open FStar.Stubs.Tactics.V2.Builtins in
              let open FStar.Tactics.SMT in
              set_rlimit 64;
              set_options "--z3cliopt 'smt.qi.eager_threshold=5'";
              ())
    end
  );
  assert (modifies (loc_union l (loc_of_aloc al0)) h h')
#pop-options

let modifies_strengthen #al #c l #r0 #a0 al0 h h' alocs =
  if a0 `GSet.mem` addrs_of_loc_weak l r0
  then begin
    addrs_of_loc_weak_loc_includes l r0 a0;
    loc_includes_refl l;
    loc_includes_union_r l l (loc_addresses true r0 (Set.singleton a0));
    loc_includes_union_l l (loc_of_aloc al0) l;
    loc_includes_trans (loc_union l (loc_of_aloc al0)) l (loc_union l (loc_addresses true r0 (Set.singleton a0)));
    modifies_loc_includes (loc_union l (loc_of_aloc al0)) h h' (loc_union l (loc_addresses true r0 (Set.singleton a0)))
  end
  else
    modifies_strengthen' l al0 h h' alocs


let does_not_contain_addr (h: HS.mem) (ra: HS.rid & nat) : GTot Type0 =
  HS.live_region h (fst ra) ==> snd ra `Heap.addr_unused_in` (HS.get_hmap h `Map.sel` (fst ra))

let not_live_region_does_not_contain_addr h ra = ()

let unused_in_does_not_contain_addr h #a #rel r = ()

let addr_unused_in_does_not_contain_addr h ra = ()

let does_not_contain_addr_addr_unused_in h ra = ()

let free_does_not_contain_addr #a #rel r m x = ()

let does_not_contain_addr_elim #a #rel r m x = ()

let disjoint_addrs_of_loc_loc_disjoint
  (#al: aloc_t)
  (#c: cls al)
  (l1 l2: loc c)
: Lemma
  (requires (
    Set.subset (Set.intersect (Ghost.reveal (Loc?.region_liveness_tags l1)) (Ghost.reveal (Loc?.region_liveness_tags l2))) Set.empty /\
    (forall r . GSet.subset (GSet.intersect (addrs_of_loc l1 r) (addrs_of_loc l2 r)) GSet.empty)
  ))
  (ensures (loc_disjoint l1 l2))
= // FIXME: WHY WHY WHY do I need this assert?
  let l1' = Ghost.reveal (Loc?.aux l1) in
  let l2' = Ghost.reveal (Loc?.aux l2) in
  assert (forall (b1 b2: aloc c) . (GSet.mem b1 l1' /\ GSet.mem b2 l2') ==> aloc_disjoint b1 b2)

let loc_not_unused_in #al c h =
  let f (r: HS.rid) : GTot (GSet.set nat) =
    GSet.comprehend (fun a -> StrongExcludedMiddle.strong_excluded_middle (HS.live_region h r /\ ~ (h `does_not_contain_addr` (r, a))))
  in
  Loc
    (Ghost.hide (Set.complement Set.empty))
    (Ghost.hide Set.empty)
    (mk_non_live_addrs f)
    (mk_live_addrs (fun x -> f x))
    (Ghost.hide (aloc_domain c (Ghost.hide (Set.complement Set.empty)) f))

let loc_unused_in #al c h =
  let f (r: HS.rid) : GTot (GSet.set nat) =
    if not (HS.live_region h r)
    then
      GSet.complement GSet.empty
    else
      GSet.comprehend (fun a -> StrongExcludedMiddle.strong_excluded_middle (h `does_not_contain_addr` (r, a)))
  in
  Loc
    (Ghost.hide (Set.complement Set.empty))
    (Ghost.hide (Set.complement (FStar.Map.domain (HS.get_hmap h))))
    (mk_non_live_addrs (fun x -> f x))
    (mk_live_addrs (fun x -> f x))
    (Ghost.hide (aloc_domain c (Ghost.hide (Set.complement Set.empty)) f))

let loc_regions_unused_in #al c h rs = ()

#push-options "--z3rlimit 20"
let loc_addresses_unused_in #al c r a h = ()
#pop-options

let loc_addresses_not_unused_in #al c r a h = ()

#push-options "--z3rlimit 50"
let loc_unused_in_not_unused_in_disjoint #al c h =
  assert (Ghost.reveal (Loc?.aux (loc_unused_in c h)) `loc_aux_disjoint` Ghost.reveal (Loc?.aux (loc_not_unused_in c h)));
  assert_spinoff (loc_disjoint #al #c (loc_unused_in #al c h)
                                      (loc_not_unused_in #al c h))
#pop-options

#push-options "--z3cliopt 'smt.qi.eager_threshold=100'"
let not_live_region_loc_not_unused_in_disjoint #al c h0 r
= let l1 = loc_region_only false r in
  let l2 = loc_not_unused_in c h0 in
  assert (loc_disjoint_region_liveness_tags l1 l2);
  assert (loc_disjoint_addrs l1 l2);
  assert (loc_disjoint_aux l1 l2)

#push-options "--z3rlimit 16"
let modifies_address_liveness_insensitive_unused_in #al c h h' =
  assert (forall r . HS.live_region h r ==> HS.live_region h' r) ;
  let ln' = loc_not_unused_in c h' in
  let ln = loc_not_unused_in c h in
  assert (forall (r: HS.rid) . Loc?.non_live_addrs ln r `GSet.subset` Loc?.non_live_addrs ln' r);
  assert (ln' `loc_includes` ln);
  let lu = loc_unused_in c h in
  let lu' = loc_unused_in c h' in
  assert (forall (r: HS.rid) . Loc?.non_live_addrs lu' r `GSet.subset` Loc?.non_live_addrs lu r);
  assert (forall (r: HS.rid) . Loc?.live_addrs lu' r `GSet.subset` Loc?.live_addrs lu r);
  assert (lu `loc_includes` lu')
#pop-options
#pop-options

#push-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 16"
let modifies_only_not_unused_in #al #c l h h' =
  assert (modifies_preserves_regions l h h');
  assert (modifies_preserves_not_unused_in l h h');
  assert (modifies_preserves_mreferences l h h');
  assert (modifies_preserves_livenesses l h h');
  modifies_preserves_alocs_intro l h h' () (fun r a b ->
    if StrongExcludedMiddle.strong_excluded_middle (h `does_not_contain_addr` (r, a))
    then c.same_mreference_aloc_preserved b h h' (fun a' pre' r' -> ())
    else ()
  )
#pop-options

#push-options "--z3rlimit 20"
let mreference_live_loc_not_unused_in #al c #t #pre h b =
  Classical.move_requires (does_not_contain_addr_addr_unused_in h) (HS.frameOf b, HS.as_addr b);
  assert (~ (h `does_not_contain_addr` (HS.frameOf b, HS.as_addr b)));
  loc_addresses_not_unused_in c (HS.frameOf b) (Set.singleton (HS.as_addr b)) h;
  loc_includes_trans (loc_not_unused_in c h) (loc_freed_mreference b) (loc_mreference b);
  ()
#pop-options

#push-options "--z3cliopt 'smt.qi.eager_threshold=100'"
let mreference_unused_in_loc_unused_in #al c #t #pre h b =
  Classical.move_requires (addr_unused_in_does_not_contain_addr h) (HS.frameOf b, HS.as_addr b);
  loc_addresses_unused_in c (HS.frameOf b) (Set.singleton (HS.as_addr b)) h;
  loc_includes_addresses_addresses c false true (HS.frameOf b) (Set.singleton (HS.as_addr b)) (Set.singleton (HS.as_addr b));
  loc_includes_trans (loc_unused_in c h) (loc_freed_mreference b) (loc_mreference b);
  ()
#pop-options

(* * Compositionality *)

noeq
type cls_union_aloc
  (al: (bool -> HS.rid -> nat -> Tot (Type u#x)))
  (r: HS.rid) (n: nat) : Type u#x
= | ALOC_FALSE of (al false) r n
  | ALOC_TRUE  of (al true) r n

let bool_of_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#r: HS.rid) (#n: nat)
  (l: cls_union_aloc al r n)
: Tot bool =
  match l with
  | ALOC_FALSE _ -> false
  | ALOC_TRUE _ -> true

let aloc_of_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#r: HS.rid) (#n: nat)
  (l: cls_union_aloc al r n)
: Tot ((al (bool_of_cls_union_aloc l)) r n)
= match l with
  | ALOC_FALSE x -> x
  | ALOC_TRUE x -> x

let make_cls_union_aloc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (b: bool)
  (#r: HS.rid)
  (#n: nat)
  (l: (al b) r n)
: Tot (cls_union_aloc al r n)
= if b
  then ALOC_TRUE l
  else ALOC_FALSE l

let cls_union_aloc_includes
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: cls_union_aloc al r a)
: GTot Type0 =
  bool_of_cls_union_aloc larger == bool_of_cls_union_aloc smaller /\
  (c (bool_of_cls_union_aloc larger)).aloc_includes
    (aloc_of_cls_union_aloc larger)
    (aloc_of_cls_union_aloc smaller)

let cls_union_aloc_disjoint
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (larger smaller: cls_union_aloc al r a)
: GTot Type0 =
  bool_of_cls_union_aloc larger == bool_of_cls_union_aloc smaller /\
  (c (bool_of_cls_union_aloc larger)).aloc_disjoint
    (aloc_of_cls_union_aloc larger)
    (aloc_of_cls_union_aloc smaller)

let cls_union_aloc_preserved
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (#r: HS.rid)
  (#a: nat)
  (x: cls_union_aloc al r a)
  (h h' : HS.mem)
: GTot Type0
= (c (bool_of_cls_union_aloc x)).aloc_preserved
    (aloc_of_cls_union_aloc x)
    h
    h'

let aloc_union = cls_union_aloc

let cls_union #al c = Cls
  #(cls_union_aloc al)
  (cls_union_aloc_includes c)
  (* aloc_includes_refl *)
  (fun #r #a x ->
    (c (bool_of_cls_union_aloc x)).aloc_includes_refl (aloc_of_cls_union_aloc x))
  (* aloc_includes_trans *)
  (fun #r #a x1 x2 x3 ->
    (c (bool_of_cls_union_aloc x1)).aloc_includes_trans
      (aloc_of_cls_union_aloc x1)
      (aloc_of_cls_union_aloc x2)
      (aloc_of_cls_union_aloc x3)
  )
  (cls_union_aloc_disjoint c)
  (* aloc_disjoint_sym *)
  (fun #r #a x1 x2 ->
    if bool_of_cls_union_aloc x1 = bool_of_cls_union_aloc x2
    then
      (c (bool_of_cls_union_aloc x1)).aloc_disjoint_sym
        (aloc_of_cls_union_aloc x1)
        (aloc_of_cls_union_aloc x2)
    else ()
  )
  (* aloc_disjoint_includes *)
  (fun #r #a larger1 larger2 smaller1 smaller2 ->
    (c (bool_of_cls_union_aloc larger1)).aloc_disjoint_includes
      (aloc_of_cls_union_aloc larger1)
      (aloc_of_cls_union_aloc larger2)
      (aloc_of_cls_union_aloc smaller1)
      (aloc_of_cls_union_aloc smaller2)
  )
  (cls_union_aloc_preserved c)
  (* aloc_preserved_refl *)
  (fun #r #a x h ->
    (c (bool_of_cls_union_aloc x)).aloc_preserved_refl
      (aloc_of_cls_union_aloc x)
      h
  )
  (* aloc_preserved_trans *)
  (fun #r #a x h1 h2 h3 ->
    (c (bool_of_cls_union_aloc x)).aloc_preserved_trans
      (aloc_of_cls_union_aloc x)
      h1
      h2
      h3
  )
  (* same_mreference_aloc_preserved *)
  (fun #r #a b h1 h2 f ->
    (c (bool_of_cls_union_aloc b)).same_mreference_aloc_preserved
      (aloc_of_cls_union_aloc b)
      h1
      h2
      f
  )

let union_aux_of_aux_left_pred
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (c b)))
  (x: aloc (cls_union c))
: GTot bool
= let ALoc region addr loc = x in
  match loc with
  | None -> GSet.mem (ALoc region addr None) s
  | Some loc ->
    b = bool_of_cls_union_aloc #al #region #addr loc &&
    GSet.mem (ALoc region addr (Some (aloc_of_cls_union_aloc #al #region #addr loc))) s

let union_aux_of_aux_left
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (c b)))
: Tot (GSet.set (aloc (cls_union c)))
= GSet.comprehend (union_aux_of_aux_left_pred c b s)

let union_loc_of_loc #al c b l =
  let (Loc regions region_liveness_tags non_live_addrs live_addrs aux) = l in
  let aux' : GSet.set (aloc #(cls_union_aloc al) (cls_union c)) =
    union_aux_of_aux_left c b (Ghost.reveal aux)
    `GSet.union`
    (aloc_domain (cls_union c) regions live_addrs)
  in
  Loc
    #(cls_union_aloc al)
    #(cls_union c)
    regions
    region_liveness_tags
    non_live_addrs
    live_addrs
    (Ghost.hide aux')

let union_aux_of_aux_left_inv_pred
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (cls_union c)))
  (x: aloc (c b))
: GTot bool
= let ALoc region addr loc = x in
  match loc with
  | None -> GSet.mem (ALoc region addr None) s
  | Some loc ->
    GSet.mem (ALoc region addr (Some (make_cls_union_aloc b loc))) s

let union_aux_of_aux_left_inv
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (#c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (s: GSet.set (aloc (cls_union c)))
: Tot (GSet.set (aloc (c b)))
= GSet.comprehend (union_aux_of_aux_left_inv_pred b s)

let mem_union_aux_of_aux_left_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (x: aloc (c b))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x aux <==> GSet.mem (ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc)))) (union_aux_of_aux_left c b aux))
  [SMTPat (GSet.mem x aux)]
= ()

let mem_union_aux_of_aux_left_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (x: aloc (cls_union c))
  (aux: GSet.set (aloc (c b)))
: Lemma
  (GSet.mem x (union_aux_of_aux_left c b aux) <==> (if None? x.loc then GSet.mem (ALoc x.region x.addr None) aux else (bool_of_cls_union_aloc (Some?.v x.loc) == b /\ GSet.mem (ALoc x.region x.addr (Some (aloc_of_cls_union_aloc (Some?.v x.loc)))) aux)))
  [SMTPat (GSet.mem x (union_aux_of_aux_left #al c b aux))]
= ()

let addrs_of_loc_union_loc_of_loc
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (r: HS.rid)
: Lemma
  (addrs_of_loc (union_loc_of_loc c b l) r `GSet.equal` addrs_of_loc l r)
  [SMTPat (addrs_of_loc (union_loc_of_loc #al c b l) r)]
= ()

let union_loc_of_loc_none #al c b =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_none #_ #(c b)))  (loc_none #_ #(cls_union c)))

#push-options "--z3rlimit 15"
let union_loc_of_loc_union #al c b l1 l2 =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_union #_ #(c b) l1 l2)) (loc_union #_ #(cls_union c) (union_loc_of_loc c b l1) (union_loc_of_loc c b l2)))
#pop-options

let union_loc_of_loc_addresses #al c b preserve_liveness r n =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_addresses #_ #(c b) preserve_liveness r n)) (loc_addresses #_ #(cls_union c) preserve_liveness r n))

let union_loc_of_loc_regions #al c b preserve_liveness r =
  assert (loc_equal #_ #(cls_union c) (union_loc_of_loc c b (loc_regions #_ #(c b) preserve_liveness r)) (loc_regions #_ #(cls_union c) preserve_liveness r))

#push-options "--z3rlimit 25"
let union_loc_of_loc_includes_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_includes` smaller))
  (ensures (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
= ();
  let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  assert (forall r a . GSet.mem (ALoc r a None) auxs ==> (
    GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux smaller)) /\
    GSet.mem (ALoc r a None) (Ghost.reveal (Loc?.aux larger)) /\
    GSet.mem (ALoc r a None) auxl
  ));
  assert (auxl `loc_aux_includes` auxs);
  let doml = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.live_addrs larger) in
  let doms = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.live_addrs smaller) in
  assert (doml `loc_aux_includes` doms)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50 --z3cliopt 'smt.qi.eager_threshold=1'"
let union_loc_of_loc_includes_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_includes` union_loc_of_loc c b smaller))
  (ensures (larger `loc_includes` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  let doml' = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.live_addrs larger) in
  let doms' = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.live_addrs smaller) in
  let doml = aloc_domain (c b) (Loc?.regions larger) (Loc?.live_addrs larger) in
  let doms = aloc_domain (c b) (Loc?.regions smaller) (Loc?.live_addrs smaller) in
  let g
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
    (y: aloc (c b))
  : GTot Type0
  = GSet.mem y (GSet.union auxl doml) /\ y `aloc_includes` x
  in
  let g' (r: HS.rid) (a: nat) (x: aloc (c b)) : GTot Type0 =
    exists (y: aloc (c b)) . g r a x y
  in
  let f
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
  : Lemma
    (requires (GSet.mem x auxs /\ (~ (GSet.mem x.addr (addrs_of_loc_weak smaller x.region)))))
    (ensures (g' r a x))
  = let x' : aloc (cls_union c) = ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc))) in
    Classical.exists_elim
      (g' r a x)
      #(aloc (cls_union c))
      #(fun y' -> GSet.mem y' (GSet.union auxl' doml') /\ y' `aloc_includes` x')
      ()
      (fun (y': aloc (cls_union c) { GSet.mem y' (GSet.union auxl' doml') /\ y' `aloc_includes` x' } ) ->
        let y : aloc (c b) = ALoc y'.region y'.addr (if None? y'.loc then None else Some (aloc_of_cls_union_aloc (Some?.v y'.loc))) in
        assert (g r a x y)
    )
  in
  let f'
    (r: HS.rid)
    (a: nat)
    (x: aloc (c b))
  : Lemma
    ((GSet.mem x auxs /\ (~ (GSet.mem x.addr (addrs_of_loc_weak smaller x.region)))) ==> g' r a x)
  = Classical.move_requires (f r a) x
  in
  Classical.forall_intro_3 f';
  assert (forall (r: HS.rid) (a: nat) (x: aloc (c b)) .
    (GSet.mem x auxs /\ GSet.mem x.addr (addrs_of_loc_weak smaller x.region)) ==>
    GSet.mem x (GSet.union auxl doml)
  ) by (
    let open FStar.Stubs.Tactics.V2.Builtins in
    set_options "--z3cliopt 'smt.qi.eager_threshold=1'";
    ()
  );
  assert (larger `loc_includes'` smaller) by (
    let open FStar.Stubs.Tactics.V2.Builtins in
    let open FStar.Tactics.SMT in
    set_rlimit 75;
    set_options "--z3cliopt 'smt.qi.eager_threshold=1'";
    ()
  );
  ()
#pop-options

let union_loc_of_loc_includes #al c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_includes_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_includes_intro c b s1) s2

#push-options "--fuel 0 --ifuel 0"
let union_loc_of_loc_disjoint_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (larger `loc_disjoint` smaller))
  (ensures (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
= let auxl = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux larger)) in
  let auxs = union_aux_of_aux_left c b (Ghost.reveal (Loc?.aux smaller)) in
  let g
    (xl xs: aloc (cls_union c))
  : Lemma
    (requires (GSet.mem xl auxl /\ GSet.mem xs auxs))
    (ensures (GSet.mem xl auxl /\ GSet.mem xs auxs /\ aloc_disjoint xl xs))
  =
    let xl' : aloc (c b) = ALoc xl.region xl.addr (if None? xl.loc then None else Some (aloc_of_cls_union_aloc (Some?.v xl.loc))) in
    let xs' : aloc (c b) = ALoc xs.region xs.addr (if None? xs.loc then None else Some (aloc_of_cls_union_aloc (Some?.v xs.loc))) in
    assert (GSet.mem xl' (Ghost.reveal (Loc?.aux larger)));
    assert (GSet.mem xs' (Ghost.reveal (Loc?.aux smaller)));
    assert (aloc_disjoint xl' xs');
    assert (aloc_disjoint xl xs)
  in
  Classical.forall_intro_2 (fun xl -> Classical.move_requires (g xl));
  assert (forall xl xs . (GSet.mem xl auxl /\ GSet.mem xs auxs) ==> aloc_disjoint xl xs);
  assert (auxl `loc_aux_disjoint` auxs);
  let larger' = union_loc_of_loc c b larger in
  let smaller' = union_loc_of_loc c b smaller in
  let doml = aloc_domain (cls_union c) (Loc?.regions larger) (Loc?.live_addrs larger) in
  let doms = aloc_domain (cls_union c) (Loc?.regions smaller) (Loc?.live_addrs smaller) in
  assert (forall (xl xs: aloc (cls_union c)) .
    (GSet.mem xl doml /\ GSet.mem xs auxs) ==> (
    xl.addr `GSet.mem` addrs_of_loc_weak larger xl.region /\
    xs.addr `GSet.mem` addrs_of_loc smaller xs.region /\
    aloc_disjoint xl xs
  )) by (
    let open FStar.Stubs.Tactics.V2.Builtins in
    let open FStar.Tactics.SMT in
    set_rlimit 64;
    set_options "--z3cliopt 'smt.qi.eager_threshold=1'";
    ()
  );
  assert (doml ` loc_aux_disjoint` auxs);
  assert (forall (xl xs: aloc (cls_union c)) .
    (GSet.mem xl auxl /\ GSet.mem xs doms) ==> (
    xl.addr `GSet.mem` addrs_of_loc larger xl.region /\
    xs.addr `GSet.mem` addrs_of_loc_weak smaller xs.region /\
    aloc_disjoint xl xs
  )) by (
    let open FStar.Tactics.SMT in
    set_rlimit 15;
    ()
  );
  assert (auxl ` loc_aux_disjoint` doms);
  assert (loc_disjoint_aux larger' smaller');
  ()
#pop-options

#push-options "--z3rlimit 32"
let union_loc_of_loc_disjoint_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (larger smaller: loc (c b))
: Lemma
  (requires (union_loc_of_loc c b larger `loc_disjoint` union_loc_of_loc c b smaller))
  (ensures (larger `loc_disjoint` smaller))
= let auxl = Ghost.reveal (Loc?.aux larger) in
  let auxl' = union_aux_of_aux_left c b auxl in
  let auxs = Ghost.reveal (Loc?.aux smaller) in
  let auxs' = union_aux_of_aux_left c b auxs in
  assert (forall (x y: aloc (c b)) . (GSet.mem x auxl /\ GSet.mem y auxs) ==> (
    let x' = ALoc x.region x.addr (if None? x.loc then None else Some (make_cls_union_aloc b (Some?.v x.loc))) in
    let y' = ALoc y.region y.addr (if None? y.loc then None else Some (make_cls_union_aloc b (Some?.v y.loc))) in
    GSet.mem x' auxl' /\ GSet.mem y' auxs' /\ (aloc_disjoint x' y' ==> aloc_disjoint x y)));
  assert (auxl `loc_aux_disjoint` auxs)
#pop-options

let union_loc_of_loc_disjoint #al c b s1 s2 =
  Classical.move_requires (union_loc_of_loc_disjoint_elim c b s1) s2;
  Classical.move_requires (union_loc_of_loc_disjoint_intro c b s1) s2

#push-options "--z3rlimit 32"
let modifies_union_loc_of_loc_elim
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2))
  (ensures (modifies #_ #(c b) l h1 h2))
= assert (modifies_preserves_regions l h1 h2);
  assert (modifies_preserves_mreferences l h1 h2);
  modifies_preserves_alocs_intro #_ #(c b) l h1 h2 () (fun r' a' b' ->
    let g
      (x: aloc (cls_union c))
    : Lemma
      (requires (
        GSet.mem a' (addrs_of_loc_aux #_ #(cls_union c) (union_loc_of_loc c b l) r') /\
        GSet.mem x (Ghost.reveal (Loc?.aux #_ #(cls_union c) (union_loc_of_loc c b l)))
      ))
      (ensures (
        aloc_disjoint #_ #(cls_union c) x (ALoc #_ #(cls_union c) r' a' (Some (make_cls_union_aloc b b')))))
    = if r' = x.region && a' = x.addr
      then begin
        let x' : aloc (c b) = ALoc #_ #(c b) r' a' (if None? x.loc then None else Some (aloc_of_cls_union_aloc (Some?.v x.loc))) in
        assert (aloc_disjoint #(al b) #(c b) x' (ALoc r' a' (Some b')))
      end else
        ()
    in
    Classical.forall_intro (Classical.move_requires g);
    assert ((cls_union c).aloc_preserved (make_cls_union_aloc b b') h1 h2)
  )
#pop-options

#push-options "--z3rlimit 32"
let modifies_union_loc_of_loc_intro
  (#al: (bool -> HS.rid -> nat -> Tot Type))
  (c: ((b: bool) -> Tot (cls (al b))))
  (b: bool)
  (l: loc (c b))
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies #_ #(c b) l h1 h2))
  (ensures (modifies #_ #(cls_union c) (union_loc_of_loc c b l) h1 h2))
= let l' = union_loc_of_loc c b l in
  assert (modifies_preserves_regions l' h1 h2);
  assert (modifies_preserves_mreferences l' h1 h2);
  assert (modifies_preserves_livenesses l' h1 h2);
  assert (modifies_preserves_not_unused_in l' h1 h2);
  modifies_preserves_alocs_intro #_ #(cls_union c) l' h1 h2 () (fun r' a' b' ->
    let b_ = bool_of_cls_union_aloc b' in
    let a_ = aloc_of_cls_union_aloc b' in
    let ll' : aloc (cls_union c) = ALoc r' a' (Some b') in
    let ll  : aloc (c b_) = ALoc r' a' (Some a_) in
    assert (exists (x: aloc (c b)) . GSet.mem x (Ghost.reveal (Loc?.aux l)) /\
        (
        let xr = x.region in
        let xa = x.addr in
        let xl : option (al b xr xa) = x.loc in
        xr == r' /\
        xa == a' /\ (
        let xl' : option (aloc_union al r' a') = if None? xl then None else Some (make_cls_union_aloc #al b (Some?.v xl)) in
        let x' : aloc (cls_union c) = ALoc r' a' xl' in
        GSet.mem x' (Ghost.reveal (Loc?.aux l')) /\
        aloc_disjoint #_ #(cls_union c) x' ll'
    )));
    assert (b_ == b);
    let f (x: aloc (c b)) : Lemma
      (requires (GSet.mem x (Ghost.reveal (Loc?.aux l))))
      (ensures (aloc_disjoint #_ #(c b) x ll))
    = let xr = x.region in
      let xa = x.addr in
      let xl : option (al b xr xa) = x.loc in
      let xl' : option (aloc_union al xr xa) = if None? xl then None else Some (make_cls_union_aloc #al b (Some?.v xl)) in
      let x' : aloc (cls_union c) = ALoc xr xa xl' in
      assert (GSet.mem x' (Ghost.reveal (Loc?.aux l')));
      assert (aloc_disjoint #_ #(cls_union c) x' ll');
      assert (aloc_disjoint #_ #(c b) x ll)
    in
    Classical.forall_intro (Classical.move_requires f);
    assert (loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton ll))
  )
#pop-options

let modifies_union_loc_of_loc #al c b l h1 h2 =
  Classical.move_requires (modifies_union_loc_of_loc_elim c b l h1) h2;
  Classical.move_requires (modifies_union_loc_of_loc_intro c b l h1) h2

let loc_of_union_loc #al #c b l
= let (Loc regions region_liveness_tags non_live_addrs live_addrs aux) = l in
  let aux' = union_aux_of_aux_left_inv b (Ghost.reveal aux) in
  Loc
    regions
    region_liveness_tags
    non_live_addrs
    live_addrs
    (Ghost.hide aux')

let loc_of_union_loc_union_loc_of_loc #al c b s
= assert (loc_of_union_loc b (union_loc_of_loc c b s) `loc_equal` s)

let loc_of_union_loc_none #al c b
= assert (loc_of_union_loc #_ #c b loc_none `loc_equal` loc_none)

let loc_of_union_loc_union #al c b l1 l2
= assert (loc_of_union_loc b (l1 `loc_union` l2) `loc_equal` (loc_of_union_loc b l1 `loc_union` loc_of_union_loc b l2))

let loc_of_union_loc_addresses #al c b preserve_liveness r n =
  assert (loc_of_union_loc #_ #c b (loc_addresses preserve_liveness r n) `loc_equal` loc_addresses preserve_liveness r n)

let loc_of_union_loc_regions #al c b preserve_liveness r =
  assert (loc_of_union_loc #_ #c b (loc_regions preserve_liveness r) `loc_equal` loc_regions preserve_liveness r)

module U = FStar.Universe

let raise_aloc al r n = U.raise_t (al r n)

let raise_cls #al c = Cls #(raise_aloc u#x u#y al)
  (fun #r #a x1 x2 -> c.aloc_includes (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a x -> c.aloc_includes_refl (U.downgrade_val x))
  (fun #r #a x1 x2 x3 -> c.aloc_includes_trans (U.downgrade_val x1) (U.downgrade_val x2) (U.downgrade_val x3))
  (fun #r #a x1 x2 -> c.aloc_disjoint (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a x1 x2 -> c.aloc_disjoint_sym (U.downgrade_val x1) (U.downgrade_val x2))
  (fun #r #a larger1 larger2 smaller1 smaller2 -> c.aloc_disjoint_includes (U.downgrade_val larger1) (U.downgrade_val larger2) (U.downgrade_val smaller1) (U.downgrade_val smaller2))
  (fun #r #a x h1 h2 -> c.aloc_preserved (U.downgrade_val x) h1 h2)
  (fun #r #a x h -> c.aloc_preserved_refl (U.downgrade_val x) h)
  (fun #r #a x h1 h2 h3 -> c.aloc_preserved_trans (U.downgrade_val x) h1 h2 h3)
  (fun #r #a b h1 h2 f -> c.same_mreference_aloc_preserved (U.downgrade_val b) h1 h2 f)

let downgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc (raise_cls u#a u#b c)) : Tot (aloc c) =
  let ALoc region addr x = a in
  ALoc region addr (if None? x then None else Some (U.downgrade_val (Some?.v x)))

let upgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc c) : Tot (aloc (raise_cls u#a u#b c)) =
  let ALoc region addr x = a in
  ALoc region addr (if None? x then None else Some (U.raise_val (Some?.v x)))

let downgrade_aloc_upgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc c) : Lemma
  (downgrade_aloc (upgrade_aloc u#a u#b a) == a)
  [SMTPat (downgrade_aloc (upgrade_aloc u#a u#b a))]
= ()

let upgrade_aloc_downgrade_aloc (#al: aloc_t u#a) (#c: cls al) (a: aloc (raise_cls u#a u#b c)) : Lemma
  (upgrade_aloc (downgrade_aloc a) == a)
  [SMTPat (upgrade_aloc u#a u#b (downgrade_aloc a))]
= ()

let raise_loc_aux_pred
  (#al: aloc_t u#a)
  (c: cls al)
  (aux: Ghost.erased (GSet.set (aloc c)))
  (a: aloc (raise_cls u#a u#b c))
: GTot bool
= GSet.mem (downgrade_aloc a) (Ghost.reveal aux)

let raise_loc #al #c l =
  let (Loc regions region_liveness_tags non_live_addrs live_addrs aux) = l in
  Loc
    regions
    region_liveness_tags
    non_live_addrs
    live_addrs
    (Ghost.hide (GSet.comprehend (raise_loc_aux_pred c aux)))

let raise_loc_none #al #c =
  assert (raise_loc u#x u#y (loc_none #_ #c) `loc_equal` loc_none)

let raise_loc_union #al #c l1 l2 =
  assert (raise_loc u#x u#y (loc_union l1 l2) `loc_equal` loc_union (raise_loc l1) (raise_loc l2))

let raise_loc_addresses #al #c preserve_liveness r a =
  assert (raise_loc u#x u#y (loc_addresses #_ #c preserve_liveness r a) `loc_equal` loc_addresses preserve_liveness r a)

let raise_loc_regions #al #c preserve_liveness r =
  assert (raise_loc u#x u#y (loc_regions #_ #c preserve_liveness r) `loc_equal` loc_regions preserve_liveness r)

#push-options "--z3rlimit 15 --z3cliopt 'smt.qi.eager_threshold=100'"
let raise_loc_includes #al #c l1 l2 =
  let l1' = raise_loc l1 in
  let l2' = raise_loc l2 in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l1')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l1)));
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l2')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l2)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l1)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l1')));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l2)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l2')));
  assert (loc_aux_includes (Ghost.reveal (Loc?.aux l1')) (Ghost.reveal (Loc?.aux l2')) <==> loc_aux_includes (Ghost.reveal (Loc?.aux l1)) (Ghost.reveal (Loc?.aux l2)))
#pop-options

#push-options "--z3rlimit 20"
let raise_loc_disjoint #al #c l1 l2 =
  let l1' = raise_loc l1 in
  let l2' = raise_loc l2 in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l1')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l1)));
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l2')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l2)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l1)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l1')));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l2)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l2')));
  assert (forall r . addrs_of_loc l1' r `GSet.equal` addrs_of_loc l1 r);
  assert (forall r . addrs_of_loc l2' r `GSet.equal` addrs_of_loc l2 r);
  assert (forall (x1 x2: aloc (raise_cls u#x u#y c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (downgrade_aloc x1) (downgrade_aloc x2));
  assert (forall (x1 x2: aloc (c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (upgrade_aloc u#x u#y x1) (upgrade_aloc x2))
#pop-options

let modifies_raise_loc #al #c l h1 h2 =
  let l' = raise_loc l in
  assert (forall (x: aloc (raise_cls c)) . GSet.mem x (Ghost.reveal (Loc?.aux l')) <==> GSet.mem (downgrade_aloc x) (Ghost.reveal (Loc?.aux l)));
  assert (forall (x: aloc c) . GSet.mem x (Ghost.reveal (Loc?.aux l)) <==> GSet.mem (upgrade_aloc x) (Ghost.reveal (Loc?.aux l')));
  assert (forall r . addrs_of_loc l' r `GSet.equal` addrs_of_loc l r);
  assert (forall (x1 x2: aloc (raise_cls u#x u#y c)) . aloc_disjoint x1 x2 <==> aloc_disjoint (downgrade_aloc x1) (downgrade_aloc x2));
  assert (forall (r: HS.rid) (a: nat) (b: raise_aloc al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l')) (GSet.singleton (ALoc r a (Some b))) ==>
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r a (Some (U.downgrade_val b)))));
  assert (modifies_preserves_alocs l h1 h2 ==> modifies_preserves_alocs l' h1 h2);
  assert (forall (r: HS.rid) (a: nat) (b: al r a) .
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l)) (GSet.singleton (ALoc r a (Some b))) ==>
    loc_aux_disjoint (Ghost.reveal (Loc?.aux l')) (GSet.singleton (ALoc r a (Some (U.raise_val b)))));
  assert (modifies_preserves_alocs l' h1 h2 ==> modifies_preserves_alocs l h1 h2)

let lower_loc_aux_pred
  (#al: aloc_t u#a)
  (c: cls al)
  (aux: Ghost.erased (GSet.set (aloc (raise_cls u#a u#b c))))
  (a: aloc c)
: GTot bool
= GSet.mem (upgrade_aloc a) (Ghost.reveal aux)

let lower_loc #al #c l =
  let (Loc regions region_liveness_tags non_live_addrs live_addrs aux) = l in
  Loc
    regions
    region_liveness_tags
    non_live_addrs
    live_addrs
    (Ghost.hide (GSet.comprehend (lower_loc_aux_pred c aux)))

let lower_loc_raise_loc #al #c l =
  assert (lower_loc (raise_loc u#x u#y l) `loc_equal` l)

let raise_loc_lower_loc #al #c l =
  assert (raise_loc (lower_loc l) `loc_equal` l)

let lower_loc_none #al #c =
  assert (lower_loc u#x u#y #_ #c loc_none `loc_equal` loc_none)

let lower_loc_union #al #c l1 l2 =
  assert (lower_loc u#x u#y (loc_union l1 l2) `loc_equal` loc_union (lower_loc l1) (lower_loc l2))

let lower_loc_addresses #al #c preserve_liveness r a =
  assert (lower_loc u#x u#y #_ #c (loc_addresses preserve_liveness r a) `loc_equal` loc_addresses preserve_liveness r a)

let lower_loc_regions #al #c preserve_liveness r =
  assert (lower_loc u#x u#y #_ #c (loc_regions preserve_liveness r) `loc_equal` loc_regions preserve_liveness r)
