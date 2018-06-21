module LowStar.Modifies

module MG = FStar.ModifiesGen
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module B = LowStar.Buffer
module U32 = FStar.UInt32

let cls : MG.cls B.abuffer = MG.Cls #B.abuffer
  B.abuffer_includes
  (fun #r #a x -> B.abuffer_includes_refl x)
  (fun #r #a x1 x2 x3 -> B.abuffer_includes_trans x1 x2 x3)
  B.abuffer_disjoint
  (fun #r #a x1 x2 -> B.abuffer_disjoint_sym x1 x2)
  (fun #r #a larger1 larger2 smaller1 smaller2 -> B.abuffer_disjoint_includes larger1 larger2 smaller1 smaller2)
  B.abuffer_preserved
  (fun #r #a x h -> B.abuffer_preserved_refl x h)
  (fun #r #a x h1 h2 h3 -> B.abuffer_preserved_trans x h1 h2 h3)
  (fun #r #a b h1 h2 f -> B.same_mreference_abuffer_preserved b h1 h2 f)

let loc = MG.loc cls

let loc_none = MG.loc_none

let loc_union = MG.loc_union

let loc_union_idem = MG.loc_union_idem

let loc_union_comm = MG.loc_union_comm

let loc_union_assoc = MG.loc_union_assoc

let loc_union_loc_none_l = MG.loc_union_loc_none_l

let loc_union_loc_none_r = MG.loc_union_loc_none_r

let loc_buffer #t b =
  if B.g_is_null b
  then
    MG.loc_none
  else
    MG.loc_of_aloc #_ #_ #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b)

let loc_buffer_null t = ()

let loc_addresses = MG.loc_addresses

let loc_regions = MG.loc_regions

let loc_includes = MG.loc_includes

let loc_includes_refl = MG.loc_includes_refl

let loc_includes_trans = MG.loc_includes_trans

let loc_includes_union_r = MG.loc_includes_union_r

let loc_includes_union_l = MG.loc_includes_union_l

let loc_includes_none = MG.loc_includes_none

let loc_includes_buffer #t b1 b2 =
  assert (B.frameOf b1 == B.frameOf b2 /\ B.as_addr b1 == B.as_addr b2);
  let t1 = B.abuffer (B.frameOf b1) (B.as_addr b1) in
  let t2 = B.abuffer (B.frameOf b2) (B.as_addr b2) in
  assert (t1 == t2);
  B.abuffer_includes_intro b1 b2;
  MG.loc_includes_aloc #_ #cls #(B.frameOf b1) #(B.as_addr b1) (B.abuffer_of_buffer b1) (B.abuffer_of_buffer b2 <: t1)

let loc_includes_gsub_buffer_r l #t b i len =
  let b' = B.gsub b i len in
  loc_includes_buffer b b';
  loc_includes_trans l (loc_buffer b) (loc_buffer b')

let loc_includes_gsub_buffer_l #t b i1 len1 i2 len2 =
  let b1 = B.gsub b i1 len1 in
  let b2 = B.gsub b1 (U32.sub i2 i1) len2 in
  loc_includes_buffer b1 b2

let loc_includes_addresses_buffer #t preserve_liveness r s p =
  MG.loc_includes_addresses_aloc #_ #cls preserve_liveness r s #(B.as_addr p) (B.abuffer_of_buffer p)

let loc_includes_region_buffer #t preserve_liveness s b =
  MG.loc_includes_region_aloc #_ #cls preserve_liveness s #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b)

let loc_includes_region_addresses = MG.loc_includes_region_addresses #_ #cls

let loc_includes_region_region = MG.loc_includes_region_region #_ #cls

let loc_includes_region_union_l = MG.loc_includes_region_union_l

let loc_includes_addresses_addresses = MG.loc_includes_addresses_addresses cls

let loc_disjoint = MG.loc_disjoint

let loc_disjoint_sym = MG.loc_disjoint_sym

let loc_disjoint_none_r = MG.loc_disjoint_none_r

let loc_disjoint_union_r = MG.loc_disjoint_union_r

let loc_disjoint_includes = MG.loc_disjoint_includes

let loc_disjoint_buffer #t1 #t2 b1 b2 =
  if B.frameOf b1 = B.frameOf b2 && B.as_addr b1 = B.as_addr b2 then
    B.abuffer_disjoint_intro b1 b2
  else ();
  MG.loc_disjoint_aloc_intro #_ #cls #(B.frameOf b1) #(B.as_addr b1) #(B.frameOf b2) #(B.as_addr b2) (B.abuffer_of_buffer b1) (B.abuffer_of_buffer b2)

let loc_disjoint_gsub_buffer #t b i1 len1 i2 len2 =
  B.gsub_disjoint b i1 len1 i2 len2;
  loc_disjoint_buffer (B.gsub b i1 len1) (B.gsub b i2 len2)

let loc_disjoint_addresses = MG.loc_disjoint_addresses_intro #_ #cls

let loc_disjoint_buffer_addresses #t p preserve_liveness r n =
  MG.loc_disjoint_aloc_addresses_intro #_ #cls #(B.frameOf p) #(B.as_addr p) (B.abuffer_of_buffer p) preserve_liveness r n

let loc_disjoint_buffer_regions #t p preserve_liveness r =
  MG.loc_disjoint_regions #_ #cls false preserve_liveness (Set.singleton (B.frameOf p)) r;
  loc_includes_region_buffer false (Set.singleton (B.frameOf p)) p;
  loc_includes_refl (loc_regions preserve_liveness r);
  MG.loc_disjoint_includes (loc_regions false (Set.singleton (B.frameOf p))) (loc_regions preserve_liveness r) (loc_buffer p) (loc_regions preserve_liveness r)

let loc_disjoint_regions = MG.loc_disjoint_regions #_ #cls

let modifies = MG.modifies

let modifies_live_region = MG.modifies_live_region

let modifies_mreference_elim = MG.modifies_mreference_elim

let modifies_buffer_elim #t1 b p h h' =
  if B.g_is_null b
  then
    assert (B.as_seq h b `Seq.equal` B.as_seq h' b)
  else begin
    MG.modifies_aloc_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b) p h h' ;
    B.abuffer_preserved_elim b h h'
  end

let modifies_refl = MG.modifies_refl

let modifies_loc_includes = MG.modifies_loc_includes

let address_liveness_insensitive_locs = MG.address_liveness_insensitive_locs _

let region_liveness_insensitive_locs = MG.region_liveness_insensitive_locs _

let address_liveness_insensitive_buffer #t b =
  MG.loc_includes_address_liveness_insensitive_locs_aloc #_ #cls #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b)

let address_liveness_insensitive_addresses =
  MG.loc_includes_address_liveness_insensitive_locs_addresses cls

let region_liveness_insensitive_buffer #t b =
  MG.loc_includes_region_liveness_insensitive_locs_loc_of_aloc #_ cls #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b)

let region_liveness_insensitive_addresses =
  MG.loc_includes_region_liveness_insensitive_locs_loc_addresses cls

let region_liveness_insensitive_regions =
  MG.loc_includes_region_liveness_insensitive_locs_loc_regions cls

let region_liveness_insensitive_address_liveness_insensitive =
  MG.loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference = MG.modifies_preserves_liveness

let modifies_liveness_insensitive_buffer l1 l2 h h' #t x =
  if B.g_is_null x
  then ()
  else
    B.liveness_preservation_intro h h' x (fun t' pre r ->
      MG.modifies_preserves_liveness_strong l1 l2 h h' r (B.abuffer_of_buffer x)
    )

let modifies_liveness_insensitive_region = MG.modifies_preserves_region_liveness

let modifies_liveness_insensitive_region_mreference = MG.modifies_preserves_region_liveness_reference

let modifies_liveness_insensitive_region_buffer l1 l2 h h' #t x =
  if B.g_is_null x
  then ()
  else
    MG.modifies_preserves_region_liveness_aloc l1 l2 h h' #(B.frameOf x) #(B.as_addr x) (B.abuffer_of_buffer x)

let modifies_trans = MG.modifies_trans

let modifies_only_live_regions = MG.modifies_only_live_regions

let no_upd_fresh_region = MG.no_upd_fresh_region

let fresh_frame_modifies = MG.fresh_frame_modifies #_ cls

let popped_modifies = MG.popped_modifies #_ cls

let modifies_fresh_frame_popped = MG.modifies_fresh_frame_popped

let modifies_loc_regions_intro = MG.modifies_loc_regions_intro #_ #cls

let modifies_loc_addresses_intro = MG.modifies_loc_addresses_intro #_ #cls

let modifies_ralloc_post = MG.modifies_ralloc_post #_ #cls

let modifies_salloc_post = MG.modifies_salloc_post #_ #cls

let modifies_free = MG.modifies_free #_ #cls

let modifies_none_modifies = MG.modifies_none_modifies #_ #cls

let modifies_0_modifies h1 h2 =
  MG.modifies_none_intro #_ #cls h1 h2
    (fun r -> B.modifies_0_live_region h1 h2 r)
    (fun t pre b -> B.modifies_0_mreference #t #pre h1 h2 b)
    (fun r n -> B.modifies_0_unused_in h1 h2 r n)

let modifies_1_modifies #t b h1 h2 =
  if B.g_is_null b
  then begin
    B.modifies_1_null b h1 h2;
    modifies_0_modifies h1 h2
  end else
   MG.modifies_intro (loc_buffer b) h1 h2
    (fun r -> B.modifies_1_live_region b h1 h2 r)
    (fun t pre p ->
      loc_disjoint_sym (loc_mreference p) (loc_buffer b);
      MG.loc_disjoint_aloc_addresses_elim #_ #cls #(B.frameOf b) #(B.as_addr b) (B.abuffer_of_buffer b) true (HS.frameOf p) (Set.singleton (HS.as_addr p));
      B.modifies_1_mreference b h1 h2 p
    )
    (fun t pre p ->
      B.modifies_1_liveness b h1 h2 p
    )
    (fun r n ->
      B.modifies_1_unused_in b h1 h2 r n
    )
    (fun r' a' b' ->
      loc_disjoint_sym (MG.loc_of_aloc b') (loc_buffer b);
      MG.loc_disjoint_aloc_elim #_ #cls #(B.frameOf b) #(B.as_addr b)  #r' #a' (B.abuffer_of_buffer b)  b';
      if B.frameOf b = r' && B.as_addr b = a'
      then
        B.modifies_1_abuffer #t b h1 h2 b'
      else
        B.same_mreference_abuffer_preserved #r' #a' b' h1 h2
          (fun a_ pre_ r_ -> B.modifies_1_mreference b h1 h2 r_)
    )

let modifies_addr_of_modifies #t b h1 h2 =
  MG.modifies_address_intro #_ #cls (B.frameOf b) (B.as_addr b) h1 h2
    (fun r -> B.modifies_addr_of_live_region b h1 h2 r)
    (fun t pre p ->
      B.modifies_addr_of_mreference b h1 h2 p
    )
    (fun r n ->
      B.modifies_addr_of_unused_in b h1 h2 r n
    )


let mreference_live_buffer_unused_in_disjoint #t1 #pre #t2 h b1 b2 =
  B.unused_in_equiv b2 h;
  loc_disjoint_includes (loc_addresses false (HS.frameOf b1) (Set.singleton (HS.as_addr b1))) (loc_addresses false (B.frameOf b2) (Set.singleton (B.as_addr b2))) (loc_freed_mreference b1) (loc_buffer b2)

let buffer_live_mreference_unused_in_disjoint #t1 #t2 #pre h b1 b2 =
  B.unused_in_equiv b1 h;
  loc_disjoint_includes (loc_addresses false (B.frameOf b1) (Set.singleton (B.as_addr b1))) (loc_addresses false (HS.frameOf b2) (Set.singleton (HS.as_addr b2))) (loc_buffer b1) (loc_freed_mreference b2)

let does_not_contain_addr = MG.does_not_contain_addr

let not_live_region_does_not_contain_addr = MG.not_live_region_does_not_contain_addr

let unused_in_does_not_contain_addr = MG.unused_in_does_not_contain_addr

let addr_unused_in_does_not_contain_addr = MG.addr_unused_in_does_not_contain_addr

let free_does_not_contain_addr = MG.free_does_not_contain_addr

let does_not_contain_addr_elim = MG.does_not_contain_addr_elim

let modifies_only_live_addresses = MG.modifies_only_live_addresses

val loc_not_unused_in (h: HS.mem) : GTot loc
let loc_not_unused_in = MG.loc_not_unused_in _

val loc_unused_in (h: HS.mem) : GTot loc
let loc_unused_in = MG.loc_unused_in _

val live_loc_not_unused_in (#t: Type) (b: B.buffer t) (h: HS.mem) : Lemma
  (requires (B.live h b))
  (ensures (loc_not_unused_in h `loc_includes` loc_buffer b))

let live_loc_not_unused_in #t b h =
  B.unused_in_equiv b h;
  Classical.move_requires (MG.does_not_contain_addr_addr_unused_in h) (B.frameOf b, B.as_addr b);
  MG.loc_addresses_not_unused_in cls (B.frameOf b) (Set.singleton (B.as_addr b)) h;
  loc_includes_addresses_buffer false (B.frameOf b) (Set.singleton (B.as_addr b)) b;
  MG.loc_includes_trans (loc_not_unused_in h) (loc_addresses false (B.frameOf b) (Set.singleton (B.as_addr b))) (loc_buffer b);
  ()

val unused_in_loc_unused_in (#t: Type) (b: B.buffer t) (h: HS.mem) : Lemma
  (requires (B.unused_in b h))
  (ensures (loc_unused_in h `loc_includes` loc_buffer b))

let unused_in_loc_unused_in #t b h =
  B.unused_in_equiv b h;
  Classical.move_requires (MG.addr_unused_in_does_not_contain_addr h) (B.frameOf b, B.as_addr b);
  MG.loc_addresses_unused_in cls (B.frameOf b) (Set.singleton (B.as_addr b)) h;
  loc_includes_addresses_buffer false (B.frameOf b) (Set.singleton (B.as_addr b)) b;
  MG.loc_includes_trans (loc_unused_in h) (loc_addresses false (B.frameOf b) (Set.singleton (B.as_addr b))) (loc_buffer b);
  ()


let cloc_cls = cls

let cloc_of_loc l = l

let loc_of_cloc l = l

let loc_of_cloc_of_loc l = ()

let cloc_of_loc_of_cloc l = ()

let cloc_of_loc_none _ = ()

let cloc_of_loc_union _ _ = ()

let cloc_of_loc_addresses _ _ _ = ()

let cloc_of_loc_regions _ _ = ()

let loc_includes_to_cloc l1 l2 = ()

let loc_disjoint_to_cloc l1 l2 = ()

let modifies_to_cloc l h1 h2 = ()
