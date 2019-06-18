module LowStar.Permissions.References

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module MG = FStar.ModifiesGen

open LowStar.Permissions
open FStar.Real


(**** Defining pointers as references + pid *)


type value_with_perms (a: Type0) = vp : (a & Ghost.erased (perms_rec a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

let same_value_with_perms_implies_equal_types
 (a1: Type0)
 (a2: Type0)
 (vp1: value_with_perms a1)
 (vp2: value_with_perms a2)
 : Lemma (vp1 === vp2 ==> a1 == a2)
 = ()

type with_perm (a: Type) = {
  wp_v: a;
  wp_perm: permission;
}

noeq type pointer (a: Type0) = {
  ptr_v: HST.reference (value_with_perms a);
  ptr_pid: Ghost.erased perm_id
}


let frame_of_pointer (#a: Type0) (ptr: pointer a) : HS.rid =
  HS.frameOf ptr.ptr_v

let pointer_as_addr (#a: Type0) (ptr: pointer a) : GTot nat =
  HS.as_addr ptr.ptr_v

let mergeable (#a: Type) (ptr1 ptr2: pointer a) : Type0 =
  ptr1.ptr_v == ptr2.ptr_v /\ (Ghost.reveal ptr1.ptr_pid) <> (Ghost.reveal ptr2.ptr_pid)

(**** Reading pointer properties *)

let sel (#a: Type0)  (h: HS.mem) (ptr: pointer a) : GTot (with_perm a) =
  let (_, perm_map) = HS.sel h ptr.ptr_v in
  let perm = get_permission_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
  let snapshot = get_snapshot_from_pid (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
  { wp_v = snapshot; wp_perm = perm}

let pointer_live (#a: Type0) (ptr: pointer a) (h: HS.mem) =
  let a_with_perm = sel h ptr in
  a_with_perm.wp_perm >. 0.0R /\ HS.contains h ptr.ptr_v /\
  HS.is_mm ptr.ptr_v /\ HST.is_eternal_region (frame_of_pointer ptr)

let readable (#a: Type0) (ptr: pointer a) (h: HS.mem) : GTot bool =
  (sel h ptr).wp_perm >. 0.0R

let writeable (#a: Type0) (ptr: pointer a) (h: HS.mem) : GTot bool =
  (sel h ptr).wp_perm = 1.0R


(**** Pointer locations *)

type ploc_ (region: HS.rid) (addr: nat) = perm_id

type ploc (region: HS.rid) (addr: nat) = Ghost.erased (ploc_ region addr)

let ploc_includes (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1) == (Ghost.reveal ploc2)

let ploc_disjoint  (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1) =!= (Ghost.reveal ploc2)

let ploc_preserved  (#r: HS.rid) (#a: nat) (ploc: ploc r a) (h0 h1: HS.mem) =
  forall (t: Type0) (ptr: pointer t) .
  let pid = Ghost.reveal ptr.ptr_pid in
  (pointer_live ptr h0 /\
    frame_of_pointer ptr == r /\
    pointer_as_addr ptr == a /\
    (Ghost.reveal ploc) == pid) ==>
  (sel h0 ptr == sel h1 ptr /\
      pointer_live ptr h1)

let ploc_preserved_intro (#r: HS.rid) (#a: nat) (ploc: ploc r a) (h0 h1: HS.mem)
  (lemma: (t: Type0 -> ptr: pointer t -> Lemma
    (requires (
      let pid = Ghost.reveal ptr.ptr_pid in
      pointer_live ptr h0 /\
      frame_of_pointer ptr == r /\
      pointer_as_addr ptr == a /\
      (Ghost.reveal ploc) == pid))
    (ensures (sel h0 ptr == sel h1 ptr /\
      pointer_live ptr h1))
  )) : Lemma (ploc_preserved #r #a ploc h0 h1)
  =
  let aux (t: Type0) (ptr: pointer t) : Lemma(
    let pid = Ghost.reveal ptr.ptr_pid in
    (pointer_live ptr h0 /\
      frame_of_pointer ptr == r /\
      pointer_as_addr ptr == a /\
      (Ghost.reveal ploc) == pid) ==>
    (sel h0 ptr == sel h1 ptr /\
      pointer_live ptr h1)
  ) =
  let aux' (_ : squash (
     let pid = Ghost.reveal ptr.ptr_pid in
      pointer_live ptr h0 /\
      frame_of_pointer ptr == r /\
      pointer_as_addr ptr == a /\
      (Ghost.reveal ploc) == pid)
    ) : Lemma (sel h0 ptr == sel h1 ptr /\
      pointer_live ptr h1)
    = lemma t ptr
  in
    Classical.impl_intro aux'
  in
  Classical.forall_intro_2 aux

open FStar.ModifiesGen

let cls : cls ploc = Cls #ploc
  ploc_includes
  (fun #r #a x -> ())
  (fun #r #a x1 x2 x3 -> ())
  ploc_disjoint
  (fun #r #a x1 x2 -> ())
  (fun #r #a larger1 larger2 smaller1 smaller2 -> ())
  ploc_preserved
  (fun #r #a x h -> ())
  (fun #r #a x h1 h2 h3 -> ())
  (fun #r #a b h0 h1 f ->
    ploc_preserved_intro #r #a b h0 h1 (fun t ptr ->
      f (value_with_perms t) (Heap.trivial_preorder (value_with_perms t)) ptr.ptr_v
    )
  )

let loc = loc cls

let aloc_pointer (#a: Type0) (ptr: pointer a) : (ploc (frame_of_pointer ptr) (pointer_as_addr ptr)) =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  let pid =  Ghost.reveal ptr.ptr_pid in
  let out = (pid <:  ploc_ r a) in
  Ghost.hide out

let loc_pointer (#a: Type0) (ptr: pointer a) : GTot loc =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  loc_of_aloc #ploc #cls
  #r
  #a
  (aloc_pointer ptr)

(**** Pointer locations lemma library *)

let modifies_pointer_elim
  (#t: Type)
  (ptr: pointer t)
  (p : loc)
  (h h': HS.mem)
: Lemma
  (requires (
    pointer_live ptr h /\
    loc_disjoint (loc_pointer ptr) p /\
    modifies p h h'
  ))
  (ensures (
    sel h ptr  == sel h' ptr /\
    pointer_live ptr h'
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (sel h ptr) ];
    [ SMTPat (modifies p h h'); SMTPat (pointer_live ptr h) ];
    [ SMTPat (modifies p h h'); SMTPat (sel h' ptr) ];
    [ SMTPat (modifies p h h'); SMTPat (pointer_live ptr h') ];
  ]] =
  MG.modifies_aloc_elim
        #_ #cls
        #(frame_of_pointer #t ptr)
        #(pointer_as_addr ptr)
        (aloc_pointer ptr)
        p
        h h'

(* Some loc patterns *)

let loc_union_idem
  (s: loc)
: Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]
= loc_union_idem s

let loc_union_comm
  (s1 s2: loc)
: Lemma
  (loc_union s1 s2 == loc_union s2 s1)
  [SMTPat (loc_union s1 s2)]
= loc_union_comm s1 s2

let loc_union_idem_1
  (s1 s2: loc)
: Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2))]
= loc_union_assoc s1 s1 s2

let loc_union_idem_2
  (s1 s2: loc)
: Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]
= loc_union_assoc s1 s2 s2

let loc_union_loc_none_l
  (s: loc)
: Lemma
  (loc_union loc_none s == s)
  [SMTPat (loc_union loc_none s)]
= loc_union_loc_none_l s

let loc_union_loc_none_r
  (s: loc)
: Lemma
  (loc_union s loc_none == s)
  [SMTPat (loc_union s loc_none)]
= loc_union_loc_none_r s

let loc_includes_refl
  (s: loc)
: Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]
= loc_includes_refl s

let loc_includes_trans_backwards
  (s1 s2 s3: loc)
: Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]
= loc_includes_trans s1 s2 s3

let loc_includes_union_l
  (s1 s2 s: loc)
  : Lemma
      (requires (loc_includes s1 s \/ loc_includes s2 s))
      (ensures (loc_includes (loc_union s1 s2) s))
      [SMTPat (loc_includes (loc_union s1 s2) s)]
  = loc_includes_union_l s1 s2 s

let loc_includes_union_r
  (s s1 s2: loc)
: Lemma
  (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
  [SMTPat (loc_includes s (loc_union s1 s2))]
= Classical.move_requires (loc_includes_union_r s s1) s2;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s1;
  Classical.move_requires (MG.loc_includes_union_l s1 s2) s2;
  Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s1;
  Classical.move_requires (loc_includes_trans s (loc_union s1 s2)) s2

let loc_includes_none
  (s: loc)
: Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]
= loc_includes_none s

let loc_includes_region_addresses
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s: Set.set HS.rid)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (requires (Set.mem r s))
  (ensures (loc_includes #_ #cls (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a)))
  [SMTPat (loc_includes #_ #cls (loc_regions preserve_liveness1 s) (loc_addresses preserve_liveness2 r a))]
= loc_includes_region_addresses #_ #cls preserve_liveness1 preserve_liveness2 s r a

let loc_includes_region_addresses'
  (preserve_liveness: bool)
  (r: HS.rid)
  (a: Set.set nat)
: Lemma
  (loc_includes #_ #cls (loc_regions true (Set.singleton r)) (loc_addresses preserve_liveness r a))
  [SMTPat (loc_addresses #_ #cls preserve_liveness r a)]
= ()

let loc_includes_region_region
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires ((preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes #_ #cls (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2)))
  [SMTPat (loc_includes #_ #cls (loc_regions preserve_liveness1 s1) (loc_regions preserve_liveness2 s2))]
= loc_includes_region_region #_ #cls preserve_liveness1 preserve_liveness2 s1 s2

let loc_includes_region_region'
  (preserve_liveness: bool)
  (s: Set.set HS.rid)
: Lemma
  (loc_includes #_ #cls (loc_regions false s) (loc_regions preserve_liveness s))
  [SMTPat (loc_regions #_ #cls preserve_liveness s)]
= ()

let loc_includes_adresses_ploc (#a: Type) (ptr: pointer a) (preserve_liveness: bool)
: Lemma (
    loc_includes (loc_addresses preserve_liveness (frame_of_pointer ptr) (Set.singleton (pointer_as_addr ptr)))
      (loc_pointer ptr)
  )
  [SMTPat (loc_addresses #ploc #cls preserve_liveness (frame_of_pointer ptr) (Set.singleton (pointer_as_addr ptr)));
   SMTPat (loc_pointer ptr)]
=
  loc_includes_addresses_aloc #ploc #cls preserve_liveness (frame_of_pointer ptr) (Set.singleton (pointer_as_addr ptr))
    #(pointer_as_addr ptr) (aloc_pointer ptr)

let loc_includes_region_union_l
  (preserve_liveness: bool)
  (l: loc)
  (s1 s2: Set.set HS.rid)
: Lemma
  (requires (loc_includes l (loc_regions preserve_liveness (Set.intersect s2 (Set.complement s1)))))
  (ensures (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2)))
  [SMTPat (loc_includes (loc_union (loc_regions preserve_liveness s1) l) (loc_regions preserve_liveness s2))]
= loc_includes_region_union_l preserve_liveness l s1 s2

let loc_includes_addresses_addresses_1
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (s1 s2: Set.set nat)
: Lemma
  (requires (r1 == r2 /\ (preserve_liveness1 ==> preserve_liveness2) /\ Set.subset s2 s1))
  (ensures (loc_includes #_ #cls (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2)))
  [SMTPat (loc_includes #_ #cls (loc_addresses preserve_liveness1 r1 s1) (loc_addresses preserve_liveness2 r2 s2))]
= loc_includes_addresses_addresses cls preserve_liveness1 preserve_liveness2 r1 s1 s2

let loc_includes_addresses_addresses_2
  (preserve_liveness: bool)
  (r: HS.rid)
  (s: Set.set nat)
: Lemma
  (loc_includes #_ #cls (loc_addresses false r s) (loc_addresses preserve_liveness r s))
  [SMTPat (loc_addresses #_ #cls preserve_liveness r s)]
= ()

let loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]
= Classical.move_requires (loc_disjoint_sym s1) s2;
  Classical.move_requires (loc_disjoint_sym s2) s1

let loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]
= loc_disjoint_none_r s

let loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]
= Classical.move_requires (loc_disjoint_union_r s s1) s2;
  loc_includes_union_l s1 s2 s1;
  loc_includes_union_l s1 s2 s2;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s1;
  Classical.move_requires (loc_disjoint_includes s (loc_union s1 s2) s) s2

let loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]
= loc_disjoint_includes b1 b2 b1 b2'

let loc_disjoint_addresses
  (preserve_liveness1 preserve_liveness2: bool)
  (r1 r2: HS.rid)
  (n1 n2: Set.set nat)
: Lemma
  (requires (r1 <> r2 \/ Set.subset (Set.intersect n1 n2) Set.empty))
  (ensures (loc_disjoint #_ #cls (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2)))
  [SMTPat (loc_disjoint #_ #cls (loc_addresses preserve_liveness1 r1 n1) (loc_addresses preserve_liveness2 r2 n2))]
= loc_disjoint_addresses #_ #cls preserve_liveness1 preserve_liveness2 r1 r2 n1 n2

let loc_disjoint_regions
  (preserve_liveness1: bool)
  (preserve_liveness2: bool)
  (rs1 rs2: Set.set HS.rid)
: Lemma
  (requires (Set.subset (Set.intersect rs1 rs2) Set.empty))
  (ensures (loc_disjoint #_ #cls (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2)))
  [SMTPat (loc_disjoint #_ #cls (loc_regions preserve_liveness1 rs1) (loc_regions preserve_liveness2 rs2))]
= loc_disjoint_regions #_ #cls preserve_liveness1 preserve_liveness2 rs1 rs2

let modifies_live_region
  (s: loc)
  (h1 h2: HS.mem)
  (r: HS.rid)
: Lemma
  (requires (modifies s h1 h2 /\ loc_disjoint s (loc_region_only false r) /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))
  [SMTPatOr [
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h1 r)];
    [SMTPat (modifies s h1 h2); SMTPat (HS.live_region h2 r)];
  ]]
= modifies_live_region s h1 h2 r

let modifies_mreference_elim
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
= modifies_mreference_elim b p h h'

let modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]
= modifies_refl s h

let modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]
= modifies_loc_includes s1 h h' s2

let address_liveness_insensitive_addresses (r: HS.rid) (a: Set.set nat) : Lemma
  (address_liveness_insensitive_locs cls `loc_includes` (loc_addresses #_ #cls true r a))
  [SMTPat (address_liveness_insensitive_locs cls `loc_includes` (loc_addresses #_ #cls true r a))]
= loc_includes_address_liveness_insensitive_locs_addresses cls r a

let region_liveness_insensitive_addresses (preserve_liveness: bool) (r: HS.rid) (a: Set.set nat) : Lemma
  (region_liveness_insensitive_locs cls `loc_includes` (loc_addresses preserve_liveness r a))
  [SMTPat (region_liveness_insensitive_locs cls `loc_includes` (loc_addresses preserve_liveness r a))]
= loc_includes_region_liveness_insensitive_locs_loc_addresses cls preserve_liveness r a

let region_liveness_insensitive_regions (rs: Set.set HS.rid) : Lemma
  (region_liveness_insensitive_locs cls `loc_includes` (loc_regions true rs))
  [SMTPat (region_liveness_insensitive_locs cls `loc_includes` (loc_regions true rs))]
= loc_includes_region_liveness_insensitive_locs_loc_regions cls rs

let region_liveness_insensitive_address_liveness_insensitive:
  squash (region_liveness_insensitive_locs cls `loc_includes` address_liveness_insensitive_locs _)
= loc_includes_region_liveness_insensitive_locs_address_liveness_insensitive_locs cls

let modifies_liveness_insensitive_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ address_liveness_insensitive_locs cls `loc_includes` l2 /\ h `HS.contains` x))
  (ensures (h' `HS.contains` x))
  [SMTPatOr [
    [SMTPat (h `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
    [SMTPat (h' `HS.contains` x); SMTPat (modifies (loc_union l1 l2) h h');];
  ]]
= modifies_preserves_liveness l1 l2 h h' x

let modifies_liveness_insensitive_mreference_weak
  (l : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
 : Lemma (requires (modifies l h h' /\
                    address_liveness_insensitive_locs cls `loc_includes` l /\
		    h `HS.contains` x))
         (ensures  (h' `HS.contains` x))
         [SMTPatOr [
           [SMTPat (h `HS.contains` x); SMTPat (modifies l h h');];
           [SMTPat (h' `HS.contains` x); SMTPat (modifies l h h');];
         ]]
  = modifies_liveness_insensitive_mreference loc_none l h h' x

let modifies_liveness_insensitive_region
  (l1 l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_region_only false x) /\ region_liveness_insensitive_locs cls `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' x)];
  ]]
= modifies_preserves_region_liveness l1 l2 h h' x

let modifies_liveness_insensitive_region_mreference
  (l1 l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
: Lemma
  (requires (modifies (loc_union l1 l2) h h' /\ loc_disjoint l1 (loc_mreference x) /\ region_liveness_insensitive_locs cls `loc_includes` l2 /\ HS.live_region h (HS.frameOf x)))
  (ensures (HS.live_region h' (HS.frameOf x)))
  [SMTPatOr [
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h (HS.frameOf x))];
    [SMTPat (modifies (loc_union l1 l2) h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
  ]]
= modifies_preserves_region_liveness_reference l1 l2 h h' x

let modifies_liveness_insensitive_region_weak
  (l2 : loc)
  (h h' : HS.mem)
  (x: HS.rid)
: Lemma
  (requires (modifies l2 h h' /\ region_liveness_insensitive_locs cls `loc_includes` l2 /\ HS.live_region h x))
  (ensures (HS.live_region h' x))
  [SMTPatOr [
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h x)];
    [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' x)];
  ]]
= modifies_liveness_insensitive_region loc_none l2 h h' x

let modifies_liveness_insensitive_region_mreference_weak
  (l2 : loc)
  (h h' : HS.mem)
  (#t: Type)
  (#pre: Preorder.preorder t)
  (x: HS.mreference t pre)
  : Lemma (requires (modifies l2 h h' /\
                     region_liveness_insensitive_locs cls `loc_includes` l2 /\
		     HS.live_region h (HS.frameOf x)))
          (ensures (HS.live_region h' (HS.frameOf x)))
          [SMTPatOr [
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h (HS.frameOf x))];
            [SMTPat (modifies l2 h h'); SMTPat (HS.live_region h' (HS.frameOf x))];
          ]]
  = modifies_liveness_insensitive_region_mreference loc_none l2 h h' x


let modifies_trans_linear (l l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies l h1 h2 /\ modifies l_goal h2 h3 /\ l_goal `loc_includes` l))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (modifies l h1 h2); SMTPat (modifies l_goal h1 h3)]
  = modifies_trans l h1 h2 l_goal h3


let no_upd_fresh_region: r:HS.rid -> l:loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (HS.fresh_region r h0 h1 /\ modifies (loc_union (loc_all_regions_from false r) l) h0 h1))
  (ensures  (modifies l h0 h1))
  [SMTPat (HS.fresh_region r h0 h1); SMTPat (modifies l h0 h1)]
= no_upd_fresh_region

let new_region_modifies (m0: HS.mem) (r0: HS.rid) (col: option int) : Lemma
  (requires (HST.is_eternal_region r0 /\ HS.live_region m0 r0 /\ (None? col \/ HS.is_eternal_color (Some?.v col))))
  (ensures (
    let (_, m1) = HS.new_eternal_region m0 r0 col in
    modifies (loc_none #_ #cls) m0 m1
  ))
  [SMTPat (HS.new_eternal_region m0 r0 col)]
= new_region_modifies cls m0 r0 col

let modifies_ralloc_post
  (#a: Type)
  (#rel: Preorder.preorder a)
  (i: HS.rid)
  (init: a)
  (h: HS.mem)
  (x: HST.mreference a rel { HST.is_eternal_region (HS.frameOf x) } )
  (h' : HS.mem)
: Lemma
  (requires (HST.ralloc_post i init h x h'))
  (ensures (modifies #_ #cls loc_none h h'))
  [SMTPat (HST.ralloc_post i init h x h')]
= modifies_ralloc_post #_ #cls i init h x h'

let modifies_free
  (#a: Type)
  (#rel: Preorder.preorder a)
  (r: HS.mreference a rel { HS.is_mm r } )
  (m: HS.mem { m `HS.contains` r } )
: Lemma
  (modifies (loc_freed_mreference #_ #cls r) m (HS.free r m))
  [SMTPat (HS.free r m)]
= modifies_free #_ #cls r m

let modifies_upd
  (#t: Type) (#pre: Preorder.preorder t)
  (r: HS.mreference t pre)
  (v: t)
  (h: HS.mem)
: Lemma
  (requires (HS.contains h r))
  (ensures (modifies (loc_mreference #_ #cls r) h (HS.upd h r v)))
  [SMTPat (HS.upd h r v)]
= modifies_upd #_ #cls r v h

let fresh_frame_loc_not_unused_in_disjoint
  (h0 h1: HS.mem)
: Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures (loc_disjoint (loc_region_only false (HS.get_tip h1)) (loc_not_unused_in cls h0)))
  [SMTPat (HS.fresh_frame h0 h1)]
= not_live_region_loc_not_unused_in_disjoint cls h0 (HS.get_tip h1)

let mreference_live_loc_not_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (h `HS.contains` r))
  (ensures (loc_not_unused_in cls h `loc_includes` loc_freed_mreference r /\ loc_not_unused_in cls h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.contains h r)];
    [SMTPat (loc_not_unused_in cls h `loc_includes` loc_mreference r)];
    [SMTPat (loc_not_unused_in cls h `loc_includes` loc_freed_mreference r)];
  ]]
= mreference_live_loc_not_unused_in cls h r

let mreference_unused_in_loc_unused_in
  (#t: Type)
  (#pre: Preorder.preorder t)
  (h: HS.mem)
  (r: HS.mreference t pre)
: Lemma
  (requires (r `HS.unused_in` h))
  (ensures (loc_unused_in cls h `loc_includes` loc_freed_mreference r /\ loc_unused_in cls h `loc_includes` loc_mreference r))
  [SMTPatOr [
    [SMTPat (HS.unused_in r h)];
    [SMTPat (loc_unused_in cls h `loc_includes` loc_mreference r)];
    [SMTPat (loc_unused_in cls h `loc_includes` loc_freed_mreference r)];
  ]]
= mreference_unused_in_loc_unused_in cls h r

let unused_in_not_unused_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in _ h `loc_includes` l1 /\ loc_not_unused_in _ h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in _ h `loc_includes` l1); SMTPat (loc_not_unused_in _ h `loc_includes` l2)]
= loc_includes_trans (loc_unused_in _ h) l1 l1' ;
  loc_includes_trans (loc_not_unused_in _ h) l2 l2'  ;
  loc_unused_in_not_unused_in_disjoint cls h ;
  loc_disjoint_includes (loc_unused_in _ h) (loc_not_unused_in _ h) l1' l2'

let modifies_loc_unused_in
  (l: loc)
  (h1 h2: HS.mem)
  (l' : loc)
: Lemma
  (requires (
    modifies l h1 h2 /\
    address_liveness_insensitive_locs _ `loc_includes` l /\
    loc_unused_in _ h2 `loc_includes` l'
  ))
  (ensures (loc_unused_in _ h1 `loc_includes` l'))
  [SMTPatOr [
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in _ h2 `loc_includes` l')];
    [SMTPat (modifies l h1 h2); SMTPat (loc_unused_in _ h1 `loc_includes` l')];
  ]]
=
  modifies_loc_includes (address_liveness_insensitive_locs _) h1 h2 l;
  modifies_address_liveness_insensitive_unused_in cls h1 h2;
  loc_includes_trans (loc_unused_in _ h1) (loc_unused_in _ h2) l'

let fresh_loc (l: loc) (h h' : HS.mem) : GTot Type0 =
  loc_unused_in _ h `loc_includes` l /\
  loc_not_unused_in _ h' `loc_includes` l

let ralloc_post_fresh_loc (#a:Type) (#rel:Preorder.preorder a) (i: HS.rid) (init:a) (m0: HS.mem)
                       (x: HST.mreference a rel{HS.is_eternal_region (HS.frameOf x)}) (m1: HS.mem) : Lemma
    (requires (HST.ralloc_post i init m0 x m1))
    (ensures (fresh_loc (loc_freed_mreference x) m0 m1))
    [SMTPat (HST.ralloc_post i init m0 x m1)]
=  ()

//AR: this is needed for liveness across fresh_frame
let fresh_frame_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.fresh_frame h0 h1))
  (ensures  (modifies #_ #cls loc_none h0 h1))
  [SMTPat (HS.fresh_frame h0 h1)]
= fresh_frame_modifies cls h0 h1

let popped_modifies (h0 h1: HS.mem) : Lemma
  (requires (HS.popped h0 h1))
  (ensures  (modifies #_ #cls (loc_region_only false (HS.get_tip h0)) h0 h1))
  [SMTPat (HS.popped h0 h1)]
= popped_modifies cls h0 h1

let modifies_remove_new_locs (l_fresh l_aux l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (fresh_loc l_fresh h1 h2 /\
                     modifies l_aux h1 h2 /\
		     l_goal `loc_includes` l_aux /\
                     modifies (loc_union l_fresh l_goal) h2 h3))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (fresh_loc l_fresh h1 h2);
	   SMTPat (modifies l_aux h1 h2);
	   SMTPat (modifies l_goal h1 h3)]
= modifies_only_not_unused_in l_goal h1 h3

let modifies_remove_fresh_frame (h1 h2 h3:HS.mem) (l:loc)
  : Lemma (requires (HS.fresh_frame h1 h2 /\
                     modifies (loc_union (loc_all_regions_from false (HS.get_tip h2)) l) h2 h3))
          (ensures  (modifies l h1 h3))
	  [SMTPat (modifies l h1 h3); SMTPat (HS.fresh_frame h1 h2)]
  = loc_regions_unused_in cls h1 (HS.mod_set (Set.singleton (HS.get_tip h2)));
    modifies_only_not_unused_in l h1 h3

(**** Operations on pointers *)

inline_for_extraction noextract let get (#a: Type0) (ptr: pointer a) : HST.Stack a
  (requires (fun h0 -> readable ptr h0 /\ pointer_live ptr h0))
  (ensures (fun h0 x h1 ->
    sel h0 ptr == sel h1 ptr /\ x == (sel h0 ptr).wp_v /\
    pointer_live ptr h1 /\
    modifies #ploc #cls (loc_pointer ptr) h0 h1
  ))
  = let open HST in
  let (v, _) = ! ptr.ptr_v in
  v


let live_same_pointers_equal_types
  (a1: Type0)
  (a2: Type0)
  (ptr1: pointer a1)
  (ptr2: pointer a2)
  (h: HS.mem)
  : Lemma (requires (
     frame_of_pointer ptr1 == frame_of_pointer ptr2 /\
     pointer_as_addr ptr1 == pointer_as_addr ptr2 /\
     pointer_live ptr1 h /\ pointer_live ptr2 h))
   (ensures (a1 == a2 /\ HS.sel h ptr1.ptr_v == HS.sel h ptr2.ptr_v))
  =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ()

inline_for_extraction noextract let upd (#a: Type0) (ptr: pointer a) (x: a) : HST.Stack unit
  (requires (fun h0 -> writeable ptr h0 /\ pointer_live ptr h0))
  (ensures (fun h0 _ h1 ->
     (sel h0 ptr).wp_perm == (sel h1 ptr).wp_perm /\
     (sel h1 ptr).wp_v == x /\
     modifies (loc_pointer ptr) h0 h1
  ))
  =
  (**) let h0 = HST.get () in
  let open HST in
  let (v', perm_map) = !ptr.ptr_v in
  let perm_map'  = Ghost.hide (change_snapshot #a #v' (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) x) in
  ptr.ptr_v := (x, (perm_map' <: Ghost.erased (perms_rec a)));
  (**) let h1 = HST.get () in
  (**) let r = frame_of_pointer ptr in
  (**) let n = pointer_as_addr ptr in
  (**) modifies_aloc_intro
  (**)   #ploc #cls
  (**)   #r
  (**)   #n
  (**)   (aloc_pointer ptr)
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun ploc' ->
  (**)     let ploc = aloc_pointer ptr in
  (**)     assert((Ghost.reveal ploc) =!= (Ghost.reveal ploc'));
  (**)     ploc_preserved_intro #r #n ploc' h0 h1 (fun t' ptr' ->
  (**)       let pid = Ghost.reveal ptr.ptr_pid in
  (**)       let pid' = Ghost.reveal ptr'.ptr_pid in
  (**)       only_one_live_pid_with_full_permission #a #x
  (**)         (Ghost.reveal perm_map')
  (**)         (Ghost.reveal ptr.ptr_pid);
  (**)       assert(get_permission_from_pid (Ghost.reveal perm_map') pid' ==
  (**)         get_permission_from_pid (Ghost.reveal perm_map) pid'
  (**)       );
  (**)       live_same_pointers_equal_types t' a ptr' ptr h0;
  (**)       live_same_pointers_equal_types t' a ptr' ptr h1;
  (**)       assert(sel h0 ptr' == sel h1 ptr');
  (**)       ()
  (**)     )
  (**)   )
  (**) ;
  ()

inline_for_extraction noextract let create (#a: Type) (init :a) : HST.ST (pointer a)
  (requires (fun _ -> True))
  (ensures (fun h0 ptr h1 ->
    ptr.ptr_v `HS.unused_in` h0 /\
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies (loc_none #ploc #cls) h0 h1 /\
    pointer_live ptr h1 /\
    sel h1 ptr == { wp_v = init; wp_perm = 1.0R}
  ))
  =
  let perm_map_pid = Ghost.hide (
    let (vp, pid) = new_value_perms init true in
    ((vp <: perms_rec a), pid)
  ) in
  let ptr_v = HST.ralloc_mm HS.root (init, Ghost.hide (fst (Ghost.reveal perm_map_pid))) in
  { ptr_v = ptr_v; ptr_pid = Ghost.hide (snd (Ghost.reveal perm_map_pid)) }

inline_for_extraction noextract let free (#a: Type) (ptr: pointer a) : HST.ST unit
  (requires (fun h0 -> writeable ptr h0 /\ pointer_live ptr h0))
  (ensures (fun h0 _ h1 ->
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies (loc_pointer ptr) h0 h1 /\
    HS.live_region h1 (frame_of_pointer ptr)
  ))
=
  (**) let h0 = HST.get () in
  (**) let (v, perm_map) = HST.(!ptr.ptr_v) in
  HST.rfree ptr.ptr_v;
  (**) let h1 = HST.get () in
  (**) let r = frame_of_pointer ptr in
  (**) let n = pointer_as_addr ptr in
  (**) modifies_free #(value_with_perms a)
  (**)   #(Heap.trivial_preorder (value_with_perms a))
  (**)   ptr.ptr_v h0
  (**) ;
  (**) assert(modifies (loc_freed_mreference #ploc #cls  ptr.ptr_v) h0 h1);
  (**) modifies_aloc_intro
  (**)   #ploc #cls
  (**)   #r
  (**)   #n
  (**)   (aloc_pointer ptr)
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> begin
            assert(HS.contains h0 b);
            assume(HS.contains h1 b)
  (**)   end)
  (**)   (fun r' n' -> begin
            assume(n `Heap.addr_unused_in` (HS.get_hmap h0 `Map.sel` r))
  (**)   end)
  (**)   (fun ploc' ->
  (**)     let ploc = aloc_pointer ptr in
  (**)     assert((Ghost.reveal ploc) =!= (Ghost.reveal ploc'));
  (**)     ploc_preserved_intro #r #n ploc' h0 h1 (fun t' ptr' ->
  (**)       let pid = Ghost.reveal ptr.ptr_pid in
  (**)       let pid' = Ghost.reveal ptr'.ptr_pid in
  (**)       only_one_live_pid_with_full_permission #a #v
  (**)         (Ghost.reveal perm_map)
  (**)         (Ghost.reveal ptr.ptr_pid);
  (**)       ()
  (**)     )
  (**)   )
  (**) ;
  (**) assert(modifies #ploc #cls (loc_pointer ptr) h0 h1);
  ()

let share (#a: Type) (ptr: pointer a) : HST.Stack (pointer a)
  (requires (fun h0 -> pointer_live ptr h0 /\ readable ptr h0))
  (ensures (fun h0 ptr1 h1 ->
     pointer_live ptr h1 /\ pointer_live ptr1 h1 /\
     mergeable ptr ptr1 /\
     loc_disjoint (loc_pointer ptr) (loc_pointer ptr1) /\
     modifies (loc_pointer ptr) h0 h1 /\
     (sel h1 ptr).wp_v == (sel h0 ptr).wp_v /\ (sel h1 ptr1).wp_v == (sel h0 ptr).wp_v /\
     (sel h1 ptr).wp_perm = half_permission (sel h0 ptr).wp_perm /\
     (sel h1 ptr1).wp_perm = half_permission (sel h0 ptr).wp_perm
  ))
  =
  let open HST in
  (**) let h0 = HST.get () in
  let (v, perm_map) = ! ptr.ptr_v in
  [@inline_let]
  let (new_perm_map_new_pid) = Ghost.hide (
    let (vp, pid) = share_perms #a #v (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) in
    ((vp <: perms_rec a), pid)
  ) in
  ptr.ptr_v := (v, Ghost.hide (fst (Ghost.reveal new_perm_map_new_pid)));
  (**) let h1 = HST.get () in
  let ptr1 = {
    ptr_v = ptr.ptr_v;
    ptr_pid = Ghost.hide (snd (Ghost.reveal new_perm_map_new_pid))
  } in
  (**) modifies_aloc_intro
  (**)   #ploc #cls
  (**)   #(frame_of_pointer ptr)
  (**)   #(pointer_as_addr ptr)
  (**)   (aloc_pointer ptr)
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun ploc' ->
  (**)     let r = frame_of_pointer ptr in
  (**)     let n = pointer_as_addr ptr in
  (**)     let ploc = aloc_pointer ptr in
  (**)     let perm_map' = fst (Ghost.reveal new_perm_map_new_pid) in
  (**)     let pid1 = snd (Ghost.reveal new_perm_map_new_pid) in
  (**)     ploc_preserved_intro #r #n ploc' h0 h1 (fun t' ptr' ->
  (**)       let pid = Ghost.reveal ptr.ptr_pid in
  (**)       let pid' = Ghost.reveal ptr'.ptr_pid in
  (**)       if pid' = pid1 then begin
  (**)         assert(~ (pointer_live ptr' h0))
  (**)       end else ()
  (**)     )
  (**)   )
  (**) ;
  (**) MG.loc_disjoint_aloc_intro #ploc #cls
  (**)   #(frame_of_pointer ptr)
  (**)   #(pointer_as_addr ptr)
  (**)   #(frame_of_pointer ptr1)
  (**)   #(pointer_as_addr ptr1)
  (**)   (aloc_pointer ptr)
  (**)   (aloc_pointer ptr1);
  ptr1

let merge (#a: Type) (ptr ptr1: pointer a) : HST.Stack unit
  (requires (fun h0 ->
    mergeable ptr ptr1 /\
    pointer_live ptr h0 /\ pointer_live ptr1 h0 /\
    summable_permissions (sel h0 ptr).wp_perm (sel h0 ptr1).wp_perm
  ))
  (ensures (fun h0 _ h1 ->
    pointer_live ptr h1 /\
    (sel h1 ptr).wp_perm = sum_permissions (sel h0 ptr).wp_perm (sel h0 ptr1).wp_perm /\
    (sel h1 ptr).wp_v == (sel h0 ptr).wp_v /\
    modifies (loc_pointer ptr `loc_union` loc_pointer ptr1) h0 h1
  ))
  =
  let open HST in
  (**) let h0 = HST.get () in
  let (v, perm_map) = !ptr.ptr_v in
  [@inline_let]
  let new_perm_map = Ghost.hide (
    merge_perms #a #v (Ghost.reveal perm_map) (Ghost.reveal ptr.ptr_pid) (Ghost.reveal ptr1.ptr_pid)
  ) in
  ptr.ptr_v := (v, new_perm_map);
  (**) MG.loc_disjoint_aloc_intro #ploc #cls
  (**)  #(frame_of_pointer ptr)
  (**)  #(pointer_as_addr ptr)
  (**)  #(frame_of_pointer ptr1)
  (**)  #(pointer_as_addr ptr1)
  (**)  (aloc_pointer ptr) (aloc_pointer ptr1);
  (**) let h1 = HST.get () in
  (**) modifies_intro
  (**)   #ploc #cls
  (**)   (loc_pointer ptr `loc_union` loc_pointer ptr1)
  (**)   h0 h1
  (**)   (fun r -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun t pre b -> ())
  (**)   (fun r n -> ())
  (**)   (fun r' n' ploc' ->
  (**)     let r = frame_of_pointer ptr in
  (**)     let n = pointer_as_addr ptr in
  (**)     let orig_ploc = aloc_pointer ptr in
  (**)     let perm_map' = new_perm_map in
  (**)     let pid1 = Ghost.reveal ptr1.ptr_pid in
  (**)       let union = loc_pointer ptr `loc_union` loc_pointer ptr1 in
  (**)     assert(loc_disjoint (loc_of_aloc ploc') union);
  (**)     ploc_preserved_intro #r' #n' ploc' h0 h1 (fun t' ptr' ->
  (**)       let pid = Ghost.reveal ptr.ptr_pid in
  (**)       let pid' = Ghost.reveal ptr'.ptr_pid in
  (**)       loc_includes_union_l (loc_pointer ptr) (loc_pointer ptr1) (loc_pointer ptr);
  (**)       loc_includes_union_l (loc_pointer ptr) (loc_pointer ptr1) (loc_pointer ptr1);
  (**)       loc_disjoint_includes
  (**)         (loc_pointer ptr')
  (**)         union
  (**)         (loc_pointer ptr')
  (**)         (loc_pointer ptr);
  (**)       loc_disjoint_includes
  (**)         (loc_pointer ptr')
  (**)         union
  (**)         (loc_pointer ptr')
  (**)         (loc_pointer ptr1);
  (**)       loc_disjoint_aloc_elim #ploc #cls #r' #n' #r #n ploc' (aloc_pointer ptr);
  (**)       loc_disjoint_aloc_elim #ploc #cls #r' #n' #(frame_of_pointer ptr1) #(pointer_as_addr ptr1) ploc' (aloc_pointer ptr1)
  (**)     )
  (**)   )
  (**) ;
  ()
