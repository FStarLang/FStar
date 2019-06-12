module LowStar.Permissions.References

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module MG = FStar.ModifiesGen

open LowStar.Permissions
open FStar.Real


type value_with_perms (a: Type0) = vp : (a & Ghost.erased (perms_rec a)){
  let (v, p) = vp in
  forall (pid:live_pid (Ghost.reveal p)). get_snapshot_from_pid (Ghost.reveal p) pid == v
}

noeq type pointer (a: Type0) = {
  ptr_v: HST.reference (value_with_perms a);
  ptr_pid: Ghost.erased perm_id
}

let frame_of_pointer (#a: Type0) (ptr: pointer a) : HS.rid =
  HS.frameOf ptr.ptr_v

let pointer_as_addr (#a: Type0) (ptr: pointer a) : GTot nat =
  HS.as_addr ptr.ptr_v


type ploc_ (region: HS.rid) (addr: nat) = {
  ploc_pid: perm_id
}

type ploc (region: HS.rid) (addr: nat) = Ghost.erased (ploc_ region addr)

let ploc_includes (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1).ploc_pid == (Ghost.reveal ploc2).ploc_pid

let ploc_disjoint  (#r: HS.rid) (#a: nat) (ploc1 ploc2: ploc r a) =
  (Ghost.reveal ploc1).ploc_pid =!= (Ghost.reveal ploc2).ploc_pid

let ploc_preserved  (#r: HS.rid) (#a: nat) (ploc: ploc r a) (h0 h1: HS.mem) =
  forall (t: Type0) (ptr: pointer t) .
  let pid = Ghost.reveal ptr.ptr_pid in
  let (_, vp0) = HS.sel h0 ptr.ptr_v in
  let vp0 = Ghost.reveal vp0 in
  let (_, vp1) = HS.sel h1 ptr.ptr_v in
  let vp1 = Ghost.reveal vp1 in
  begin
    (is_live_pid vp0 (Ghost.reveal ploc).ploc_pid /\ HS.contains h0 ptr.ptr_v /\
    HS.frameOf ptr.ptr_v == r /\ HS.as_addr ptr.ptr_v == a /\ (Ghost.reveal ploc).ploc_pid == pid)
    ==> begin
      get_permission_from_pid vp0 pid == get_permission_from_pid vp1 pid /\
      get_snapshot_from_pid vp0 pid == get_snapshot_from_pid vp1 pid /\
      HS.contains h1 ptr.ptr_v
    end
  end

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
  (fun #r #a b h1 h2 f -> admit())

let loc = loc cls

let aloc_pointer (#a: Type0) (ptr: pointer a) : GTot (ploc (frame_of_pointer ptr) (pointer_as_addr ptr)) =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  let pid =  Ghost.reveal ptr.ptr_pid in
  let out = ({
    ploc_pid = pid
  } <:  ploc_ r a) in
  Ghost.hide out

let loc_pointer (#a: Type0) (ptr: pointer a) : GTot loc =
  let r = frame_of_pointer ptr in
  let a = pointer_as_addr ptr in
  loc_of_aloc #ploc #cls
  #r
  #a
  (aloc_pointer ptr)

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
  [SMTPat (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)]
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

(*
let live_loc_not_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (live h b))
         (ensures  (loc_not_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (live h b)]
= live_loc_not

val unused_in_loc_unused_in (#a:Type0) (#rrel #rel:srel a) (b:mbuffer a rrel rel) (h:HS.mem)
  :Lemma (requires (unused_in b h))
         (ensures  (loc_unused_in h `loc_includes` loc_addr_of_buffer b))
         [SMTPat (unused_in b h)]
