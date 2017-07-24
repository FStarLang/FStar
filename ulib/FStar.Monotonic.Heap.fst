module FStar.Monotonic.Heap

open FStar.Preorder
open FStar.DataInvariant
open FStar.Classical

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & rel:(option (preorder a)) & inv:(data_inv a) & a))
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

let equal h1 h2 =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

let equal_extensional h1 h2 = ()

let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

private type mref' (a:Type0) (inv : data_inv a) (rel:preorder a) :Type0 = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}

let mref (a:Type0) (inv:data_inv a) (rel:preorder a) : Type0 = mref' a inv rel

let addr_of #a #inv #rel r = r.addr

let is_mm #a #inv #rel r = r.mm

let compare_addrs #a #b #inv1 #inv2 #rel1 #rel2 r1 r2 = r1.addr = r2.addr

let contains #a #inv #rel h r =
  let _ = () in
  Some? (h.memory r.addr) /\
  (let Some (| a1, pre_opt, _, _ |) = h.memory r.addr in
   a == a1 /\ Some? pre_opt /\ Some?.v pre_opt === rel)  //using `===` here, since otherwise typechecker fails with a and a1 being different types, why?

let addr_unused_in n h = None? (h.memory n)

let unused_in #a #inv #rel r h = addr_unused_in (addr_of r) h

let sel_tot #a #inv #rel h r =
  let Some (| _, _, _, x |) = h.memory r.addr in x

let sel #a #inv #rel h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
    sel_tot #a h r
  else r.init

let upd_tot #a #inv #rel h r x =
  { h with memory = (fun r' -> if r.addr = r'
			    then Some (| a, Some rel, inv, x |)
                            else h.memory r') }

let upd #a #inv #rel h r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
  then upd_tot h r x
  else
    if r.addr >= h.next_addr
    then
      { next_addr = r.addr + 1;
        memory    = (fun (r':nat) -> if r' = r.addr
	   		         then Some (| a, Some rel, inv, x |)
                                 else h.memory r') }
    else
      { h with memory = (fun r' -> if r' = r.addr
				then Some (| a, Some rel, inv, x |)
                                else h.memory r') }

let alloc #a inv rel h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r, { next_addr = r.addr + 1;
       memory    = (fun (r':nat) -> if r' = r.addr
	   		        then Some (| a, Some rel, inv, x |)
                                else h.memory r') }

let free_mm #a #inv #rel h r =
  { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

(*
 * update of a well-typed mreference
 *)
private let lemma_upd_contains_test
  (#a:Type) (#inv:data_inv a) (#rel:preorder a) (h0:heap) (r:mref a inv rel) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
	   (forall (b:Type) (inv:data_inv b)(rel:preorder b) (r':mref b inv rel). (h0 `contains` r' /\ addr_of r' = addr_of r) ==> sel h1 r' == x /\
           (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')             /\
	   (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). h0 `contains` r' <==> h1 `contains` r')                         /\
	   (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). r' `unused_in` h0  <==> r' `unused_in` h1))))
  = ()

(*
 * update of a mreference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:mref a) contains (| b, y:b |),
 * and that (r':mref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (#inv:data_inv a) (#rel:preorder a) (h0:heap) (r:mref a inv rel) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (#inv:data_inv b) (#rel:preorder b) (r':mref b inv rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (#inv:data_inv b) (#rel:preorder b) (r':mref b inv rel). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (#inv:data_inv b) (#rel:preorder b) (r':mref b inv rel). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused mreference
 *)
private let lemma_upd_unused_test
  (#a:Type) (#inv:data_inv a) (#rel:preorder a) (h0:heap) (r:mref a inv rel) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped mreference
 *)
private let lemma_alloc_test (#a:Type) (inv:data_inv a) (rel:preorder a) (h0:heap) (x:a) (mm:bool)
  :Lemma (let (r, h1) = alloc inv rel h0 x mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_free_mm_test (#a:Type) (inv:data_inv a) (rel:preorder a) (h0:heap) (r:mref a inv rel{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          r `unused_in` h1 /\
	  (forall (b:Type) (inv:data_inv b) (rel:preorder b) (r':mref b inv rel). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' <==> h1 `contains` r') /\
				   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (inv:data_inv a) (rel:preorder a) (h0:heap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc inv rel h0 x mm in
          fresh r h0 h1 /\ modifies Set.empty h0 h1)
  = ()

let lemma_ref_unused_iff_addr_unused #a #inv #rel h r = ()
let lemma_contains_implies_used #a #inv #rel h r = ()
let lemma_distinct_addrs_distinct_types #a #b #inv1 #inv2 #rel1 #rel2 h r1 r2 = ()
let lemma_distinct_addrs_distinct_preorders #a #inv1 #inv2 #rel1 #rel2 h r1 r2 = ()
let lemma_distinct_addrs_unused #a #b #inv1 #inv2 #rel1 #rel2 h r1 r2 = ()
let lemma_alloc #a inv rel h0 x mm =
  let r, h1 = alloc inv rel h0 x mm in
  let h1' = upd h0 r x in
  assert (equal h1 h1')
let lemma_free_mm_sel #a #b #inv1 #inv2 #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_contains #a #b #inv1 #inv2 #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_unused #a #b #inv1 #inv2 #rel1 #rel2 h0 r1 r2 = ()
let lemma_sel_same_addr #a #inv #rel h r1 r2 = ()
let lemma_sel_upd1 #a #inv #rel h r1 x r2 = ()
let lemma_sel_upd2 #a #b #inv1 #inv2 #rel1 #rel2 h r1 r2 x = ()
let lemma_mref_injectivity = ()
let lemma_in_dom_emp #a #inv #rel r = ()
let lemma_upd_contains #a #inv #rel h r x = ()
let lemma_well_typed_upd_contains #a #b #inv1 #inv2 #rel1 #rel2 h r1 x r2 = ()
let lemma_unused_upd_contains #a #b #inv1 #inv2 #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b #inv1 #inv2 #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_unused #a #b #inv1 #inv2 #rel1 #rel2 h r1 x r2 = ()
let lemma_contains_upd_modifies #a #inv #rel h r x = ()
let lemma_unused_upd_modifies #a #inv #rel h r x = ()

let upd_upd_same_mref #a #inv #rel h r x y = assert (equal (upd (upd h r x) r y) (upd h r y))
let lemma_sel_equals_sel_tot_for_contained_refs #a #inv #rel h r = ()
let lemma_upd_equals_upd_tot_for_contained_refs #a #inv #rel h r x = ()
