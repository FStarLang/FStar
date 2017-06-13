module FStar.Heap

open FStar.Classical
open FStar.Monotonic.Heap

let heap = heap

let emp = emp

let trivial_preorder (a:Type0) = fun _ _ -> True

let ref a = ref a (trivial_preorder a)

let addr_of #a r = addr_of r

let is_mm #a r = is_mm r

let compare_addrs #a #b r1 r2 = compare_addrs r1 r2

let contains #a h r = contains h r

let unused_in #a r h = unused_in r h

let sel_tot #a h r = sel_tot h r

let sel #a h r = sel h r

let upd_tot #a h r x = upd_tot h r x

let upd #a h r x = upd h r x

let alloc #a h x mm = alloc (trivial_preorder a) h x mm

let free_mm #a h r = free_mm h r

(*
 * update of a well-typed reference
 *)
private let lemma_upd_contains_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (h0 `contains` r ==>
          (let h1 = upd h0 r x in
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' <==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0  <==> r' `unused_in` h1)))
  = ()

(*
 * update of a reference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:ref a) contains (| b, y:b |),
 * and that (r':ref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private let lemma_upd_contains_not_necessarily_well_typed_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma ((~ (r `unused_in` h0)) ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r')           /\
	   (forall (b:Type) (r':ref b). (addr_of r' <> addr_of r /\ h0 `contains` r') ==> h1 `contains` r') /\
	   (forall (b:Type) (r':ref b). r' `unused_in` h0 <==> r' `unused_in` h1)))
  = ()

(*
 * update of an unused reference
 *)
private let lemma_upd_unused_test
  (#a:Type) (h0:heap) (r:ref a) (x:a)
  :Lemma (r `unused_in` h0 ==>
          (let h1 = upd h0 r x in
	   h1 `contains` r /\
           (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
	   (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	   (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1))))
  = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped reference
 *)
private let lemma_alloc_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let (r, h1) = alloc h0 x mm in
          r `unused_in` h0 /\
	  h1 `contains` r  /\
          is_mm r = mm     /\
          (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b:Type) (r':ref b). h0 `contains` r' ==> h1 `contains` r')             /\
	  (forall (b:Type) (r':ref b). ~ (r' `unused_in` h0) ==> ~ (r' `unused_in` h1)))
  = ()

private let lemma_free_mm_test (#a:Type) (h0:heap) (r:ref a{h0 `contains` r /\ is_mm r})
  :Lemma (let h1 = free_mm h0 r in
          r `unused_in` h1 /\
	  (forall (b:Type) (r':ref b). addr_of r' <> addr_of r ==>
	                          ((sel h0 r' == sel h1 r'                 /\
				   (h0 `contains` r' <==> h1 `contains` r') /\
				   (r' `unused_in` h0 <==> r' `unused_in` h1)))))
  = ()

private let lemma_alloc_fresh_test (#a:Type) (h0:heap) (x:a) (mm:bool)
  :Lemma (let r, h1 = alloc h0 x mm in
          fresh r h0 h1 /\ modifies Set.empty h0 h1)
  = ()

let lemma_contains_implies_used #a h r = ()
let lemma_distinct_addrs_distinct_types #a #b h r1 r2 = ()
let lemma_distinct_addrs_unused #a #b h r1 r2 = ()
let lemma_alloc #a h0 x mm = ()
let lemma_free_mm_sel #a #b h0 r1 r2 = ()
let lemma_free_mm_contains #a #b h0 r1 r2 = ()
let lemma_free_mm_unused #a #b h0 r1 r2 = ()
let lemma_sel_same_addr #a h r1 r2 = lemma_sel_same_addr h r1 r2  //AR: figure out why this is not fired automatically
let lemma_sel_upd1 #a h r1 x r2 = ()
let lemma_sel_upd2 #a #b h r1 r2 x = ()
let lemma_ref_injectivity = ()
let lemma_in_dom_emp #a r = ()
let lemma_upd_contains #a h r x = ()
let lemma_well_typed_upd_contains #a #b h r1 x r2 = ()
let lemma_unused_upd_contains #a #b h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b h r1 x r2 = ()
let lemma_upd_unused #a #b h r1 x r2 = ()
let lemma_contains_upd_modifies #a h r x = ()
let lemma_unused_upd_modifies #a h r x = ()

let equal h1 h2 = equal h1 h2

let equal_extensional h1 h2 = ()

let upd_upd_same_ref #a h r x y = assert (equal (upd (upd h r x) r y) (upd h r y))
