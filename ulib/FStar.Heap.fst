module FStar.Heap

open FStar.Classical

private noeq type ref_contents (a: Type0): Type0 = {
  c_cur: a;
  c_init: a;
  c_mm: bool;
}

private noeq type heap_rec = {
  next_addr: nat;
  memory   : nat -> Tot (option (a:Type0 & ref_contents a))
}

let heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

let emp = {
  next_addr = 0;
  memory    = (fun (r:nat) -> None)
}

private type ref' (a:Type0) :Type0 = {
  addr: nat;
  init: a;
  mm:   bool;  //manually managed flag
}

let ref a = ref' a

let addr_of #a r = r.addr

let is_mm #a r = r.mm

let compare_addrs #a #b r1 r2 = r1.addr = r2.addr

let contains #a h r =
  let _ = () in
  let maybe_raw_contents = h.memory r.addr in
  Some? maybe_raw_contents /\ (
    let raw_contents = Some?.v maybe_raw_contents in (
      dfst raw_contents == a /\ (
      let contents = dsnd raw_contents in (
        contents.c_init == r.init /\
        contents.c_mm == r.mm
  ))))

let unused_in #a r h = None? (h.memory r.addr)

let sel_tot #a h r =
  let Some (| _, x |) = h.memory r.addr in
  x.c_cur

let sel #a h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r) then
    sel_tot #a h r
  else r.init

let upd_tot #a h r x =
  let x = {
    c_cur = x;
    c_init = r.init;
    c_mm = r.mm;
  }
  in
  { h with memory = (fun r' -> if r.addr = r'
			    then Some (| a, x |)
                            else h.memory r') }

let upd #a h r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains` r)
  then upd_tot h r x
  else
    let x = {
      c_cur = x;
      c_init = r.init;
      c_mm = r.mm;
    }
    in
    if r.addr >= h.next_addr
    then
      { next_addr = r.addr + 1;
        memory    = (fun (r':nat) -> if r' = r.addr
	   		         then Some (| a, x |)
                                 else h.memory r') }
    else
      { h with memory = (fun r' -> if r' = r.addr
				then Some (| a, x |)
                                else h.memory r') }

let alloc #a h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r, upd #a h r x

let free_mm #a h r =
  { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

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
	   (forall (b:Type) (r':ref b). (r'.addr <> r.addr /\ h0 `contains` r') ==> h1 `contains` r') /\
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
let lemma_same_addrs_same_types_same_refs #a h r1 r2 = ()
let lemma_distinct_addrs_unused #a #b h r1 r2 = ()
let lemma_alloc #a h0 x mm = ()
let lemma_free_mm_sel #a #b h0 r1 r2 = ()
let lemma_free_mm_contains #a #b h0 r1 r2 = ()
let lemma_free_mm_unused #a #b h0 r1 r2 = ()
let lemma_sel_same_addr #a h r1 r2 = ()
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

let equal h1 h2 =
  let _ = () in
  h1.next_addr = h2.next_addr /\
  FStar.FunctionalExtensionality.feq h1.memory h2.memory

let equal_extensional h1 h2 = ()

let upd_upd_same_ref #a h r x y = assert (equal (upd (upd h r x) r y) (upd h r y))

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)
noeq type aref' :Type0 = {
  a_addr: nat;
  a_mm:   bool;  //manually managed flag
}
let aref = aref'
let dummy_aref = {
  a_addr = 0;
  a_mm   = false;
}
let aref_equal a1 a2 = a1.a_addr = a2.a_addr && a1.a_mm = a2.a_mm

(* Introduction rule *)
let aref_of #t r = {
  a_addr = r.addr;
  a_mm   = r.mm;
}

(* Operators lifted from ref *)
let addr_of_aref a = a.a_addr
let addr_of_aref_of #t r = ()
let aref_is_mm a = a.a_mm
let is_mm_aref_of #t r = ()
let aref_unused_in a h = None? (h.memory a.a_addr)
let unused_in_aref_of #t r h = ()
let contains_aref_unused_in #a h x y = ()

(* Elimination rule *)
let aref_live_at (h: heap) (a: aref) (t: Type0) =
  let maybe_raw_contents = h.memory a.a_addr in
  Some? maybe_raw_contents /\ (
    let raw_contents = Some?.v maybe_raw_contents in (
      dfst raw_contents == t /\ (
        let contents = dsnd raw_contents in
        contents.c_mm == a.a_mm
  )))

let ref_of'
  (h: heap)
  (a: aref)
  (t: Type0)
: Pure (ref t)
  (requires (aref_live_at h a t))
  (ensures (fun _ -> True))
= let raw_contents = Some?.v (h.memory a.a_addr) in
  let contents: ref_contents t = dsnd raw_contents in
  {
    addr = a.a_addr;
    init = contents.c_init;
    mm = contents.c_mm
  }

let gref_of a t =
  let m : squash (exists (h: heap) . aref_live_at h a t) = () in
  let l : (exists (h: heap) . aref_live_at h a t) =
    Squash.join_squash #(h: heap & aref_live_at h a t) m
  in
  let k : (exists (h: heap { aref_live_at h a t} ) . squash True ) =
    FStar.Squash.bind_squash
      #(h: heap & aref_live_at h a t)
      #(h: (h: heap { aref_live_at h a t} ) & squash True)
      l
      (fun h -> let (| h', _ |) = h in Squash.return_squash (| h', () |) )
  in
  let h = FStar.ErasedLogic.exists_proj1 #(h: heap {aref_live_at h a t}) #(fun _ -> squash True) k in
  ref_of' h a t

let ref_of h a t = ref_of' h a t

let aref_live_at_aref_of h #t r = ()
let contains_gref_of h a t = ()
let aref_of_gref_of a t = ()
let gref_of_aref_of #t r = ()
