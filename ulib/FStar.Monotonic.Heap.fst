module FStar.Monotonic.Heap

open FStar.Preorder
open FStar.Classical
private noeq
type heap_rec = {
  next_addr:(x: nat{x > 0});
  //type, preorder, mm flag, and value
  memory:x: nat{x > 0} -> Tot (option (a: Type0 & rel: (option (preorder a)) & b: bool & a))
}

let heap = h: heap_rec{(forall (n: nat). n >= h.next_addr ==> None? (h.memory n))}

let equal h1 h2 =
  let _ = () in
  h1.next_addr = h2.next_addr /\ FStar.FunctionalExtensionality.feq h1.memory h2.memory

let equal_extensional h1 h2 = ()

let emp = { next_addr = 1; memory = (fun (r: nat) -> None) }
private noeq
type mref' (a: Type0) (rel: preorder a) : Type0 = {
  addr:(x: nat{x > 0});
  init:a;
  mm:bool //manually managed flag
}

let mref a rel = mref' a rel

let addr_of #a #rel r = r.addr

let is_mm #a #rel r = r.mm

let compare_addrs #a #b #rel1 #rel2 r1 r2 = r1.addr = r2.addr

let contains #a #rel h r =
  let _ = () in
  Some? (h.memory r.addr) /\
  (let Some (| a1 , pre_opt , mm , _ |) = h.memory r.addr in
    //using `===` here, since otherwise typechecker fails with a and a1 being different types, why?
    a == a1 /\ Some? pre_opt /\ Some?.v pre_opt == rel /\ mm = r.mm)

let addr_unused_in n h = n <> 0 && None? (h.memory n)

let not_addr_unused_in_nullptr h = ()

let unused_in #a #rel r h = addr_unused_in (addr_of r) h

let sel_tot #a #rel h r =
  let Some (| _ , _ , _ , x |) = h.memory r.addr in
  x

let sel #a #rel h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (contains h r)
  then sel_tot #a h r
  else r.init

let upd_tot' (#a: Type0) (#rel: preorder a) (h: heap) (r: mref a rel) (x: a) =
  {
    h with
    memory = (fun r' -> if r.addr = r' then Some (| a, Some rel, r.mm, x |) else h.memory r')
  }

let upd_tot #a #rel h r x = upd_tot' h r x

let upd #a #rel h r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (contains h r)
  then upd_tot' h r x
  else
    if r.addr >= h.next_addr
    then
      {
        next_addr = r.addr + 1;
        memory = (fun r' -> if r' = r.addr then Some (| a, Some rel, r.mm, x |) else h.memory r')
      }
    else
      {
        h with
        memory = (fun r' -> if r' = r.addr then Some (| a, Some rel, r.mm, x |) else h.memory r')
      }

let alloc #a rel h x mm =
  let r = { addr = h.next_addr; init = x; mm = mm } in
  r,
  {
    next_addr = r.addr + 1;
    memory = (fun r' -> if r' = r.addr then Some (| a, Some rel, r.mm, x |) else h.memory r')
  }

let free_mm #a #rel h r = { h with memory = (fun r' -> if r' = r.addr then None else h.memory r') }

(*
 * update of a well-typed mreference
 *)
private
let lemma_upd_contains_test (#a: Type) (#rel: preorder a) (h0: heap) (r: mref a rel) (x: a)
  : Lemma
  (contains h0 r ==>
    (let h1 = upd h0 r x in
      (forall (b: Type) (rel: preorder b) (r': mref b rel).
          (contains h0 r' /\ addr_of r' = addr_of r) ==>
          sel h1 r' == x /\
          (forall (b: Type) (rel: preorder b) (r': mref b rel).
              addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
          (forall (b: Type) (rel: preorder b) (r': mref b rel). contains h0 r' <==> contains h1 r') /\
          (forall (b: Type) (rel: preorder b) (r': mref b rel). unused_in r' h0 <==> unused_in r' h1
          )))) = ()

(*
 * update of a mreference that is mapped but not necessarily well-typed
 * we cannot prove that h0 `contains` r' ==> h1 `contains` r'
 * because consider that in h0 (r:mref a) contains (| b, y:b |),
 * and that (r':mref b) s.t. r'.addr = r.addr
 * in h0, r' is well-typed, but in h1 it's not
 *)
private
let lemma_upd_contains_not_necessarily_well_typed_test
  (#a: Type) (#rel: preorder a) (h0: heap) (r: mref a rel) (x: a)
  : Lemma
  ((~(unused_in r h0)) ==>
    (let h1 = upd h0 r x in
      contains h1 r /\
      (forall (b: Type) (#rel: preorder b) (r': mref b rel).
          addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
      (forall (b: Type) (#rel: preorder b) (r': mref b rel).
          (r'.addr <> r.addr /\ contains h0 r') ==> contains h1 r') /\
      (forall (b: Type) (#rel: preorder b) (r': mref b rel). unused_in r' h0 <==> unused_in r' h1))) =
  ()

(*
 * update of an unused mreference
 *)
private
let lemma_upd_unused_test (#a: Type) (#rel: preorder a) (h0: heap) (r: mref a rel) (x: a)
  : Lemma
  (unused_in r h0 ==>
    (let h1 = upd h0 r x in
      contains h1 r /\
      (forall (b: Type) (rel: preorder b) (r': mref b rel).
          addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
      (forall (b: Type) (rel: preorder b) (r': mref b rel). contains h0 r' ==> contains h1 r') /\
      (forall (b: Type) (rel: preorder b) (r': mref b rel).
          ~(unused_in r' h0) ==> ~(unused_in r' h1)))) = ()

(*
 * alloc and alloc_mm behaves just like upd of an unmapped mreference
 *)
private
let lemma_alloc_test (#a: Type) (rel: preorder a) (h0: heap) (x: a) (mm: bool)
  : Lemma
  (let r, h1 = alloc rel h0 x mm in
    unused_in r h0 /\ contains h1 r /\ is_mm r = mm /\
    (forall (b: Type) (rel: preorder b) (r': mref b rel).
        addr_of r' <> addr_of r ==> sel h0 r' == sel h1 r') /\
    (forall (b: Type) (rel: preorder b) (r': mref b rel). contains h0 r' ==> contains h1 r') /\
    (forall (b: Type) (rel: preorder b) (r': mref b rel). ~(unused_in r' h0) ==> ~(unused_in r' h1))
  ) = ()
private
let lemma_free_mm_test
  (#a: Type) (rel: preorder a) (h0: heap) (r: mref a rel {contains h0 r /\ is_mm r})
  : Lemma
  (let h1 = free_mm h0 r in
    unused_in r h1 /\
    (forall (b: Type) (rel: preorder b) (r': mref b rel).
        addr_of r' <> addr_of r ==>
        ((sel h0 r' == sel h1 r' /\ (contains h0 r' <==> contains h1 r') /\
            (unused_in r' h0 <==> unused_in r' h1))))) = ()
private
let lemma_alloc_fresh_test (#a: Type) (rel: preorder a) (h0: heap) (x: a) (mm: bool)
  : Lemma
  (let r, h1 = alloc rel h0 x mm in
    fresh r h0 h1 /\ modifies Set.empty h0 h1) = ()

let lemma_ref_unused_iff_addr_unused #a #rel h r = ()
let lemma_contains_implies_used #a #rel h r = ()
let lemma_distinct_addrs_distinct_types #a #b #rel1 #rel2 h r1 r2 = ()
let lemma_distinct_addrs_distinct_preorders u = ()
let lemma_distinct_addrs_distinct_mm u = ()
let lemma_distinct_addrs_unused #a #b #rel1 #rel2 h r1 r2 = ()
let lemma_alloc #a rel h0 x mm =
  let r, h1 = alloc rel h0 x mm in
  let h1' = upd h0 r x in
  assert (equal h1 h1')
let lemma_free_mm_sel #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_contains #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_mm_unused #a #b #rel1 #rel2 h0 r1 r2 = ()
let lemma_free_addr_unused_in #a #rel h r n = ()
let lemma_sel_same_addr #a #rel h r1 r2 = ()
let lemma_sel_upd1 #a #rel h r1 x r2 = ()
let lemma_sel_upd2 #a #b #rel1 #rel2 h r1 r2 x = ()
let lemma_mref_injectivity = ()
let lemma_in_dom_emp #a #rel r = ()
let lemma_upd_contains #a #rel h r x = ()
let lemma_well_typed_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_unused_upd_contains #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_contains_different_addr #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_upd_unused #a #b #rel1 #rel2 h r1 x r2 = ()
let lemma_contains_upd_modifies #a #rel h r x = ()
let lemma_unused_upd_modifies #a #rel h r x = ()

let lemma_sel_equals_sel_tot_for_contained_refs #a #rel h r = ()
let lemma_upd_equals_upd_tot_for_contained_refs #a #rel h r x = ()
let lemma_modifies_and_equal_dom_sel_diff_addr #a #rel s h0 h1 r = ()

let lemma_heap_equality_upd_same_addr #a #rel h r1 r2 x = assert (equal (upd h r1 x) (upd h r2 x))

let lemma_heap_equality_cancel_same_mref_upd #a #rel h r x y =
  let h0 = upd (upd h r x) r y in
  let h1 = upd h r y in
  assert (equal h0 h1)

let lemma_heap_equality_upd_with_sel #a #rel h r =
  let h' = upd h r (sel h r) in
  let Some (| _ , _ , _ , _ |) = h.memory r.addr in
  assert (equal h h')

let lemma_heap_equality_commute_distinct_upds #a #b #rel_a #rel_b h r1 r2 x y =
  let h0 = upd (upd h r1 x) r2 y in
  let h1 = upd (upd h r2 y) r1 x in
  assert (equal h0 h1)

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)
noeq
type aref' : Type0 = {
  a_addr:(x: nat{x > 0});
  a_mm:bool //manually managed flag
}
let aref = aref'
let dummy_aref = { a_addr = 1; a_mm = false }
let aref_equal a1 a2 = a1.a_addr = a2.a_addr && a1.a_mm = a2.a_mm

(* Introduction rule *)
let aref_of #t #rel r = { a_addr = r.addr; a_mm = r.mm }

(* Operators lifted from ref *)
let addr_of_aref a = a.a_addr
let addr_of_aref_of #t #rel r = ()
let aref_is_mm a = a.a_mm
let is_mm_aref_of #t #rel r = ()
let aref_unused_in a h = None? (h.memory a.a_addr)
let unused_in_aref_of #t #rel r h = ()
let contains_aref_unused_in #a #rel h x y = ()

(* Elimination rule *)
let aref_live_at (h: heap) (a: aref) (t: Type0) (rel: preorder t) =
  let _ = () in
  Some? (h.memory a.a_addr) /\
  (let Some (| a1 , pre_opt , mm , _ |) = h.memory a.a_addr in
    //using `===` here, since otherwise typechecker fails with a and a1 being different types, why?
    t == a1 /\ Some? pre_opt /\ Some?.v pre_opt === rel /\ mm == a.a_mm)

let ref_of' (h: heap) (a: aref) (t: Type0) (rel: preorder t)
  : Pure (mref t rel) (requires (aref_live_at h a t rel)) (ensures (fun _ -> True)) =
  let Some (| _ , pre_opt , _ , x |) = h.memory a.a_addr in
  { addr = a.a_addr; init = x; mm = a.a_mm }

let gref_of a t rel =
  let m: squash (exists (h: heap). aref_live_at h a t rel) = () in
  let l: (exists (h: heap). aref_live_at h a t rel) =
    Squash.join_squash #(h: heap & aref_live_at h a t rel) m
  in
  let k: (exists (h: heap{aref_live_at h a t rel}). squash True) =
    FStar.Squash.bind_squash #(h: heap & aref_live_at h a t rel)
      #(h: (h: heap{aref_live_at h a t rel}) & squash True)
      l
      (fun h ->
          let (| h' , _ |) = h in
          Squash.return_squash (| h', () |))
  in
  let h =
    FStar.ErasedLogic.exists_proj1 #(h: heap{aref_live_at h a t rel}) #(fun _ -> squash True) k
  in
  ref_of' h a t rel

let ref_of h a t rel = ref_of' h a t rel

let aref_live_at_aref_of h #t #rel r = ()
let contains_gref_of h a t rel = ()
let aref_of_gref_of a t rel = ()

