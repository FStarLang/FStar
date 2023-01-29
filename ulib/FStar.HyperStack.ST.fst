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
module FStar.HyperStack.ST

open FStar.HyperStack

module W  = FStar.Monotonic.Witnessed
module HS = FStar.HyperStack

open FStar.Preorder

(* Eternal regions remain contained *)
private let eternal_region_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (HS.is_heap_color (color r)); (m1 `contains_region` r)}
                 (HS.is_eternal_region_hs r /\ m1 `contains_region` r) ==> m2 `contains_region` r

(* rid counter increases monotonically *)
private let rid_ctr_pred (m1 m2:mem) :Type0 = get_rid_ctr m1 <= get_rid_ctr m2

(*
 * A region r, that is:
 * (a) not contained in m1, and
 * (b) has rid last component less than m1.rid_ctr
 * 
 * remains not contained in m2
 *)
private let rid_last_component_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (m1 `contains_region` r)}
                 ((~ (m1 `contains_region` r)) /\ rid_last_component r < get_rid_ctr m1) ==>
		 (~ (m2 `contains_region` r))

(* Predicate for eternal refs *)
private let eternal_refs_pred (m1 m2:mem) :Type0
  = forall (a:Type) (rel:preorder a) (r:HS.mreference a rel).
      {:pattern (m1 `HS.contains` r)}
      (is_mm r) \/
      (((m1 `HS.contains` r) /\
        (HS.is_eternal_region_hs (frameOf r) \/
         m2 `contains_region` (HS.frameOf r))) ==> (m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r)))
       
(*
 * Predicate for next ref address in a region's heap
 * For all regions, their next_addr increases monotonically (or the region ceases to exist)
 *)
private let next_ref_addr_in_a_region_pred (m1 m2:mem) :Type0
  = forall (r:HS.rid).{:pattern (m1 `contains_region` r)}
                 (m1 `contains_region` r) ==> 
		 (if m2 `contains_region` r then
		    let h1 = Map.sel (HS.get_hmap m1) r in
		    let h2 = Map.sel (HS.get_hmap m2) r in
		    Heap.next_addr h1 <= Heap.next_addr h2
		  else True)

(* Predicate that an unused ref whose addr is less than the next addr remains unused *)
private let unused_ref_next_addr_pred (m1 m2:mem) :Type0
  = forall (rid:HS.rid).{:pattern (m1 `contains_region` rid)}
                   (m1 `contains_region` rid) ==>
		   (let h1 = Map.sel (HS.get_hmap m1) rid in
		    (forall (a:Type0) (rel:preorder a) (r:HS.mreference a rel).{:pattern (r `HS.unused_in` m1)}
		       (HS.frameOf r == rid /\ r `HS.unused_in` m1 /\ HS.as_addr r < Heap.next_addr h1) ==>
		       (r `HS.unused_in` m2)))

(* Predicate for mm refs *)
private let mm_refs_pred (m1 m2:mem) :Type0
  = forall (a:Type) (rel:preorder a) (r:HS.mreference a rel).{:pattern (m1 `HS.contains` r)}
      (not (is_mm r)) \/
      (m1 `HS.contains` r ==>
       (m2 `HS.contains` r /\ rel (HS.sel m1 r) (HS.sel m2 r) \/
        r `HS.unused_in` m2))

(* The preorder is the conjunction of above predicates *)
let mem_rel :preorder mem
  = HS.lemma_rid_ctr_pred (); HS.lemma_next_addr_contained_refs_addr ();  
    fun (m1 m2:mem) ->
    eternal_region_pred m1 m2 /\ rid_ctr_pred m1 m2 /\ rid_last_component_pred m1 m2 /\ eternal_refs_pred m1 m2 /\
    next_ref_addr_in_a_region_pred m1 m2 /\ unused_ref_next_addr_pred m1 m2 /\ mm_refs_pred m1 m2

(* Predicates that we will witness with regions and refs *)
let region_contains_pred r =
  fun m -> (not (HS.is_eternal_region_hs r)) \/ m `contains_region` r

let ref_contains_pred #_ #_ r =
  fun m ->
  let rid = HS.frameOf r in
  rid_last_component rid < get_rid_ctr m /\
  (m `contains_region` rid ==> (
   (HS.as_addr r < Heap.next_addr (Map.sel (HS.get_hmap m) rid)) /\
   (HS.is_mm r ==> (m `HS.contains` r \/ r `HS.unused_in` m)) /\
   ((not (HS.is_mm r)) ==> m `HS.contains` r)))

let stable p = forall (h1:mem) (h2:mem).{:pattern (mem_rel h1 h2)} (p h1 /\ mem_rel h1 h2) ==> p h2

let witnessed p = W.witnessed mem_rel p

(* TODO: we should derive these using DM4F *)
let gst_get _ = admit ()
let gst_put _ = admit ()

let gst_witness _ = admit ()
let gst_recall _ = admit ()

let lemma_functoriality p q = W.lemma_witnessed_weakening mem_rel p q

let same_refs_in_all_regions m0 m1 = same_refs_common contained_region m0 m1
let same_refs_in_stack_regions m0 m1 = same_refs_common contained_stack_region m0 m1
let same_refs_in_non_tip_regions m0 m1 = same_refs_common contained_non_tip_region m0 m1
let same_refs_in_non_tip_stack_regions m0 m1 = same_refs_common contained_non_tip_stack_region m0 m1

let lemma_same_refs_in_all_regions_intro _ _ = ()
let lemma_same_refs_in_all_regions_elim _ _ _ = ()
let lemma_same_refs_in_stack_regions_intro _ _ = ()
let lemma_same_refs_in_stack_regions_elim _ _ _ = ()
let lemma_same_refs_in_non_tip_regions_intro _ _ = ()
let lemma_same_refs_in_non_tip_regions_elim _ _ _ = ()
let lemma_same_refs_in_non_tip_stack_regions_intro _ _ = ()
let lemma_same_refs_in_non_tip_stack_regions_elim _ _ _ = ()
let lemma_equal_domains_trans _ _ _ = ()

let push_frame _ =
  let m0 = gst_get () in
  let m1 = HS.hs_push_frame m0 in
  gst_put m1

let pop_frame _ =
  let m1 = pop (gst_get ()) in
  gst_put m1

private let salloc_common (#a:Type) (#rel:preorder a) (init:a) (mm:bool)
  :StackInline (mreference a rel)
  (requires (fun m       -> is_stack_region (get_tip m)))
  (ensures  (fun m0 s m1 -> is_stack_region (HS.frameOf s) /\ salloc_post init m0 s m1 /\ is_mm s == mm))
  = let m0 = gst_get () in
    let r, m1 = HS.alloc rel (get_tip m0) init mm m0 in
    Heap.lemma_next_addr_alloc rel (Map.sel (get_hmap m0) (get_tip m0)) init mm;  //AR: to prove that next_addr in tip's heap increases (it is part of mem_rel)
    gst_put m1;
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    HS.lemma_rid_ctr_pred ();  //AR: to prove that rid_last_component of r.id is < rid_ctr
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred (HS.frameOf r));
    r

let salloc #_ #_ init = salloc_common init false
let salloc_mm #_ #_ init = salloc_common init true

let sfree #_ #_ r =
  let m0 = gst_get () in
  let m1 = HS.free r m0 in
  assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  Heap.lemma_next_addr_free_mm (Map.sel (HS.get_hmap m0) (HS.get_tip m0)) (HS.as_ref r);  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
  gst_put m1

let new_region r0 =
  if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
  HS.lemma_rid_ctr_pred ();
  let m0 = gst_get () in
  let new_rid, m1 = HS.new_eternal_region m0 r0 None in
  gst_put m1;
  gst_witness (region_contains_pred new_rid);
  new_rid

let new_colored_region r0 c =
  if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
  HS.lemma_rid_ctr_pred ();
  let m0 = gst_get () in
  let new_rid, m1 = HS.new_eternal_region m0 r0 (Some c) in
  gst_put m1;
  gst_witness (region_contains_pred new_rid);
  new_rid

private let ralloc_common (#a:Type) (#rel:preorder a) (i:rid) (init:a) (mm:bool)
  :ST (mreference a rel)
      (requires (fun m       -> is_heap_color (color i) /\ m `contains_region` i))
      (ensures  (fun m0 r m1 -> ralloc_post i init m0 r m1 /\ is_mm r == mm))
  = let m0 = gst_get () in
    let r, m1 = HS.alloc rel i init mm m0 in
    Heap.lemma_next_addr_alloc rel (Map.sel (HS.get_hmap m0) i) init mm;  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
    gst_put m1;
    assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
    HS.lemma_rid_ctr_pred ();
    gst_witness (ref_contains_pred r);
    gst_witness (region_contains_pred i);
    r

let ralloc #_ #_ i init =
  if i <> HS.root then gst_recall (region_contains_pred i);
  ralloc_common i init false
  
let ralloc_mm #_ #_ i init =
  if i <> HS.root then gst_recall (region_contains_pred i);
  ralloc_common i init true

let rfree #_ #_ r =
  let m0 = gst_get () in
  gst_recall (region_contains_pred (HS.frameOf r));
  gst_recall (ref_contains_pred r);
  HS.lemma_rid_ctr_pred ();
  let m1 = HS.free r m0 in
  assert (Set.equal (Map.domain (get_hmap m0)) (Map.domain (get_hmap m1)));
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();    
  Heap.lemma_next_addr_free_mm (Map.sel (HS.get_hmap m0) (HS.frameOf r)) (HS.as_ref r);  //AR: to prove that next_addr in tip's heap remains same (to satisfy the predicate in mm rel)
  gst_put m1

let op_Colon_Equals #_ #_ r v =
  let m0 = gst_get () in
  gst_recall (region_contains_pred (HS.frameOf r));
  gst_recall (ref_contains_pred r);
  let m1 = HS.upd_tot m0 r v in
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  Heap.lemma_upd_equals_upd_tot_for_contained_refs (get_hmap m0 `Map.sel` (HS.frameOf r)) (HS.as_ref r) v;
  Heap.lemma_next_addr_upd (Map.sel (HS.get_hmap m0) (HS.frameOf r)) (HS.as_ref r) v;  //next_addr in ref's rid heap remains same
  gst_put m1

let op_Bang #_ #_ r =
  let m0 = gst_get () in
  gst_recall (region_contains_pred (HS.frameOf r));
  gst_recall (ref_contains_pred r);
  Heap.lemma_sel_equals_sel_tot_for_contained_refs (get_hmap m0 `Map.sel` (HS.frameOf r)) (HS.as_ref r);
  HS.sel_tot m0 r

let get _ = gst_get ()

let recall #_ #_ r =
  gst_recall (ref_contains_pred r);
  gst_recall (region_contains_pred (HS.frameOf r))

let recall_region i = if i <> HS.root then gst_recall (region_contains_pred i)
let witness_region i = gst_witness (region_contains_pred i)

let witness_hsref #_ #_ r =
  HS.lemma_rid_ctr_pred ();
  HS.lemma_next_addr_contained_refs_addr ();
  gst_witness (ref_contains_pred r)

let mr_witness #r #_ #_ m p =
  recall m;
  let p_pred (#i:erid) (#a:Type) (#b:preorder a)
             (r:m_rref i a b) (p:mem_predicate)
    :mem_predicate
    = fun m -> m `contains` r /\ p m
  in
  gst_witness (p_pred m p);
  lemma_functoriality (p_pred m p) p

let weaken_witness p q =
  let aux () :Lemma (requires ((forall h. p h ==> q h) /\ witnessed p)) (ensures (witnessed q))
    = lemma_functoriality p q
  in
  FStar.Classical.move_requires aux ()

let testify (p:mem_predicate) = gst_recall p

let testify_forall #c #p $s =
  W.lemma_witnessed_forall mem_rel p;
  gst_recall (fun h -> forall (x:c). p x h)

let testify_forall_region_contains_pred #c #p $s =
  let p' (x:c) :mem_predicate = region_contains_pred (p x) in
  let s:squash (forall (x:c). witnessed (p' x)) = () in
  testify_forall s

private let mem_rel_predicate (#a:Type0) (#rel:preorder a) (r:mreference a rel) (p:mem_predicate)
  :mem_predicate
  = let rid = HS.frameOf r in
    fun m ->
    (HS.rid_last_component rid < HS.get_rid_ctr m) /\ (  //will help us prove that a deallocated region remains deallocated
      (m `HS.contains` r /\ p m) \/  //the ref is contained and satisfies p
      (m `contains_region` rid /\ ~ (m `HS.contains_ref_in_its_region` r) /\ HS.as_addr r < Heap.next_addr (HS.get_hmap m `Map.sel` rid) /\ r `HS.unused_in` m) \/  //the ref is deallocated, but its region is contained and next_addr > addr_of ref
      (not (m `contains_region` rid)))  //the region itself is not there

let token_p #_ #_ r p = witnessed (mem_rel_predicate r p)

let witness_p #_ #_ r p =
  gst_recall (ref_contains_pred r);
  gst_recall (region_contains_pred (HS.frameOf r));
  HS.lemma_next_addr_contained_refs_addr ();
  gst_witness (mem_rel_predicate r p)

let recall_p #_ #_ r p =
  gst_recall (ref_contains_pred r);
  gst_recall (region_contains_pred (HS.frameOf r));
  gst_recall (mem_rel_predicate r p)

let token_functoriality #_ #_ r p q =
  lemma_functoriality (mem_rel_predicate r p) (mem_rel_predicate r q)

let lemma_witnessed_constant p = W.lemma_witnessed_constant mem_rel p

let lemma_witnessed_nested p =
  assert_norm (witnessed (fun (m:mem) -> witnessed p) ==
               W.witnessed mem_rel (fun (m:mem) -> W.witnessed mem_rel p));
  assert_norm (witnessed p == W.witnessed mem_rel p);
  W.lemma_witnessed_nested mem_rel p
let lemma_witnessed_and p q = W.lemma_witnessed_and mem_rel p q
let lemma_witnessed_or p q = W.lemma_witnessed_or mem_rel p q
let lemma_witnessed_impl p q = W.lemma_witnessed_impl mem_rel p q
let lemma_witnessed_forall #_ p = W.lemma_witnessed_forall mem_rel p
let lemma_witnessed_exists #_ p = W.lemma_witnessed_exists mem_rel p


let drgn = d_hrid
let rid_of_drgn d = d

let new_drgn r0 =
  if r0 <> HS.root then gst_recall (region_contains_pred r0);  //recall containment of r0
  HS.lemma_rid_ctr_pred ();
  let m0 = gst_get () in
  let new_rid, m1 = HS.new_freeable_heap_region m0 r0 in
  gst_put m1;
  gst_witness (region_contains_pred new_rid);
  new_rid

let free_drgn d =
  let m0 = gst_get () in
  let m1 = HS.free_heap_region m0 d in
  gst_put m1

let ralloc_drgn #_ #_ d init = ralloc_common (rid_of_drgn d) init false
let ralloc_drgn_mm #_ #_ d init = ralloc_common (rid_of_drgn d) init true
