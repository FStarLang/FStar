(*
   Copyright 2008-2014 Aseem Rastogi, and Microsoft Research

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
module FStar.Monotonic.HyperStack

open FStar.Preorder
module Map = FStar.Map

include FStar.Monotonic.HyperHeap


(****** Some predicates ******)

unfold let is_in (r:rid) (h:hmap) = h `Map.contains` r

let is_stack_region r = color r > 0
let is_heap_color c = c <= 0

[@@(deprecated "FStar.HyperStack.ST.is_eternal_region")]
let is_eternal_region r  = is_heap_color (color r) && not (rid_freeable r)

unfold let is_eternal_region_hs r = is_heap_color (color r) && not (rid_freeable r)

type sid = r:rid{is_stack_region r} //stack region ids

(*
 * AR: marking these unfolds, else I think there are pattern firing issues depending on which one we use
 *)
unfold let is_above r1 r2          = r1 `includes` r2
unfold let is_just_below r1 r2     = r1 `extends`  r2
unfold let is_below r1 r2          = r2 `is_above` r1
let is_strictly_below r1 r2 = r1 `is_below` r2 && r1 <> r2
let is_strictly_above r1 r2 = r1 `is_above` r2 && r1 <> r2


[@@"opaque_to_smt"]
unfold private let map_invariant_predicate (m:hmap) :Type0 =
  forall r. Map.contains m r ==>
      (forall s. includes s r ==> Map.contains m s)

[@@"opaque_to_smt"]
unfold private let downward_closed_predicate (h:hmap) :Type0 =
  forall (r:rid). r `is_in` h  //for any region in the memory
        ==> (r=root    //either is the root
            \/ (forall (s:rid). (r `is_above` s  //or, any region beneath it
                           /\ s `is_in` h)   //that is also in the memory
                     ==> ((is_stack_region r = is_stack_region s) /\  //must be of the same flavor as itself
                          ((is_heap_color (color r) /\ rid_freeable r) ==> s == r)))) //and if r is a freeable heap region, s can only be r (no regions strictly below r)

[@@"opaque_to_smt"]
unfold private let tip_top_predicate (tip:rid) (h:hmap) :Type0 =
  forall (r:sid). r `is_in` h <==> r `is_above` tip

[@@"opaque_to_smt"]
unfold private let rid_ctr_pred_predicate (h:hmap) (n:int) :Type0 =
  forall (r:rid). h `Map.contains` r ==> rid_last_component r < n


(****** Mem definition ******)

[@@ remove_unused_type_parameters [0]]
val map_invariant (m:hmap) :Type0  //all regions above a contained region are contained
[@@ remove_unused_type_parameters [0]]
val downward_closed (h:hmap) :Type0  //regions below a non-root region are of the same color
[@@ remove_unused_type_parameters [0;1]]
val tip_top (tip:rid) (h:hmap) :Type0  //all contained stack regions are above tip
[@@ remove_unused_type_parameters [0;1]]
val rid_ctr_pred (h:hmap) (n:int) :Type0  //all live regions have last component less than the rid_ctr

let is_tip (tip:rid) (h:hmap) =
  (is_stack_region tip \/ tip = root) /\  //the tip is a stack region, or the root
  tip `is_in` h                      /\   //the tip is live
  tip_top tip h                          //any other sid activation is a above (or equal to) the tip

let is_wf_with_ctr_and_tip (h:hmap) (ctr:int) (tip:rid)
  = (not (rid_freeable root)) /\
    root `is_in` h /\
    tip `is_tip` h /\
    map_invariant h /\
    downward_closed h /\
    rid_ctr_pred h ctr

private val mem' :Type u#1

private val mk_mem (rid_ctr:int) (h:hmap) (tip:rid) :mem'

val get_hmap (m:mem') :hmap
val get_rid_ctr (m:mem') :int
val get_tip (m:mem') :rid

private val lemma_mk_mem'_projectors (rid_ctr:int) (h:hmap) (tip:rid)
  :Lemma (requires True)
         (ensures  (let m = mk_mem rid_ctr h tip in
	            (get_hmap m == h /\ get_rid_ctr m == rid_ctr /\ get_tip m == tip)))
         [SMTPatOr [[SMTPat (get_hmap (mk_mem rid_ctr h tip))];
	            [SMTPat (get_rid_ctr (mk_mem rid_ctr h tip))];
		    [SMTPat (get_tip (mk_mem rid_ctr h tip))]
		    ]]

type mem :Type = m:mem'{is_wf_with_ctr_and_tip (get_hmap m) (get_rid_ctr m) (get_tip m) }


(****** Lemmas about mem and predicates ******)

private val lemma_mem_projectors_are_in_wf_relation (m:mem)
  :Lemma (is_wf_with_ctr_and_tip (get_hmap m) (get_rid_ctr m) (get_tip m))

private val lemma_is_wf_ctr_and_tip_intro (h:hmap) (ctr:int) (tip:rid)
  :Lemma (requires (root `is_in` h /\ (is_stack_region tip \/ tip = root) /\  tip `is_in` h /\
                    tip_top_predicate tip h /\ map_invariant_predicate h /\
                    downward_closed_predicate h /\ rid_ctr_pred_predicate h ctr))
	 (ensures  (is_wf_with_ctr_and_tip h ctr tip))

private val lemma_is_wf_ctr_and_tip_elim (m:mem)
  :Lemma (let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
          (root `is_in` h /\ (is_stack_region tip \/ tip = root) /\  tip `is_in` h /\
	   tip_top_predicate tip h /\ map_invariant_predicate h /\
           downward_closed_predicate h /\ rid_ctr_pred_predicate h rid_ctr))

(******* map_invariant related lemmas ******)

val lemma_map_invariant (m:mem) (r s:rid)
  :Lemma (requires (r `is_in` get_hmap m /\ s `is_above` r))
         (ensures  (s `is_in` get_hmap m))
         [SMTPat (r `is_in` get_hmap m); SMTPat (s `is_above` r); SMTPat (s `is_in` get_hmap m)]

(****** downward_closed related lemmas *******)

val lemma_downward_closed (m:mem) (r:rid) (s:rid{s =!= root})
  :Lemma (requires (r `is_in` get_hmap m /\ s `is_above` r))
         (ensures  (is_heap_color (color r) == is_heap_color (color s) /\
	            is_stack_region r == is_stack_region s))
         [SMTPatOr [[SMTPat (get_hmap m `Map.contains` r); SMTPat (s `is_above` r); SMTPat (is_heap_color (color s))];
                    [SMTPat (get_hmap m `Map.contains` r); SMTPat (s `is_above` r); SMTPat (is_stack_region s)]
                    ]]

(****** tip_top related lemmas ******)

val lemma_tip_top (m:mem) (r:sid)
  :Lemma (r `is_in` get_hmap m <==> r `is_above` get_tip m)

(*
 * Pointer uses lemma_tip_top by calling it explicitly with Classical.forall_intro2
 * Classical.forall_intro2 does not work well with SMTPat
 * So adding this smt form of the same lemma
 *)
val lemma_tip_top_smt (m:mem) (r:rid)
  :Lemma (requires (is_stack_region r))
         (ensures  (r `is_in` get_hmap m <==> r `is_above` get_tip m))
         [SMTPatOr [[SMTPat (is_stack_region r); SMTPat (r `is_above` get_tip m)];
                    [SMTPat (is_stack_region r); SMTPat (r `is_in` get_hmap m)]]]

(****** rid_ctr_pred related lemmas ******)

val lemma_rid_ctr_pred (_:unit)
  :Lemma (forall (m:mem) (r:rid).{:pattern (get_hmap m `Map.contains` r)} get_hmap m `Map.contains` r ==> rid_last_component r < get_rid_ctr m)

(*****)

(****** Operations on mem ******)


let empty_mem : mem =
  let empty_map = Map.restrict Set.empty (Map.const Heap.emp) in
  let h = Map.upd empty_map root Heap.emp in
  let tip = root in
  root_last_component ();
  lemma_is_wf_ctr_and_tip_intro h 1 tip;
  mk_mem 1 h tip

let heap_region_does_not_overlap_with_tip
  (m:mem) (r:rid{is_heap_color (color r) /\ not (disjoint r (get_tip m)) /\ r =!= root /\ is_stack_region (get_tip m)})
  : Lemma (requires True)
          (ensures (~ (r `is_in` get_hmap m)))
  = root_has_color_zero()

let poppable (m:mem) = get_tip m =!= root

private let remove_elt (#a:eqtype) (s:Set.set a) (x:a) = Set.intersect s (Set.complement (Set.singleton x))

let popped (m0 m1:mem) =
  poppable m0 /\
  (let h0, tip0, h1, tip1 = get_hmap m0, get_tip m0, get_hmap m1, get_tip m1 in
   (parent tip0 = tip1 /\
    Set.equal (Map.domain h1) (remove_elt (Map.domain h0) tip0) /\
    Map.equal h1 (Map.restrict (Map.domain h1) h0)))

let pop (m0:mem{poppable m0}) :mem =
  let h0, tip0, rid_ctr0 = get_hmap m0, get_tip m0, get_rid_ctr m0 in
  root_has_color_zero();
  lemma_is_wf_ctr_and_tip_elim m0;
  let dom = remove_elt (Map.domain h0) tip0 in
  let h1 = Map.restrict dom h0 in
  let tip1 = parent tip0 in
  lemma_is_wf_ctr_and_tip_intro h1 rid_ctr0 tip1;
  mk_mem rid_ctr0 h1 tip1

//A (reference a) may reside in the stack or heap, and may be manually managed
//Mark it private so that clients can't use its projectors etc.
//enabling extraction of mreference to just a reference in ML and pointer in C
//note that this not enforcing any abstraction
(*
 * AR: 12/26: Defining it using Heap.mref directly, removing the HyperHeap.mref indirection
 *)
private noeq
type mreference' (a:Type) (rel:preorder a) =
  | MkRef : frame:rid -> ref:Heap.mref a rel -> mreference' a rel

let mreference a rel = mreference' a rel

//TODO: rename to frame_of, avoiding the inconsistent use of camelCase
let frameOf (#a:Type) (#rel:preorder a) (r:mreference a rel) :rid
  = r.frame

let mk_mreference (#a:Type) (#rel:preorder a) (id:rid)
                  (r:Heap.mref a rel)
  :mreference a rel
  = MkRef id r

//Hopefully we can get rid of this one
val as_ref (#a:Type0) (#rel:preorder a) (x:mreference a rel)
  :Heap.mref a rel

//And make this one abstract
let as_addr #a #rel (x:mreference a rel)
  :GTot pos
  = Heap.addr_of (as_ref x)

val lemma_as_ref_inj (#a:Type) (#rel:preorder a) (r:mreference a rel)
  :Lemma (requires True) (ensures (mk_mreference (frameOf r) (as_ref r) == r))
         [SMTPat (as_ref r)]

let is_mm (#a:Type) (#rel:preorder a) (r:mreference a rel) :GTot bool =
  Heap.is_mm (as_ref r)

// Warning: all of the type aliases below get special support for KaRaMeL
// extraction. If you rename or add to this list,
// src/extraction/FStar.Extraction.Karamel.fs needs to be updated.

//adding (not s.mm) to stackref and ref so as to keep their semantics as is
let mstackref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_stack_region (frameOf s)  && not (is_mm s) }

let mref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_eternal_region_hs (frameOf s) && not (is_mm s) }

let mmmstackref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_stack_region (frameOf s) && is_mm s }

let mmmref (a:Type) (rel:preorder a) =
  s:mreference a rel{ is_eternal_region_hs (frameOf s) && is_mm s }

//NS: Why do we need this one?
let s_mref (i:rid) (a:Type) (rel:preorder a) = s:mreference a rel{frameOf s = i}

(*
 * AR: this used to be (is_eternal_region i \/ i `is_above` m.tip) /\ Map.contains ...
 *     As far as the memory model is concerned, this should just be Map.contains
 *     The fact that an eternal region is always contained (because of monotonicity) should be used in the ST interface
 *)
let live_region (m:mem) (i:rid) :bool = get_hmap m `Map.contains` i

let contains (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel) =
  live_region m (frameOf s) /\
  Heap.contains (get_hmap m `Map.sel` (frameOf s)) (as_ref s)

let unused_in (#a:Type) (#rel:preorder a) (r:mreference a rel) (m:mem) =
  not ((get_hmap m) `Map.contains` (frameOf r)) \/
  Heap.unused_in (as_ref r) ((get_hmap m) `Map.sel` (frameOf r))

let contains_ref_in_its_region (#a:Type) (#rel:preorder a) (m:mem) (r:mreference a rel) =
  Heap.contains (get_hmap m `Map.sel` (frameOf r)) (as_ref r)

let fresh_ref (#a:Type) (#rel:preorder a) (r:mreference a rel) (m0:mem) (m1:mem) :Type0 =
  let i = frameOf r in
  Heap.fresh (as_ref r) (get_hmap m0 `Map.sel` i) (get_hmap m1 `Map.sel` i)

let fresh_region (i:rid) (m0 m1:mem) =
  not (get_hmap m0 `Map.contains` i) /\ get_hmap m1 `Map.contains` i

let sel (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel) :GTot a
  = Heap.sel (get_hmap m `Map.sel` (frameOf s)) (as_ref s)

let upd (#a:Type) (#rel:preorder a) (m:mem) (s:mreference a rel{live_region m (frameOf s)}) (v:a)
  :GTot mem
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let i = frameOf s in
    let h = Map.upd h i (Heap.upd (Map.sel h i) (as_ref s) v) in
    lemma_is_wf_ctr_and_tip_intro h rid_ctr tip;
    mk_mem rid_ctr h tip

let alloc (#a:Type0) (rel:preorder a) (id:rid) (init:a) (mm:bool) (m:mem{get_hmap m `Map.contains` id})
  :Tot (p:(mreference a rel & mem){let (r, h) = Heap.alloc rel (get_hmap m `Map.sel` id) init mm in
                                   as_ref (fst p) == r /\
                                   get_hmap (snd p) == Map.upd (get_hmap m) id h})
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let r, id_h = Heap.alloc rel (Map.sel h id) init mm in
    let h = Map.upd h id id_h in
    lemma_is_wf_ctr_and_tip_intro h rid_ctr tip;
    (mk_mreference id r), mk_mem rid_ctr h tip

let free (#a:Type0) (#rel:preorder a) (r:mreference a rel{is_mm r}) (m:mem{m `contains` r})
  :Tot mem
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let i = frameOf r in
    let i_h = h `Map.sel` i in
    let i_h = Heap.free_mm i_h (as_ref r) in
    let h = Map.upd h i i_h in
    lemma_is_wf_ctr_and_tip_intro h rid_ctr tip;
    mk_mem rid_ctr h tip

let upd_tot (#a:Type) (#rel:preorder a) (m:mem) (r:mreference a rel{m `contains` r}) (v:a)
  :Tot mem
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let i = frameOf r in
    let i_h = h `Map.sel` i in
    let i_h = Heap.upd_tot i_h (as_ref r) v in
    let h = Map.upd h i i_h in
    lemma_is_wf_ctr_and_tip_intro h rid_ctr tip;
    mk_mem rid_ctr h tip

let sel_tot (#a:Type) (#rel:preorder a) (m:mem) (r:mreference a rel{m `contains` r})
  :Tot a
  = Heap.sel_tot (get_hmap m `Map.sel` (frameOf r)) (as_ref r)

let fresh_frame (m0:mem) (m1:mem) =
  not (get_hmap m0 `Map.contains` get_tip m1) /\
  parent (get_tip m1) == get_tip m0  /\
  get_hmap m1 == Map.upd (get_hmap m0) (get_tip m1) Heap.emp

let hs_push_frame (m:mem) :Tot (m':mem{fresh_frame m m'})
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let new_tip_rid = extend tip rid_ctr 1 in
    let h = Map.upd h new_tip_rid Heap.emp in
    assert (forall (s:rid). (new_tip_rid `is_above` s /\ s `is_in` h) ==> s = new_tip_rid);
    lemma_is_wf_ctr_and_tip_intro h (rid_ctr + 1) new_tip_rid;
    mk_mem (rid_ctr + 1) h new_tip_rid

let new_eternal_region (m:mem) (parent:rid{is_eternal_region_hs parent /\ get_hmap m `Map.contains` parent})
                       (c:option int{None? c \/ is_heap_color (Some?.v c)})
  :Tot (t:(rid & mem){fresh_region (fst t) m (snd t)})
  = let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
    lemma_is_wf_ctr_and_tip_elim m;
    let new_rid =
      if None? c then extend_monochrome parent rid_ctr
      else extend parent rid_ctr (Some?.v c)
    in
    let h = Map.upd h new_rid Heap.emp in
    lemma_is_wf_ctr_and_tip_intro h (rid_ctr + 1) tip;
    new_rid, mk_mem (rid_ctr + 1) h tip

let new_freeable_heap_region
  (m:mem)
  (parent:rid{is_eternal_region_hs parent /\ get_hmap m `Map.contains` parent})  
: t:(rid & mem){fresh_region (fst t) m (snd t) /\ rid_freeable (fst t)}
= let h, rid_ctr, tip = get_hmap m, get_rid_ctr m, get_tip m in
  lemma_is_wf_ctr_and_tip_elim m;
  let new_rid = extend_monochrome_freeable parent rid_ctr true in
  let h = Map.upd h new_rid Heap.emp in
  lemma_is_wf_ctr_and_tip_intro h (rid_ctr + 1) tip;
  new_rid, mk_mem (rid_ctr + 1) h tip

let free_heap_region
  (m0:mem)
  (r:rid{
    is_heap_color (color r) /\
    rid_freeable r /\
    get_hmap m0 `Map.contains` r})
: mem
= let h0, rid_ctr0 = get_hmap m0, get_rid_ctr m0 in
  lemma_is_wf_ctr_and_tip_elim m0;
  let dom = remove_elt (Map.domain h0) r in
  let h1 = Map.restrict dom h0 in
  lemma_is_wf_ctr_and_tip_intro h1 rid_ctr0 (get_tip m0);
  mk_mem (get_rid_ctr m0) h1 (get_tip m0)


(****** The following two lemmas are only used in FStar.Pointer.Base, and invoked explicitly ******)

val lemma_sel_same_addr (#a:Type0) (#rel:preorder a) (h:mem) (r1:mreference a rel) (r2:mreference a rel)
  :Lemma (requires (frameOf r1 == frameOf r2 /\ h `contains` r1 /\ as_addr r1 = as_addr r2 /\ is_mm r1 == is_mm r2))
         (ensures  (h `contains` r2 /\ sel h r1 == sel h r2))

val lemma_upd_same_addr (#a:Type0) (#rel:preorder a) (h:mem) (r1 r2:mreference a rel) (x: a)
  :Lemma (requires (frameOf r1 == frameOf r2 /\ (h `contains` r1 \/ h `contains` r2) /\
                    as_addr r1 == as_addr r2 /\ is_mm r1 == is_mm r2))
         (ensures  (h `contains` r1 /\ h `contains` r2 /\ upd h r1 x == upd h r2 x))

(* Two references with different reads are disjoint. *)
val mreference_distinct_sel_disjoint
  (#a:Type0) (#rel1: preorder a) (#rel2: preorder a) (h: mem) (r1: mreference a rel1) (r2:mreference a rel2)
  : Lemma (requires (h `contains` r1 /\ h `contains` r2 /\ frameOf r1 == frameOf r2 /\ as_addr r1 == as_addr r2))
          (ensures (sel h r1 == sel h r2))

(*
 * AR: 12/26: modifies clauses
 *            NOTE: the modifies clauses used to have a m0.tip == m1.tip conjunct too
 *                  which seemed a bit misplaced
 *                  removing that conjunct required very few changes (one in HACL), since ST effect gives it already
 *)
let modifies (s:Set.set rid) (m0:mem) (m1:mem) = modifies_just s (get_hmap m0) (get_hmap m1)

let modifies_transitively (s:Set.set rid) (m0:mem) (m1:mem) = FStar.Monotonic.HyperHeap.modifies s (get_hmap m0) (get_hmap m1)

let heap_only (m0:mem) = get_tip m0 == root

let top_frame (m:mem) = get_hmap m `Map.sel` get_tip m

val modifies_drop_tip (m0:mem) (m1:mem) (m2:mem) (s:Set.set rid)
    : Lemma (fresh_frame m0 m1 /\ get_tip m1 == get_tip m2 /\
             modifies_transitively (Set.union s (Set.singleton (get_tip m1))) m1 m2 ==>
             modifies_transitively s m0 (pop m2))

let modifies_one id h0 h1 = modifies_one id (get_hmap h0) (get_hmap h1)
let modifies_ref (id:rid) (s:Set.set nat) (h0:mem) (h1:mem) =
  Heap.modifies s (get_hmap h0 `Map.sel` id) (get_hmap h1 `Map.sel` id)


(****** API for generating modifies clauses in the old style, should use new modifies clauses now ******)

noeq type some_ref =
  | Ref: #a:Type0 -> #rel:preorder a -> mreference a rel -> some_ref

let some_refs = list some_ref

[@@"opaque_to_smt"]
private let rec regions_of_some_refs (rs:some_refs) :Tot (Set.set rid) =
  match rs with
  | []         -> Set.empty
  | (Ref r)::tl -> Set.union (Set.singleton (frameOf r)) (regions_of_some_refs tl)

[@@"opaque_to_smt"]
private let rec refs_in_region (r:rid) (rs:some_refs) :GTot (Set.set nat) =
  match rs with
  | []         -> Set.empty
  | (Ref x)::tl ->
    Set.union (if frameOf x = r then Set.singleton (as_addr x) else Set.empty)
              (refs_in_region r tl)

[@@"opaque_to_smt"]
private let rec modifies_some_refs (i:some_refs) (rs:some_refs) (h0:mem) (h1:mem) :GTot Type0 =
  match i with
  | []         -> True
  | (Ref x)::tl ->
    (modifies_ref (frameOf x) (refs_in_region (frameOf x) rs) h0 h1) /\
    (modifies_some_refs tl rs h0 h1)

[@@"opaque_to_smt"]
unfold private let norm_steps :list norm_step =
  //iota for reducing match
  [iota; zeta; delta; delta_only ["FStar.Monotonic.HyperStack.regions_of_some_refs";
                                  "FStar.Monotonic.HyperStack.refs_in_region";
                                  "FStar.Monotonic.HyperStack.modifies_some_refs"];
   primops]

[@@"opaque_to_smt"]
unfold let mods (rs:some_refs) (h0 h1:mem) :GTot Type0 =
  (norm norm_steps (modifies (regions_of_some_refs rs) h0 h1)) /\
  (norm norm_steps (modifies_some_refs rs rs h0 h1))

//////

val eternal_disjoint_from_tip (h:mem{is_stack_region (get_tip h)})
                              (r:rid{is_heap_color (color r) /\
                                     r =!= root /\
                                     r `is_in` get_hmap h})
  :Lemma (disjoint (get_tip h) r)

val above_tip_is_live (#a:Type) (#rel:preorder a) (m:mem) (x:mreference a rel)
  :Lemma (requires (frameOf x `is_above` get_tip m))
         (ensures  (frameOf x `is_in` get_hmap m))

/////

(****** Lemmas about equality of mem ******)

val lemma_heap_equality_cancel_same_mref_upd
  (#a:Type) (#rel:preorder a) (h:mem) (r:mreference a rel) (x y:a)
  :Lemma (requires (live_region h (frameOf r)))
         (ensures  (upd (upd h r x) r y == upd h r y))

val lemma_heap_equality_upd_with_sel
  (#a:Type) (#rel:preorder a) (h:mem) (r:mreference a rel)
  :Lemma (requires (h `contains` r))
         (ensures  (upd h r (sel h r) == h))

val lemma_heap_equality_commute_distinct_upds
  (#a:Type) (#b:Type) (#rel_a:preorder a) (#rel_b:preorder b)
  (h:mem) (r1:mreference a rel_a) (r2:mreference b rel_b) (x:a) (y:b)
  :Lemma (requires (as_addr r1 =!= as_addr r2 /\ live_region h (frameOf r1) /\ live_region h (frameOf r2)))
         (ensures  (upd (upd h r1 x) r2 y == upd (upd h r2 y) r1 x))

val lemma_next_addr_contained_refs_addr (_:unit)
  :Lemma (forall (a:Type0) (rel:preorder a) (r:mreference a rel) (m:mem).
            m `contains` r ==> as_addr r < Heap.next_addr (get_hmap m `Map.sel` frameOf r))

(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

val aref: Type0

val dummy_aref :aref

val aref_equal (a1 a2: aref)
  :Ghost bool (requires True)
              (ensures  (fun b -> b == true <==> a1 == a2))

(* Introduction rule *)

val aref_of (#t: Type) (#rel: preorder t) (r: mreference t rel) :aref

(* Operators lifted from reference *)

val frameOf_aref (a:aref) :GTot rid

val frameOf_aref_of (#t:Type) (#rel:preorder t) (r:mreference t rel)
  :Lemma (frameOf_aref (aref_of r) == frameOf r)
         [SMTPat (frameOf_aref (aref_of r))]

val aref_as_addr (a:aref) :GTot pos

val aref_as_addr_aref_of (#t:Type) (#rel:preorder t) (r:mreference t rel)
  :Lemma (aref_as_addr (aref_of r) == as_addr r)
         [SMTPat (aref_as_addr (aref_of r))]

val aref_is_mm (r:aref) :GTot bool

val is_mm_aref_of (#t:Type) (#rel:preorder t) (r:mreference t rel)
  :Lemma (aref_is_mm (aref_of r) == is_mm r)
         [SMTPat (aref_is_mm (aref_of r))]

[@@ remove_unused_type_parameters [0;1]]
val aref_unused_in (a:aref) (h:mem) :GTot Type0

val unused_in_aref_of (#t:Type) (#rel:preorder t) (r:mreference t rel) (h:mem)
  :Lemma (aref_unused_in (aref_of r) h <==> unused_in r h)
         [SMTPat (aref_unused_in (aref_of r) h)]

val contains_aref_unused_in (#a:Type) (#rel:preorder a) (h:mem) (x:mreference a rel) (y:aref)
  :Lemma (requires (contains h x /\ aref_unused_in y h))
         (ensures  (frameOf x <> frameOf_aref y \/ as_addr x <> aref_as_addr y))
         [SMTPat (contains h x); SMTPat (aref_unused_in y h)]

(* Elimination rule *)

[@@ remove_unused_type_parameters [0;1;2;3]]
val aref_live_at (h:mem) (a:aref) (v:Type0) (rel:preorder v) :GTot Type0

val greference_of (a:aref) (v:Type0) (rel:preorder v)
  :Ghost (mreference v rel) (requires (exists h . aref_live_at h a v rel))
                            (ensures  (fun _ -> True))

val reference_of (h:mem) (a:aref) (v:Type0) (rel:preorder v)
  :Pure (mreference v rel) (requires (aref_live_at h a v rel))
                           (ensures  (fun x -> aref_live_at h a v rel /\ frameOf x == frameOf_aref a /\
			                    as_addr x == aref_as_addr a /\ is_mm x == aref_is_mm a))

val aref_live_at_aref_of (h:mem) (#t:Type0) (#rel:preorder t) (r:mreference t rel)
  :Lemma (aref_live_at h (aref_of r) t rel <==> contains h r)
         [SMTPat (aref_live_at h (aref_of r) t rel)]

val contains_greference_of (h:mem) (a:aref) (t:Type0) (rel:preorder t)
  :Lemma (requires (exists h' . aref_live_at h' a t rel))
         (ensures  ((exists h' . aref_live_at h' a t rel) /\ (contains h (greference_of a t rel) <==> aref_live_at h a t rel)))
         [SMTPatOr [
             [SMTPat (contains h (greference_of a t rel))];
             [SMTPat (aref_live_at h a t rel)];
         ]]

val aref_of_greference_of (a:aref) (v:Type0) (rel:preorder v)
  :Lemma (requires (exists h' . aref_live_at h' a v rel))
         (ensures  ((exists h' . aref_live_at h' a v rel) /\ aref_of (greference_of a v rel) == a))
         [SMTPat (aref_of (greference_of a v rel))]

(* Operators lowered to rref *)

val frameOf_greference_of (a:aref) (t:Type0) (rel:preorder t)
  :Lemma (requires (exists h . aref_live_at h a t rel))
         (ensures  ((exists h . aref_live_at h a t rel) /\ frameOf (greference_of a t rel) == frameOf_aref a))
         [SMTPat (frameOf (greference_of a t rel))]

val as_addr_greference_of (a:aref) (t:Type0) (rel:preorder t)
  :Lemma (requires (exists h . aref_live_at h a t rel))
         (ensures  ((exists h . aref_live_at h a t rel) /\ as_addr (greference_of a t rel) == aref_as_addr a))
         [SMTPat (as_addr (greference_of a t rel))]

val is_mm_greference_of (a:aref) (t:Type0) (rel:preorder t)
  :Lemma (requires (exists h . aref_live_at h a t rel))
         (ensures  ((exists h . aref_live_at h a t rel) /\ is_mm (greference_of a t rel) == aref_is_mm a))
         [SMTPat (is_mm (greference_of a t rel))]

val unused_in_greference_of (a:aref) (t:Type0) (rel:preorder t) (h:mem)
  :Lemma (requires (exists h . aref_live_at h a t rel))
         (ensures  ((exists h . aref_live_at h a t rel) /\ (unused_in (greference_of a t rel) h <==> aref_unused_in a h)))
         [SMTPat (unused_in (greference_of a t rel) h)]

val sel_reference_of (a:aref) (v:Type0) (rel:preorder v) (h1 h2: mem)
  :Lemma (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
         (ensures  (aref_live_at h2 a v rel /\ sel h1 (reference_of h2 a v rel) == sel h1 (greference_of a v rel)))
         [SMTPat (sel h1 (reference_of h2 a v rel))]

val upd_reference_of (a:aref) (v:Type0) (rel:preorder v) (h1 h2:mem) (x:v)
  :Lemma (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
         (ensures  (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel /\
	            upd h1 (reference_of h2 a v rel) x == upd h1 (greference_of a v rel) x))
         [SMTPat (upd h1 (reference_of h2 a v rel) x)]
