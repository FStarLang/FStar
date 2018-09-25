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

let map_invariant = map_invariant_predicate

let downward_closed = downward_closed_predicate

let tip_top = tip_top_predicate

let rid_ctr_pred = rid_ctr_pred_predicate

noeq type mem' =
  | HS :rid_ctr:int -> h:hmap -> tip:rid -> mem'

let mk_mem rid_ctr h tip = HS rid_ctr h tip

let get_hmap m = m.h
let get_rid_ctr m = m.rid_ctr
let get_tip m = m.tip

let lemma_mk_mem'_projectors _ _ _ = ()

let lemma_mem_projectors_are_in_wf_relation _ = ()

let lemma_is_wf_ctr_and_tip_intro _ _ _ = ()

let lemma_is_wf_ctr_and_tip_elim _ = ()

let lemma_map_invariant _ _ _ = ()

let lemma_downward_closed _ _ _ = ()

let lemma_tip_top _ _ = ()

let lemma_tip_top_smt _ _ = ()

let lemma_rid_ctr_pred _ = ()

let as_ref #_ #_ x = MkRef?.ref x

let lemma_as_ref_inj #_ #_ _ = ()

private val lemma_extends_fresh_disjoint: i:rid -> j:rid -> ipar:rid -> jpar:rid
                               -> (m0:mem) -> (m1:mem) ->
  Lemma (requires (let h0, h1 = get_hmap m0, get_hmap m1 in
                   (map_invariant h0       /\
		    map_invariant h1       /\
                    fresh_region i m0 m1   /\
                    fresh_region j m0 m1   /\
                    h0 `Map.contains` ipar /\
                    h0 `Map.contains` jpar /\
                    extends i ipar         /\
                    extends j jpar         /\
                    i<>j)))
        (ensures (disjoint i j))
let lemma_extends_fresh_disjoint i j ipar jpar m0 m1 = ()

let lemma_sel_same_addr #_ #_ _ _ _ = ()

let lemma_upd_same_addr #_ #_ h r1 r2 x =
  FStar.Monotonic.Heap.lemma_heap_equality_upd_same_addr (Map.sel h.h (frameOf r1)) (as_ref r1) (as_ref r2) x;
  if StrongExcludedMiddle.strong_excluded_middle (h `contains` r1) then
    lemma_sel_same_addr h r1 r2
  else lemma_sel_same_addr h r2 r1

let mreference_distinct_sel_disjoint #_ #_ #_ h r1 r2 =
  Heap.lemma_distinct_addrs_distinct_preorders ();
  Heap.lemma_distinct_addrs_distinct_mm ();
  Heap.lemma_sel_same_addr (Map.sel h.h (frameOf r1)) (as_ref r1) (as_ref r2)

private let lemma_pop_is_popped (m0:mem{poppable m0})
  : Lemma (popped m0 (pop m0))
  = let m1 = pop m0 in
    assert (Set.equal (Map.domain m1.h) (remove_elt (Map.domain m0.h) m0.tip))

let modifies_drop_tip _ _ _ _ = ()

let eternal_disjoint_from_tip h r = ()

let lemma_heap_equality_cancel_same_mref_upd #_ #_ h r x y =
  let h0 = upd (upd h r x) r y in
  let h1 = upd h r y in
  Heap.lemma_heap_equality_cancel_same_mref_upd (Map.sel h.h (frameOf r)) (as_ref r) x y;
  assert (Map.equal h0.h h1.h)

let lemma_heap_equality_upd_with_sel #_ #_ h r =
  let h' = upd h r (sel h r) in
  Heap.lemma_heap_equality_upd_with_sel (Map.sel h.h (frameOf r)) (as_ref r);
  assert (Map.equal h.h h'.h)

let lemma_heap_equality_commute_distinct_upds #_ #_ #_ #_ h r1 r2 x y =
  let h0 = upd (upd h r1 x) r2 y in
  let h1 = upd (upd h r2 y) r1 x in
  if frameOf r1 = frameOf r2 then Heap.lemma_heap_equality_commute_distinct_upds (Map.sel h.h (frameOf r1)) (as_ref r1) (as_ref r2) x y;
  assert (Map.equal h0.h h1.h)

let lemma_next_addr_contained_refs_addr ()
  :Lemma (forall (a:Type0) (rel:preorder a) (r:mreference a rel) (m:mem).
            m `contains` r ==> as_addr r < Heap.next_addr (get_hmap m `Map.sel` frameOf r))
  = let aux (a:Type0) (rel:preorder a) (r:mreference a rel) (m:mem)
      :Lemma (m `contains` r ==> as_addr r < Heap.next_addr (get_hmap m `Map.sel` frameOf r))
      = Heap.lemma_next_addr_contained_refs_addr (get_hmap m `Map.sel` frameOf r) (as_ref r)
    in
    Classical.forall_intro_4 aux

private let lemma_upd_1 #a #rel (h:mem) (x:mreference a rel) (v:a{rel (sel h x) v}) : Lemma
  (requires (contains h x))
  (ensures (contains h x
            /\ modifies_one (frameOf x) h (upd h x v)
            /\ modifies_ref (frameOf x) (Set.singleton (as_addr x)) h (upd h x v)
            /\ sel (upd h x v) x == v ))
  = ()

private let lemma_upd_2 (#a:Type) (#rel:preorder a) (h:mem) (x:mreference a rel) (v:a{rel (sel h x) v}) : Lemma
  (requires (frameOf x = get_tip h /\ x `unused_in` h))
  (ensures (frameOf x = get_tip h
            /\ modifies_one (get_tip h) h (upd h x v)
            /\ modifies_ref (get_tip h) Set.empty h (upd h x v)
            /\ sel (upd h x v) x == v ))
  = ()

private val lemma_live_1: #a:Type ->  #a':Type -> #rel:preorder a -> #rel':preorder a'
                  -> h:mem -> x:mreference a rel -> x':mreference a' rel' -> Lemma
  (requires (contains h x /\ x' `unused_in` h))
  (ensures  (frameOf x <> frameOf x' \/ ~ (as_ref x === as_ref x')))
let lemma_live_1 #a #a' #rel #rel' h x x' = ()

let above_tip_is_live (#a:Type) (#rel:preorder a) (m:mem) (x:mreference a rel) : Lemma
  (requires (frameOf x `is_above` get_tip m))
  (ensures (frameOf x `is_in` get_hmap m))
  = ()


(*** Untyped views of references *)

(* Definition and ghost decidable equality *)

noeq abstract type aref: Type0 =
| ARef:
    (aref_region: rid) ->
    (aref_aref: Heap.aref) ->
    aref

abstract let dummy_aref : aref = ARef root Heap.dummy_aref

abstract let aref_equal
  (a1 a2: aref)
: Ghost bool
  (requires True)
  (ensures (fun b -> b == true <==> a1 == a2))
= a1.aref_region = a2.aref_region && Heap.aref_equal a1.aref_aref a2.aref_aref

(* Introduction rule *)

abstract let aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
  : Tot aref
  = ARef (frameOf r) (Heap.aref_of (as_ref r))

(* Operators lifted from reference *)

abstract let frameOf_aref
  (a: aref)
: GTot rid
= a.aref_region

abstract let frameOf_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (frameOf_aref (aref_of r) == frameOf r)
  [SMTPat (frameOf_aref (aref_of r))]
= ()

abstract let aref_as_addr
  (a: aref)
: GTot (x: nat { x > 0 } )
= Heap.addr_of_aref a.aref_aref

abstract let aref_as_addr_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_as_addr (aref_of r) == as_addr r)
  [SMTPat (aref_as_addr (aref_of r))]
= Heap.addr_of_aref_of (as_ref r)

abstract let aref_is_mm
  (r: aref)
: GTot bool
= Heap.aref_is_mm r.aref_aref

abstract let is_mm_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_is_mm (aref_of r) == is_mm r)
  [SMTPat (aref_is_mm (aref_of r))]
= Heap.is_mm_aref_of (as_ref r)

abstract let aref_unused_in
  (a: aref)
  (h: mem)
: GTot Type0
= ~ (live_region h a.aref_region) \/
  Heap.aref_unused_in a.aref_aref (Map.sel h.h a.aref_region)

abstract let unused_in_aref_of
  (#t: Type)
  (#rel: preorder t)
  (r: mreference t rel)
  (h: mem)
: Lemma
  (aref_unused_in (aref_of r) h <==> unused_in r h)
  [SMTPat (aref_unused_in (aref_of r) h)]
= Heap.unused_in_aref_of (as_ref r) (Map.sel h.h (frameOf r))

abstract
val contains_aref_unused_in: #a:Type -> #rel: preorder a -> h:mem -> x:mreference a rel -> y:aref -> Lemma
  (requires (contains h x /\ aref_unused_in y h))
  (ensures  (frameOf x <> frameOf_aref y \/ as_addr x <> aref_as_addr y))
  [SMTPat (contains h x); SMTPat (aref_unused_in y h)]
let contains_aref_unused_in #a #rel h x y =
  if frameOf x = frameOf_aref y
  then
    Heap.contains_aref_unused_in (Map.sel h.h (frameOf x)) (as_ref x) y.aref_aref
  else ()

(* Elimination rule *)

abstract
let aref_live_at
  (h: mem)
  (a: aref)
  (v: Type)
  (rel: preorder v)
: GTot Type0
= live_region h a.aref_region
  /\ Heap.aref_live_at (Map.sel h.h a.aref_region) a.aref_aref v rel

abstract
let greference_of
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Ghost (mreference v rel)
  (requires (exists h . aref_live_at h a v rel))
  (ensures (fun _ -> True))
= MkRef a.aref_region (Heap.gref_of a.aref_aref v rel)

abstract
let reference_of
  (h: mem)
  (a: aref)
  (v: Type)
  (rel: preorder v)
: Pure (mreference v rel)
  (requires (aref_live_at h a v rel))
  (ensures (fun x -> aref_live_at h a v rel /\ frameOf x == frameOf_aref a /\ as_addr x == aref_as_addr a /\ is_mm x == aref_is_mm a))
= MkRef a.aref_region (Heap.ref_of (Map.sel h.h a.aref_region) a.aref_aref v rel)

abstract
let aref_live_at_aref_of
  (h: mem)
  (#t: Type0)
  (#rel: preorder t)
  (r: mreference t rel)
: Lemma
  (aref_live_at h (aref_of r) t rel <==> contains h r)
  [SMTPat (aref_live_at h (aref_of r) t rel)]
= ()

abstract
let contains_greference_of
  (h: mem)
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h' . aref_live_at h' a t rel))
  (ensures ((exists h' . aref_live_at h' a t rel) /\ (contains h (greference_of a t rel) <==> aref_live_at h a t rel)))
  [SMTPatOr [
    [SMTPat (contains h (greference_of a t rel))];
    [SMTPat (aref_live_at h a t rel)];
  ]]
= ()

abstract
let aref_of_greference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
: Lemma
  (requires (exists h' . aref_live_at h' a v rel))
  (ensures ((exists h' . aref_live_at h' a v rel) /\ aref_of (greference_of a v rel) == a))
  [SMTPat (aref_of (greference_of a v rel))]
= ()

(* Operators lowered to rref *)

abstract let frameOf_greference_of
  (a: aref)
  (t: Type)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ frameOf (greference_of a t rel) == frameOf_aref a))
  [SMTPat (frameOf (greference_of a t rel))]
= ()

abstract
let as_addr_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ as_addr (greference_of a t rel) == aref_as_addr a))
  [SMTPat (as_addr (greference_of a t rel))]
= ()

abstract
let is_mm_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ is_mm (greference_of a t rel) == aref_is_mm a))
  [SMTPat (is_mm (greference_of a t rel))]
= ()

abstract
let unused_in_greference_of
  (a: aref)
  (t: Type0)
  (rel: preorder t)
  (h: mem)
: Lemma
  (requires (exists h . aref_live_at h a t rel))
  (ensures ((exists h . aref_live_at h a t rel) /\ (unused_in (greference_of a t rel) h <==> aref_unused_in a h)))
  [SMTPat (unused_in (greference_of a t rel) h)]
= ()

abstract
let sel_reference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
  (h1 h2: mem)
: Lemma
  (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
  (ensures (aref_live_at h2 a v rel /\ sel h1 (reference_of h2 a v rel) == sel h1 (greference_of a v rel)))
  [SMTPat (sel h1 (reference_of h2 a v rel))]
= ()

abstract
let upd_reference_of
  (a: aref)
  (v: Type0)
  (rel: preorder v)
  (h1 h2: mem)
  (x: v)
: Lemma
  (requires (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel))
  (ensures (aref_live_at h1 a v rel /\ aref_live_at h2 a v rel /\ upd h1 (reference_of h2 a v rel) x == upd h1 (greference_of a v rel) x))
  [SMTPat (upd h1 (reference_of h2 a v rel) x)]
= ()
