(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi, and Microsoft Research

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
module FStar.ST

open FStar.TSet
open FStar.Heap
open FStar.Preorder

module W = FStar.Monotonic.Witnessed

(***** Global ST (GST) effect with put, get, witness, and recall *****)

new_effect GST = STATE_h heap

let gst_pre           = st_pre_h heap
let gst_post' (a:Type) (pre:Type) = st_post_h' heap a pre
let gst_post  (a:Type) = st_post_h heap a
let gst_wp (a:Type)   = st_wp_h heap a

unfold let lift_div_gst (a:Type) (wp:pure_wp a) (p:gst_post a) (h:heap) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
                                               (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

assume val gst_get: unit    -> GST heap (fun p h0 -> p h0 h0)
assume val gst_put: h1:heap -> GST unit (fun p h0 -> heap_rel h0 h1 /\ p () h1)

type heap_predicate = heap -> Type0

let stable (p:heap_predicate) =
  forall (h1:heap) (h2:heap). (p h1 /\ heap_rel h1 h2) ==> p h2

[@@"opaque_to_smt"]
let witnessed (p:heap_predicate{stable p}) : Type0 = W.witnessed heap_rel p

assume val gst_witness: p:heap_predicate -> GST unit (fun post h0 -> stable p /\ p h0 /\ (witnessed p ==> post () h0))
assume val gst_recall:  p:heap_predicate -> GST unit (fun post h0 -> stable p /\ witnessed p /\ (p h0 ==> post () h0))

val lemma_functoriality (p:heap_predicate{stable p /\ witnessed p}) 
                        (q:heap_predicate{stable q /\ (forall (h:heap). p h ==> q h)})
  :Lemma (ensures (witnessed q))
let lemma_functoriality p q =
  reveal_opaque (`%witnessed) witnessed;
  W.lemma_witnessed_weakening heap_rel p q

(***** ST effect *****)

let st_pre   = gst_pre
let st_post' = gst_post'
let st_post  = gst_post
let st_wp    = gst_wp

new_effect STATE = GST

unfold let lift_gst_state (a:Type) (wp:gst_wp a) = wp
sub_effect GST ~> STATE = lift_gst_state

effect State (a:Type) (wp:st_wp a) = STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATE a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

let contains_pred (#a:Type0) (#rel:preorder a) (r:mref a rel) = fun h -> h `contains` r

type mref (a:Type0) (rel:preorder a) = r:Heap.mref a rel{is_mm r = false /\ witnessed (contains_pred r)}

let recall (#a:Type) (#rel:preorder a) (r:mref a rel) :STATE unit (fun p h -> Heap.contains h r ==> p () h)
  = gst_recall (contains_pred r)

let alloc (#a:Type) (#rel:preorder a) (init:a)
  :ST (mref a rel)
      (fun h -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = let h0 = gst_get () in
    let r, h1 = alloc rel h0 init false in
    gst_put h1;
    gst_witness (contains_pred r);
    r

let read (#a:Type) (#rel:preorder a) (r:mref a rel) :STATE a (fun p h -> p (sel h r) h)
  = let h0 = gst_get () in
    gst_recall (contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs h0 r;
    sel_tot h0 r

let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
  = let h0 = gst_get () in
    gst_recall (contains_pred r);
    let h1 = upd_tot h0 r v in
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
    gst_put h1

let get (u:unit) :ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h==h1) = gst_get ()

let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATE a (fun p h -> p (sel h r) h)
= read #a #rel r

let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
= write #a #rel r v

type ref (a:Type0) = mref a (trivial_preorder a)

let modifies_none (h0:heap) (h1:heap) = modifies !{} h0 h1
