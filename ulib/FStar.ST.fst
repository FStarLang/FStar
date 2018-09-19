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

module I = FStar.IMST
module W = FStar.Monotonic.Witnessed

(***** Heap relation and witnessed *****)

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (rel:preorder a) (r:mref a rel). h1 `contains` r ==>
                                               (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

type heap_predicate = heap -> Type0

let stable (p:heap_predicate) =
  forall (h1:heap) (h2:heap). (p h1 /\ heap_rel h1 h2) ==> p h2

let witnessed (p:heap_predicate{stable p}) :Type0 = I.witnessed #heap #heap_rel p

val lemma_functoriality (p:heap_predicate{stable p /\ witnessed p}) 
                        (q:heap_predicate{stable q /\ (forall (h:heap). p h ==> q h)})
  :Lemma (ensures (witnessed q))
let lemma_functoriality p q = W.lemma_witnessed_weakening heap_rel p q


(***** Intatiating FStar.IMST to a heap-specific ST effect *****)

//new_effect IST = I.IMST (* intermediate step to generate a "fresh" copy of IMST, and hide global state operations *)

//unfold let lift_imst_ist (a:Type) (wp:I.st_wp a) = wp
//sub_effect I.IMST ~> IST = lift_imst_ist

let st_pre            = st_pre_h heap
let st_post' (a:Type) (pre:Type) = st_post_h' heap a pre
let st_post  (a:Type) = st_post_h heap a
let st_wp (a:Type)    = st_wp_h heap a

effect STATE a (wp:st_wp a) = I.IMST a (I.index heap heap_rel wp)

effect State (a:Type) (wp:st_wp a) = STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (h:heap -> Tot (st_post' a (pre h)))) =
  STATE a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)


(***** Actions for this ST effect *****)

let contains_pred (#a:Type0) (#rel:preorder a) (r:mref a rel) = fun h -> h `contains` r

type mref (a:Type0) (rel:preorder a) = r:Heap.mref a rel{is_mm r = false /\ witnessed (contains_pred r)}

abstract let recall (#a:Type) (#rel:preorder a) (r:mref a rel) :STATE unit (fun p h -> Heap.contains h r ==> p () h)
  = I.recall #heap #heap_rel (contains_pred r)

abstract let alloc (#a:Type) (#rel:preorder a) (init:a)
  :ST (mref a rel)
      (fun h -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
  = let h0 = I.get #heap #heap_rel () in
    let r, h1 = alloc rel h0 init false in
    I.put #heap #heap_rel h1;
    I.witness #heap #heap_rel (contains_pred r);
    r

abstract let read (#a:Type) (#rel:preorder a) (r:mref a rel) :STATE a (fun p h -> p (sel h r) h)
  = let h0 = I.get #heap #heap_rel () in
    I.recall #heap #heap_rel (contains_pred r);
    Heap.lemma_sel_equals_sel_tot_for_contained_refs h0 r;
    sel_tot h0 r

abstract let write (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
  = let h0 = I.get #heap #heap_rel () in
    I.recall #heap #heap_rel (contains_pred r);
    let h1 = upd_tot h0 r v in
    Heap.lemma_distinct_addrs_distinct_preorders ();
    Heap.lemma_distinct_addrs_distinct_mm ();
    Heap.lemma_upd_equals_upd_tot_for_contained_refs h0 r v;
    I.put #heap #heap_rel h1

abstract let get (u:unit) 
  :ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h==h1) 
  = I.get #heap #heap_rel ()

abstract
let op_Bang (#a:Type) (#rel:preorder a) (r:mref a rel)
  : STATE a (fun p h -> p (sel h r) h)
  = read #a #rel r

abstract let op_Colon_Equals (#a:Type) (#rel:preorder a) (r:mref a rel) (v:a)
  : ST unit
    (fun h -> rel (sel h r) v)
    (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\
                 modifies (Set.singleton (addr_of r)) h0 h1 /\ equal_dom h0 h1 /\
                 sel h1 r == v)
  = write #a #rel r v

type ref (a:Type0) = mref a (trivial_preorder a)

let modifies_none (h0:heap) (h1:heap) = modifies !{} h0 h1





