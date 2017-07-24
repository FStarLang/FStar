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
open FStar.DataInvariant

(***** Global ST (GST) effect with put, get, witness, and recall *****)
type iheap = h:heap{forall r. h `contains` r ==> invariant_of h1 r (sel h1 r)}

new_effect GST = STATE_h heap

let gst_pre           = st_pre_h heap
let gst_post (a:Type) = st_post_h heap a
let gst_wp (a:Type)   = st_wp_h heap a

unfold let lift_div_gst (a:Type0) (wp:pure_wp a) (p:gst_post a) (h:heap) = wp (fun a -> p a h)
sub_effect DIV ~> GST = lift_div_gst

let related_at (h1:heap) (h2:heap) (a:Type0) (inv:data_inv a) (rel:preorder a) (r:mref a inv rel) = 
           h1 `contains` r ==>
           (h2 `contains` r /\ rel (sel h1 r) (sel h2 r))

let heap_rel (h1:heap) (h2:heap) =
  forall (a:Type0) (inv:data_inv a) (rel:preorder a) (r:mref a inv rel).
    related_at h1 h2 a inv rel r

let forall_intro_4 (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#d:(x:a -> y:b x -> z:c x y -> Type)) (#p:(x:a -> y:b x -> z:c x y -> w:d x y z -> Type0))
		  ($f: (x:a -> y:b x -> z:c x y -> w:d x y z -> Lemma (p x y z w)))
  : Lemma (forall (x:a) (y:b x) (z:c x y) (w:d x y z). p x y z w)
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y) (w:d x y z). p x y z w) = fun x -> FStar.Classical.forall_intro_3 (f x) in
    FStar.Classical.forall_intro g

let intro_heap_rel (h1:heap) (h2:heap) (f: (a:Type0) -> (inv:data_inv a) -> (rel:preorder a) -> (r:mref a inv rel) -> Lemma (related_at h1 h2 a inv rel r))
  : Lemma (heap_rel h1 h2)
  = forall_intro_4 f
  
assume val gst_get: unit    -> GST heap (fun p h0 -> p h0 h0)
assume val gst_put: h1:heap -> GST unit (fun p h0 -> heap_rel h0 h1 /\ p () h1)

type heap_predicate = heap -> Type0

let stable (p:heap_predicate) =
  forall (h1:heap) (h2:heap). (p h1 /\ heap_rel h1 h2) ==> p h2

assume type witnessed: (p:heap_predicate{stable p}) -> Type0

assume val gst_witness: p:heap_predicate -> GST unit (fun post h0 -> stable p /\ p h0 /\ (witnessed p ==> post () h0))
assume val gst_recall:  p:heap_predicate -> GST unit (fun post h0 -> stable p /\ witnessed p /\ (p h0 ==> post () h0))

assume val lemma_functoriality
  (p:heap_predicate{stable p /\ witnessed p}) (q:heap_predicate{stable q /\ (forall (h:heap). p h ==> q h)})
  :Lemma (ensures (witnessed q))

(***** ST effect *****)

let st_pre  = gst_pre
let st_post = gst_post
let st_wp   = gst_wp

new_effect STATE = GST

unfold let lift_gst_state (a:Type0) (wp:gst_wp a) = wp
sub_effect GST ~> STATE = lift_gst_state

effect State (a:Type) (wp:st_wp a) = STATE a wp

effect ST (a:Type) (pre:st_pre) (post: (heap -> Tot (st_post a))) =
  STATE a (fun (p:st_post a) (h:heap) -> pre h /\ (forall a h1. post h a h1 ==> p a h1))
effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

let contains_pred (#a:Type0) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) = fun h -> h `contains` r

type mref (a:Type0) (inv:data_inv a) (rel:preorder a) = r:Heap.mref a inv rel{witnessed (contains_pred r)}

abstract let recall (#a:Type) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) :STATE unit (fun p h -> Heap.contains h r ==> p () h)
  = gst_recall (contains_pred r)

abstract let alloc (#a:Type) (#inv:data_inv a) (#rel:preorder a) (init:a)
  :ST (mref a inv rel)
      (fun h -> True)
      (fun h0 r h1 -> let (r', h1') = alloc inv rel h0 init true in
	           witnessed (contains_pred r') /\ r' == r /\ h1 == h1')
  = let h0 = gst_get () in
    let r, h1 = alloc inv rel h0 init true in
    gst_put h1;
    gst_witness (contains_pred r);
    r

abstract let read (#a:Type) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) :STATE a (fun p h -> p (sel h r) h)
  = let h0 = gst_get () in
    gst_recall (contains_pred r);
    sel_tot h0 r

let upd_maintains_heap_inv (b:Type0) (inv_b:data_inv b) (rel_b:preorder b) (r':Heap.mref b inv_b rel_b) (v:b) (h1 h2 : heap):
(a:Type0) ->
(inv:data_inv a) ->
(rel:preorder a) ->
(r:Heap.mref a inv rel) ->
Lemma (requires h2 == upd h1 r' v) 
      (ensures (related_at h1 h2 a inv rel r)) //(h1 `contains` r ==> (h2 `contains` r /\ rel (sel h1 r) (sel h2 r)))) =
= fun a inv rel r ->
if compare_addrs r r'
then (assume (h2 `contains` r); assume (rel (sel h1 r) (sel h2 r)))
else ()


(* #reset-options // "--ugly --print_effect_args --print_full_names" *)



(* #set-options "--z3rlimit 30" *)

let upd_tot_maintains_heap_inv (#b:Type) (#inv_b:data_inv b) (#rel_b:preorder b) (r':Heap.mref b inv_b rel_b) (v:b) (h0 h1 : heap) :
Lemma
  (requires (h1 == upd h0 r' v))
  (ensures (heap_rel h0 h1)) =
  let aux (a : Type0) (inv:data_inv a) (rel:preorder a) (r:Heap.mref a inv rel) : 
    Lemma (related_at h0 h1 a inv rel r) =
    upd_maintains_heap_inv b inv_b rel_b r' v h0 h1 a inv rel r
  in
  forall_intro_4 aux
  
  
  assert (forall (a : Type0) (inv:data_inv a) (rel:preorder a) (r:mref a inv rel). related_at h0 h1 a inv rel r);
  intro_heap_rel h0 h1;  admit()
  
  assert (heap_rel h0 h1);
  admit()
  
  
  assert (forall (a : Type0) (inv:data_inv a) (rel:preorder a) (r:mref a inv rel). h0 `contains` r ==> (h1 `contains` r /\ rel (sel h0 r) (sel h1 r)))
  
  intro_heap_rel h0 h1
  

  assert (heap_rel h0 h1);
  admit()

  
  (fun (a : Type0) (inv:data_inv a) (rel:preorder a) (r:mref a inv rel) -> 
    
  let _ = fun 
    (FStar.Classical.forall_intro 
      (FStar.Classical.move_requires (fun (r:mref a inv rel) -> upd_maintains_heap_inv b inv_b rel_b r' v h0 h1 a inv rel))) in
   admit()
   
      
      
      r)) in 
  admit()
    
    
FStar.Classical.forall_intro_3 (fun (a : Type0) (inv:data_inv a) (rel:preorder a) ->
  ) <: Lemma (requires (h1 == upd h0 r' v))
                                                                                                               (ensures (heap_rel h0 h1))

abstract let write (#a:Type) (#inv:data_inv a) (#rel:preorder a) (r:mref a inv rel) (v:a)
  :ST unit (fun h -> rel (sel h r) v) (fun h0 x h1 -> rel (sel h0 r) v /\ h0 `contains` r /\ h1 == upd h0 r v)
  = let h0 = gst_get () in
    gst_recall (contains_pred r);
    let h1 = upd_tot h0 r v in
    assume (heap_rel h0 h1);
    // upd_tot_maintains_heap_inv r v;
    gst_put h1

abstract let get (u:unit) :ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h==h1) = gst_get ()

type ref (a:Type0) = mref a (trivial_invariant a) (trivial_preorder a)

let modifies_none (h0:heap) (h1:heap) = modifies Set.empty h0 h1
