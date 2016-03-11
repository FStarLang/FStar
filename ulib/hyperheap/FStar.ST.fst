(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.Map --admit_fsi FStar.HyperHeap;
    other-files:FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst hyperHeap.fsi
 --*)
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
open FStar.HyperHeap
let modifies = HyperHeap.modifies
let ref (t:Type) = rref root t
let st_pre = st_pre_h t
let st_post (a:Type) = st_post_h t a
let st_wp (a:Type) = st_wp_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:st_wp a) =
       STATE a wp wp
effect ST (a:Type) (pre:st_pre) (post: (t -> Tot (st_post a))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. post h a h1 ==> p a h1)) (* WP *)
             (fun (p:st_post a) (h:t) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:t) -> wp (fun a -> p a h)



assume val new_region: r0:rid -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
                        /\ m1=Map.upd m0 r1 Heap.emp))
 
inline let ralloc_post (#a:Type) (i:rid) (init:a) (m0:t) (x:rref i a) (m1:t) = 
     (let region_i = Map.sel m0 i in
       not (Heap.contains region_i (as_ref x))
           /\ m1=Map.upd m0 i (Heap.upd region_i (as_ref x) init))

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> True))
    (ensures (ralloc_post i init))

inline let alloc_post (#a:Type) (init:a) m0 (x:ref a) m1 = 
  (let region_i = Map.sel m0 root in
    not (Heap.contains region_i (as_ref x))
   /\ m1=Map.upd m0 root (Heap.upd region_i (as_ref x) init))

assume val alloc: #a:Type -> init:a -> ST (ref a)
    (requires (fun m -> True))
    (ensures (alloc_post init))

inline let assign_post (#a:Type) (#i:rid) (r:rref i a) (v:a) m0 (_u:unit) m1 : Type = 
  m1=Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)

assume val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (assign_post r v))

inline let deref_post (#a:Type) (#i:rid) (r:rref i a) m0 x m1 =
  m1=m0 /\ x=Heap.sel (Map.sel m0 i) (as_ref r)

assume val op_Bang: #a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (deref_post r))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0 /\ map_invariant m1))

assume val recall: #a:Type -> #i:rid -> r:rref i a -> STATE unit
   (fun 'p m0 -> Map.contains m0 i /\ Heap.contains (Map.sel m0 i) (as_ref r) ==> 'p () m0)
   (fun 'p m0 -> Map.contains m0 i /\ Heap.contains (Map.sel m0 i) (as_ref r) ==> 'p () m0)

assume val recall_region: i:rid -> STATE unit
   (fun 'p m0 -> Map.contains m0 i /\ map_invariant m0  ==> 'p () m0)
   (fun 'p m0 -> Map.contains m0 i /\ map_invariant m0  ==> 'p () m0)
