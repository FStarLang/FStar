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
module FStar.STH

open FStar.HyperStack
open FStar.HyperHeap
open FStar.HST

let modifies = HyperHeap.modifies
let ref (t:Type) = rref root t
let st_pre = st_pre_h t
let st_post (a:Type) = st_post_h t a
let st_wp (a:Type) = st_wp_h t a

assume val color : rid -> GTot int

assume val new_region: r0:rid -> STH rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
			/\ color r1 = color r0
                        /\ m1==Map.upd m0 r1 Heap.emp))

assume val new_colored_region: r0:rid -> c:int -> STH rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
			/\ color r1 = c
                        /\ m1==Map.upd m0 r1 Heap.emp))

unfold let ralloc_post (#a:Type) (i:rid) (init:a) (m0:t) (x:rref i a) (m1:t) = 
     (let region_i = Map.sel m0 i in
       not (Heap.contains region_i (as_ref x))
           /\ m1==HyperHeap.upd m0 x init)

assume val ralloc: #a:Type -> i:rid -> init:a -> STH (rref i a)
    (requires (fun m -> True))
    (ensures (ralloc_post i init))

unfold let alloc_post (#a:Type) (init:a) m0 (x:ref a) m1 = 
  (let region_i = Map.sel m0 root in
    not (Heap.contains region_i (as_ref x))
   /\ m1==HyperHeap.upd m0 x init)

assume val alloc: #a:Type -> init:a -> STH (ref a)
    (requires (fun m -> True))
    (ensures (alloc_post init))

unfold let assign_post (#a:Type) (#i:rid) (r:rref i a) (v:a) m0 (_u:unit) m1 : Type = 
  m1==HyperHeap.upd m0 r v

assume val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> STH unit
  (requires (fun m -> True))
  (ensures (assign_post r v))

unfold let deref_post (#a:Type) (#i:rid) (r:rref i a) m0 x m1 =
  m1==m0 /\ x==HyperHeap.sel m0 r

assume val op_Bang: #a:Type -> #i:rid -> r:rref i a -> STH a
  (requires (fun m -> True))
  (ensures (deref_post r))

assume val get: unit -> STH t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0==x /\ m1==m0 /\ map_invariant m1))

assume val recall: #a:Type -> #i:rid -> r:rref i a -> STATE unit
   (fun 'p m0 -> Map.contains m0.h i /\ Heap.contains (Map.sel m0.h i) (as_ref r) ==> 'p () m0)

assume val recall_region: i:rid -> STATE unit
   (fun 'p m0 -> Map.contains m0.h i /\ map_invariant m0.h  ==> 'p () m0)
