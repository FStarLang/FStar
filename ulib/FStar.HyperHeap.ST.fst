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
module FStar.HyperHeap.ST
open FStar.HyperHeap
let modifies s h0 h1 = HyperHeap.modifies s h0 h1
let modifies_none h0 h1 = modifies Set.empty h0 h1
let ref (t:Type) = rref root t
let st_pre = st_pre_h t
let st_post' (a:Type) (pre:Type) = st_post_h' t a pre
let st_post  (a:Type) = st_post' a True
let st_wp (a:Type) = st_wp_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:st_wp a) =
       STATE a wp
effect ST (a:Type) (pre:st_pre) (post: (x:t -> Tot (st_post' a (pre x)))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:t) -> wp (fun a -> p a h)


assume val new_region: r0:rid -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
			/\ color r1 = color r0
                        /\ m1==Map.upd m0 r1 Heap.emp))

assume val new_colored_region: r0:rid -> c:int -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (r1:rid) (m1:t) ->
                           extends r1 r0
                        /\ fresh_region r1 m0 m1
			/\ color r1 = c
                        /\ m1==Map.upd m0 r1 Heap.emp))

unfold let ralloc_post (#a:Type) (i:rid) (init:a) (m0:t) (x:rref i a) (m1:t) = 
    let region_i = Map.sel m0 i in
    ~ (Heap.contains region_i (as_ref x))
  /\ m1==(m0.[x]<-init)

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> True))
    (ensures (ralloc_post i init))

unfold let alloc_post (#a:Type) (init:a) m0 (x:ref a) m1 = 
   let region_i = Map.sel m0 root in
   ~ (Heap.contains region_i (as_ref x))
 /\ m1==(m0.[x]<-init)

assume val alloc: #a:Type -> init:a -> ST (ref a)
    (requires (fun m -> True))
    (ensures (alloc_post init))

unfold let assign_post (#a:Type) (#i:rid) (r:rref i a) (v:a) m0 (_u:unit) m1 : Type = 
  m1==(m0.[r] <- v)

assume val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (assign_post r v))

unfold let deref_post (#a:Type) (#i:rid) (r:rref i a) m0 x m1 =
  m1==m0 /\ x==m0.[r]

assume val op_Bang: #a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (deref_post r))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0==x /\ m1==m0 /\ map_invariant m1))

assume val recall: #a:Type -> #i:rid -> r:rref i a -> STATE unit
   (fun 'p m0 -> Map.contains m0 i /\ Heap.contains (Map.sel m0 i) (as_ref r) ==> 'p () m0)

assume val recall_region: i:rid -> STATE unit
   (fun 'p m0 -> Map.contains m0 i /\ map_invariant m0  ==> 'p () m0)
