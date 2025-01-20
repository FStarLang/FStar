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
module FStar.TwoLevelHeap
open FStar.Map
open FStar.Heap
type rid = int  //region id
type t = Map.t rid heap

let st_pre = st_pre_h t
let st_post' (a:Type) (pre:Type) = st_post_h' t a pre
let st_post  (a:Type) = st_post_h t a
let st_wp (a:Type) = st_wp_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:st_wp a) =
       STATE a wp
effect ST (a:Type) (pre:st_pre) (post: (h0:t -> Tot (st_post' a (pre h0)))) =
       STATE a
             (fun (p:st_post a) (h:t) -> pre h /\ (forall a h1. pre h /\ post h a h1 ==> p a h1)) (* WP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:pure_wp a) (p:st_post a) (h:t) -> wp (fun a -> p a h)

type rref (id:rid) (a:Type) = ref a
val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref #a #id r = r

private val ref_as_rref : #a:Type -> i:rid -> r:ref a -> Tot (rref i a)
let ref_as_rref #a i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) == r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj #a #i r = ()

assume val new_region: unit -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (id:rid) (m1:t) -> exists (h:heap). not(Map.contains m0 id) /\ m1==Map.upd m0 id h))

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> Map.contains m i))
    (ensures (fun m0 x m1 ->
                    let region_i = Map.sel m0 i in
                    (~ (Heap.contains region_i (as_ref x))
                    /\ m1==Map.upd m0 i (Heap.upd region_i (as_ref x) init))))

assume val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _u m1 -> m1== Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)))

assume val op_Bang:#a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m1==m0 /\ x==Heap.sel (Map.sel m0 i) (as_ref r)))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0==x /\ m1==m0))

let modifies (s:Set.set rid) (m0:t) (m1:t) =
    Map.equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0))

let fresh_region (i:rid) (m0:t) (m1:t) =
  not (Map.contains m0 i)
  /\ Map.contains m1 i

let contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

let fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  ~ (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))
