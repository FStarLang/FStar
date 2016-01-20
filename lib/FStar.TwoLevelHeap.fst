(*--build-config
    options:--admit_fsi Set --admit_fsi Map;
    other-files:FStar.Set.fsi FStar.Heap.fst map.fsi
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
module FStar.TwoLevelHeap
open FStar.Map
open FStar.Heap
type rid = int  //region id
type t = Map.t rid heap

kind STPre = STPre_h t
kind STPost (a:Type) = STPost_h t a
kind STWP (a:Type) = STWP_h t a
new_effect STATE = STATE_h t
effect State (a:Type) (wp:STWP a) =
       STATE a wp wp
effect ST (a:Type) (pre:STPre) (post: (t -> STPost a)) =
       STATE a
             (fun (p:STPost a) (h:t) -> pre h /\ (forall a h1. post h a h1 ==> p a h1)) (* WP *)
             (fun (p:STPost a) (h:t) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:t) -> wp (fun a -> p a h)

private type rref (id:rid) (a:Type) = ref a
val as_ref : #a:Type -> #id:rid -> r:rref id a -> Tot (ref a)
let as_ref id r = r

private val ref_as_rref : #a:Type -> i:rid -> r:ref a -> Tot (rref i a)
let ref_as_rref i r = r

val lemma_as_ref_inj: #a:Type -> #i:rid -> r:rref i a
    -> Lemma (requires (True))
             (ensures ((ref_as_rref i (as_ref r) = r)))
       [SMTPat (as_ref r)]
let lemma_as_ref_inj i r = ()

assume val new_region: unit -> ST rid
      (requires (fun m -> True))
      (ensures (fun (m0:t) (id:rid) (m1:t) -> exists (h:heap). not(Map.contains m0 id) /\ m1=Map.upd m0 id h))

type Let (#a:Type) (x:a) (body:(a -> Type)) = body x

let sel (#a:Type) (#i:rid) (m:t) (r:rref i a) = Heap.sel (Map.sel m i) (as_ref r)
let upd (#a:Type) (#i:rid) (m:t) (r:rref i a) (v:a) = Map.upd m i (Heap.upd (Map.sel m i) (as_ref r) v)

assume val ralloc: #a:Type -> i:rid -> init:a -> ST (rref i a)
    (requires (fun m -> Map.contains m i))
    (ensures (fun m0 x m1 ->
                    Let (Map.sel m0 i) (fun region_i ->
                    not (Heap.contains region_i (as_ref x))
                    /\ m1=Map.upd m0 i (Heap.upd region_i (as_ref x) init))))

assume val op_Colon_Equals: #a:Type -> #i:rid -> r:rref i a -> v:a -> ST unit
  (requires (fun m -> True))
  (ensures (fun m0 _u m1 -> m1= Map.upd m0 i (Heap.upd (Map.sel m0 i) (as_ref r) v)))

assume val op_Bang:#a:Type -> #i:rid -> r:rref i a -> ST a
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m1=m0 /\ x=Heap.sel (Map.sel m0 i) (as_ref r)))

assume val get: unit -> ST t
  (requires (fun m -> True))
  (ensures (fun m0 x m1 -> m0=x /\ m1=m0))

type modifies (s:Set.set rid) (m0:t) (m1:t) =
    Map.Equal m1 (Map.concat m1 (Map.restrict (Set.complement s) m0))

type fresh_region (i:rid) (m0:t) (m1:t) =
  not (Map.contains m0 i)
  /\ Map.contains m1 i

type contains_ref (#a:Type) (#i:rid) (r:rref i a) (m:t) =
    Map.contains m i /\ Heap.contains (Map.sel m i) (as_ref r)

type fresh_rref (#a:Type) (#i:rid) (r:rref i a) (m0:t) (m1:t) =
  not (Heap.contains (Map.sel m0 i) (as_ref r))
  /\  (Heap.contains (Map.sel m1 i) (as_ref r))
