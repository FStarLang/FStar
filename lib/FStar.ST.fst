(*--build-config
    options:--admit_fsi Set;
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst
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
open FStar.Set
open FStar.Heap
type ref (a:Type) = Heap.ref a
// this intentionally does not preclude h' extending h with fresh refs
opaque logic type modifies (mods:set aref) (h:heap) (h':heap) =
    b2t (Heap.equal h' (concat h' (restrict h (complement mods))))

kind STPre = STPre_h heap
kind STPost (a:Type) = STPost_h heap a
kind STWP (a:Type) = STWP_h heap a
new_effect STATE = STATE_h heap
effect State (a:Type) (wp:STWP a) =
       STATE a wp wp
effect ST (a:Type) (pre:STPre) (post: (heap -> STPost a)) =
       STATE a
             (fun (p:STPost a) (h:heap) -> pre h /\ (forall a h1. (pre h /\ post h a h1) ==> p a h1)) (* WP *)
             (fun (p:STPost a) (h:heap) -> (forall a h1. (pre h /\ post h a h1) ==> p a h1))          (* WLP *)
effect St (a:Type) =
       ST a (fun h -> True) (fun h0 r h1 -> True)
sub_effect
  DIV   ~> STATE = fun (a:Type) (wp:PureWP a) (p:STPost a) (h:heap) -> wp (fun a -> p a h)

(* signatures WITHOUT permissions *)
assume val recall: #a:Type -> r:ref a -> STATE unit
                                         (fun 'p h -> Heap.contains h r ==> 'p () h)
                                         (fun 'p h -> Heap.contains h r ==> 'p () h)

assume val alloc:  #a:Type -> init:a -> ST (ref a)
                                           (fun h -> True)
                                           (fun h0 r h1 -> not(contains h0 r) /\ contains h1 r /\ h1==upd h0 r init)

assume val read:  #a:Type -> r:ref a -> STATE a
                                         (fun 'p h -> 'p (sel h r) h)
                                         (fun 'p h -> 'p (sel h r) h)

assume val write:  #a:Type -> r:ref a -> v:a -> ST unit
                                                 (fun h -> True)
                                                 (fun h0 x h1 -> h1==upd h0 r v)

assume val op_Colon_Equals:  #a:Type -> r:ref a -> v:a -> ST unit
                                                 (fun h -> True)
                                                 (fun h0 x h1 -> h1==upd h0 r v)

assume val get: unit -> ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h=h1)
