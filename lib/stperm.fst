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
module ST
open Prims.STATE
open Set
open Heap

opaque type Modifies (mods:refs) (h:heap) (h':heap) =
           is_SomeRefs mods ==> (Heap.equal h' (concat h' (restrict h (complement (SomeRefs.v mods)))))

let modifies (r:refs) = r
kind Pre  = heap -> Type
kind Post (a:Type) = a -> heap -> Type
effect ST (a:Type) (pre:Pre) (post: (heap -> Post a)) (mods:refs) =
        STATE a
              (fun (p:Post a) (h:heap) -> pre h /\ (forall a h1. (pre h /\ Modifies mods h h1 /\ post h a h1) ==> p a h1)) (* WP *)
              (fun (p:Post a) (h:heap) -> (forall a h1. (pre h /\ Modifies mods h h1 /\ post h a h1) ==> p a h1))          (* WLP *)

(* signatures WITH permissions *)
assume val alloc: a:Type -> init:a -> Prims.STATE.ST (ref a) 
                                         (fun h -> True) 
                                         (fun h0 r h1 -> not(contains h0 r) /\ contains h1 r /\ h1==upd h0 r init)
                                         (* (modifies no_refs) *)

assume val read: a:Type -> r:ref a -> ST a 
                                         (requires (fun h -> contains h r))
                                         (ensures (fun h0 x h1 -> h0==h1 /\ x==sel h0 r))
                                         (modifies no_refs)

assume val write: a:Type -> r:ref a -> v:a -> ST unit 
                                                 (requires (fun h -> contains h r))
                                                 (ensures (fun h0 x h1 -> h1==upd h0 r v))
                                                 (modifies (a_ref r))

assume val get: unit -> ST heap (fun h -> True) (fun h0 h h1 -> h0==h1 /\ h=h1) (modifies no_refs)

