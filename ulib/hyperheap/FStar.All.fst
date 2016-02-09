(*--build-config
    options:--admit_fsi Set --admit_fsi Map --admit_fsi HyperHeap;
    other-files:FStar.Set.fsi FStar.Heap.fst map.fsi FStar.List.Tot.fst hyperHeap.fsi stHyperHeap.fst
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
module FStar.All
open FStar.ST

kind AllPre = AllPre_h HyperHeap.t
kind AllPost (a:Type) = AllPost_h HyperHeap.t a
kind AllWP (a:Type) = AllWP_h HyperHeap.t a
new_effect ALL = ALL_h HyperHeap.t
effect All (a:Type) (pre:AllPre) (post: (HyperHeap.t -> AllPost a)) =
       ALL a
           (fun (p:AllPost a) (h:HyperHeap.t) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* AllWP *)
           (fun (p:AllPost a) (h:HyperHeap.t) -> forall ra h1. (pre h /\ post h ra h1) ==> p ra h1) (* WLP *)
default effect ML (a:Type) =
  ALL a (all_null_wp HyperHeap.t a) (all_null_wp HyperHeap.t a)
sub_effect
  STATE ~> ALL = fun (a:Type) (wp:STWP a)   (p:AllPost a) -> wp (fun a -> p (V a))
sub_effect
  EXN   ~> ALL = fun (a:Type) (wp:ExWP a)   (p:AllPost a) (h:HyperHeap.t) -> wp (fun ra -> p ra h)

assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val failwith: string -> All 'a (fun h -> True) (fun h a h' -> is_Err a /\ h==h')
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a
