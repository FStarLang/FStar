(*--build-config
options:--admit_fsi FStar.Set;
other-files: FStar.Set.fsi FStar.Heap.fst FStar.ST.fst;
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
open FStar.Heap
open FStar.ST

kind AllPre = AllPre_h heap
kind AllPost (a:Type) = AllPost_h heap a
kind AllWP (a:Type) = AllWP_h heap a
new_effect ALL = ALL_h heap
effect All (a:Type) (pre:AllPre) (post: (heap -> AllPost a)) =
       ALL a
           (fun (p:AllPost a) (h:heap) -> pre h /\ (forall ra h1. post h ra h1 ==> p ra h1)) (* AllWP *)
           (fun (p:AllPost a) (h:heap) -> forall ra h1. (pre h /\ post h ra h1) ==> p ra h1) (* WLP *)
default effect ML (a:Type) =
  ALL a (all_null_wp heap a) (all_null_wp heap a)
sub_effect
  STATE ~> ALL = fun (a:Type) (wp:STWP a)   (p:AllPost a) -> wp (fun a -> p (V a))
sub_effect
  EXN   ~> ALL = fun (a:Type) (wp:ExWP a)   (p:AllPost a) (h:heap) -> wp (fun ra -> p ra h)

assume val pipe_right: 'a -> ('a -> 'b) -> 'b
assume val pipe_left: ('a -> 'b) -> 'a -> 'b
assume val failwith: string -> All 'a (fun h -> True) (fun h a h' -> is_Err a /\ h==h')
assume val exit: int -> 'a
assume val try_with: (unit -> 'a) -> (exn -> 'a) -> 'a
