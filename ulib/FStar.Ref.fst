(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Ref

(* wrapper over FStar.ST to provide operations over refs with default preorder *)

include FStar.Heap
include FStar.ST

open FStar.Heap
open FStar.ST

unfold
let sel (#a:Type0) (h:heap) (r:ref a) : GTot a
  = Heap.sel h r

unfold
let upd (#a:Type0) (h:heap) (r:ref a) (v:a) :GTot heap
  = Heap.upd h r v

unfold
let addr_of (#a:Type0) (r:ref a) : GTot nat = addr_of r

unfold
let contains (#a:Type0) (h:heap) (r:ref a) :GTot Type0
  = Heap.contains h r

unfold
let unused_in (#a:Type0) (r:ref a) (h:heap) :GTot Type0
  = Heap.unused_in r h

unfold
let fresh (#a:Type0) (r:ref a) (h0:heap) (h1:heap) : Type0
  = Heap.fresh r h0 h1

unfold
let only (#a:Type0) (r:ref a) :GTot (Set.set nat)
  = Heap.only r

val recall (#a:Type0) (r:ref a) : STATE unit (fun p h -> h `contains` r ==> p () h)
let recall #_ r = recall r

val alloc (#a:Type0) (init:a)
  :ST (ref a)
      (fun _       -> True)
      (fun h0 r h1 -> fresh r h0 h1 /\ modifies Set.empty h0 h1 /\ sel h1 r == init)
let alloc #_ init = alloc init

val read (#a:Type0) (r:ref a) :STATE a (fun p h -> p (sel h r) h)
let read #_ r = read r

val write (#a:Type0) (r:ref a) (v:a)
  :ST unit (fun _ -> True) (fun h0 _ h1 -> h0 `contains` r /\ modifies (only r) h0 h1 /\ equal_dom h0 h1 /\ sel h1 r == v)
let write #_ r v = write r v

val op_Bang (#a:Type0) (r:ref a) :STATE a (fun p h -> p (sel h r) h)
let op_Bang #_ r = read r

val op_Colon_Equals (#a:Type0) (r:ref a) (v:a)
  :ST unit (fun _ -> True) (fun h0 _ h1 -> h0 `contains` r /\ modifies (only r) h0 h1 /\ equal_dom h0 h1 /\ sel h1 r == v)
let op_Colon_Equals #_ r v = write r v
