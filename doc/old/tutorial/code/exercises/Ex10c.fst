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
module Ex10c
//evens

open FStar.Heap
open FStar.Set
open FStar.ST

type even (x:int) = x%2=0


effect InvST (t:Type) (inv:(heap -> Type)) (fp:set aref) (post:(heap -> t -> heap -> Type)) =
             ST t (fun h -> On fp inv h)
                  (fun h i h' -> post h i h' /\ On fp inv h')
//                  (SomeRefs fp)

type even_post (h:heap) (i:int) (h':heap) = even i


type t =
  | Evens : inv:(heap -> Type)
          -> fp:set aref
          -> (unit -> InvST int inv fp even_post)
          -> t

opaque type inv1 (r1:ref int) (r2:ref int) (h:heap) =
           Heap.sel h r1 = Heap.sel h r2
           /\ contains h r1
           /\ contains h r2

val mk_counter: unit
             -> ST t (requires (fun h -> True))
                     (ensures  (fun h v h' ->
                             On  (Evens.fp v) (Evens.inv v) h'
                             /\ Heap.fresh h (Evens.fp v)))
//                     (modifies no_refs)
let mk_counter _ =
  let x = ST.alloc 0 in
  let y = ST.alloc 0 in
  let evens () =
    let rx = ST.read x in
    let ry = ST.read y in
    ST.write x (rx + 1);
    ST.write y (ry + 1);
    rx + ry in
  Evens (inv1 x y) (Set.union (Set.singleton (Ref x)) (Set.singleton (Ref y))) evens


val mk_counter2: unit
               -> ST t (requires (fun h -> True))
                       (ensures  (fun h v h' ->
                         On  (Evens.fp v) (Evens.inv v) h'
                         /\ Heap.fresh h (Evens.fp v)))
//                       (modifies no_refs)
let mk_counter2 _ =
  let x = ST.alloc 0 in
  let evens = fun _ ->
    let rx = ST.read x in
    ST.write x (rx + 1);
    2 * rx in
  Evens (fun h -> b2t(contains h r)) (Set.singleton (Ref x)) evens
