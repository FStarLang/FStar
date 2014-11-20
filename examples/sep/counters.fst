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
module Evens
logic type even (x:int) = x % 2 == 0

effect Evens (inv:heap -> Type) (fp:refs) = 
          ST2 int (requires (fun h => On fp inv h))
                  (ensures (fun h u h' => even u /\ On fp inv h'))
                  (modifies fp)
    
type t = 
  | Evens : inv:(heap -> Type)
          -> fp:refs (* ghost *)
          -> (unit -> Evens inv fp)
          -> t

opaque type inv1 (r1:ref int) (r2:ref int) (h:heap) = 
    Perm r1 h /\ Perm r2 h /\ SelHeap h r1 = SelHeap h r2

val mk_counter: unit 
          -> ST2 t (requires (fun h -> True))
                   (ensures  (fun h v h' -> 
                             On  (Evens.fp v) (Evens_inv v) h'
                             /\ Fresh h (Evens.fp v)))
                   (modifies no_refs)
let mk_counter _ =
  let x = alloc 0 in
  let y = alloc 0 in
  let fp = Union (Singleton x) (Singleton y) in 
  let evens : unit -> Evens (inv1 x y) fp = fun _ -> 
    let rx = !x in 
    let ry = !y in 
    x := rx + 1;
    y := ry + 1;
    rx + ry in
  Evens (inv1 x y) fp evens
    

opaque type inv2 (r:ref int) (h:heap) = Perm r h

val mk_counter_2: unit 
              -> ST2 t (requires (fun h -> True))
                       (ensures (fun h v h' -> 
                         On  (Evens_proj_1 v) (Evens_proj_0 v) h'
                         /\ Fresh h (Evens_proj_1 v)))
                              (Modifies EmptySet)
let create2 (u:unit) = 
  let x = ref 0 in
  let fp = Singleton x in
  let evens (u:unit) : evens_t (Inv2 x) fp =
    let rx = !x in
    x := rx + 1;
    2 * rx in
  Evens (Inv2 x) fp evens
    
