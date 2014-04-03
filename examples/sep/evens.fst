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
#monadic(DST.DST, DST.returnTX, DST.bindNoExnTX)
module Evens
open DST
open RefSet

type Even = fun (x:int) => exists (n:int). x=2*n

type evens_t ('Inv:heap => E) (fp:refset) = 
    Writer int (Requires (fun h => On fp 'Inv h))
               (Ensures _ (fun h u h' => Even u /\ On fp 'Inv h'))
               (Modifies fp)
    
logic data type t = 
  | Evens : 'Inv:(heap => E)
          -> fp:refset (* ghost *)
          -> (unit -> evens_t 'Inv fp)
          -> t

type Inv1 : ref int => ref int => heap => E
assume Inv1_def: forall r1 r2 h. Inv1 r1 r2 h 
                                  <==> 
                                 Perm r1 h /\ Perm r2 h /\ SelHeap h r1 = SelHeap h r2

type HeapP : heap => E
val create1: u:unit -> Writer t TrivialPre 
                              (Ensures _ (fun h v h' => 
                                  On  (Evens_proj_1 v) (Evens_proj_0 v) h'
                               /\ Fresh h (Evens_proj_1 v)))
                              (Modifies EmptySet)
let create1 (u:unit) = 
  let x = DST.ref 0 in
  let y = DST.ref 0 in
  let fp = Union (Singleton x) (Singleton y) in 
  let evens (u:unit) : evens_t (Inv1 x y) fp =
    let rx = !x in 
    let ry = !y in 
    x := rx + 1;
    y := ry + 1;
    rx + ry in
  Evens (Inv1 x y) fp evens
    

type Inv2 : ref int => heap => E
assume Inv2_def: forall r h. Inv2 r h <==> Perm r h
val create2: u:unit -> Writer t TrivialPre 
                              (Ensures _ (fun h v h' => 
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
    
