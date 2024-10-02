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
(*perhaps this should be an interface file?*)

module LallocTest
open FStar.Regions.RST
open StackAndHeap
open FStar.Regions.Located
open Heap
open Stack
open Set
open Prims
open List
open FStar.Regions.Heap  open FStar.Regions.Located
open ListSet



(*see example usages of lalloc and lift in lallocTest.fst*)
type point = {x:int ; y:int}

val lx : p:(located point) -> PureMem int (requires (fun m-> liveLoc p m))
              (ensures (fun v m1 -> v == (greveal p).x ))
let lx p =  (llift (fun (p:point)-> p.x)) p

val lallocExample1 : px:int -> py:int -> PureMem int (fun m -> True) (fun m v -> v == px+1)
let lallocExample1 px py =
  pushRegion ();
  let sp= lalloc ({x=px ; y=py}) in
  let r = lx sp in
  popRegion ();
  (r+1)
