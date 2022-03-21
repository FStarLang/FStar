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
module Test.IFC
////////////////////////////////////////////////////////////////////////////////
//A basic test of monadic information flow control provided in FStar.IFC
////////////////////////////////////////////////////////////////////////////////
open FStar.IFC

let two_point_lattice =
  SemiLattice true (fun x y -> x || y)

let sl2 = FStar.Ghost.hide two_point_lattice
let high : lattice_element sl2 = Ghost.hide true
let low  : lattice_element sl2 = Ghost.hide false

let ret #a (x:a) = return low x

let test1 (#l1:lattice_element sl2)
          (px:protected l1 int)
   : z:protected l1 int{reveal z = reveal px + 1}
   = map px (fun x -> x + 1)

let test2 (#l1:lattice_element sl2)
          (#l2:lattice_element sl2)
          (px:protected l1 int)
          (py:protected l2 int)
   : z:protected (l1 `lub` l2) int{reveal z = reveal px + reveal py}
   = let f (x:int) : (z:protected l2 int{reveal z = x + reveal py}) =
         map py (fun y -> x + y)
     in
     let g :  (z:protected l1 (protected l2 int){reveal (reveal z) = reveal px + reveal py}) =
         map px f
     in
     join g

let test3 (#l1:lattice_element sl2)
          (#l2:lattice_element sl2)
          (px:protected l1 int)
          (py:protected l2 int)
   : z:protected (l1 `lub` l2) int{reveal z = reveal px + reveal py}
   = x <-- px ;
     y <-- py ;
     ret (x + y)
