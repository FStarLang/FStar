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
(* ******************************************************************************** *)
module NegativeTests.Heap
open FStar.TSet
open FStar.Heap
assume val x : ref int
assume val y : ref int
assume val h : heap
assume DistinctXY: x =!= y

[@(expect_failure [19])]
let test2 _ = assert (sel (upd (upd h x 0) y 1) y = 0) //should fail
(* let test10 (x:ref int) (y:ref int) (h0:heap) (h1:heap) (h2:heap) = *)
(*   admitP (h1 == concat h1 (restrict h0 (complement empty))); *)
(*   admitP (h1 == upd h0 x 0); *)
(*   admitP (~ (contains h1 y)); *)
(*   assert false //should fail *)
