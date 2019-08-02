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
module Test2

let good (x:int) = x=0
assume val g : z:int{z=z /\ good z } -> Tot nat

#reset-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0 --log_queries"

val f1 : x:int -> Pure int (requires True) (ensures (fun y -> good (x + y)))
let f1 x =
  let y = if x = 0
	  then g (x - 1)
	  else 0 in
  -x

val f2 : x:int -> Pure int (requires True) (ensures (fun y -> good (x + y)))
let f2 x =
  let y = if x = 0
	  then g 0
	  else 0 in
  y + 1


val f3 : x:ref int -> ST int (requires (fun h -> True)) (ensures (fun h0 y h1 -> h0==h1 /\ (Heap.sel h0 x = y)))
let f3 x = 
  let y = if !x = 0
  	  then g (!x - !x)
  	  else 0 in
  !x + y

