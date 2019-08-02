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
module TestTwoLevelHeap
open FStar.TwoLevelHeap

val test0: #r:rid -> i:int -> v:rref r int -> ST int
  (requires (fun m0 -> Map.contains m0 r))
  (ensures (fun m0 k m1 -> k=i+sel m0 v
                        /\ modifies Set.empty m0 m1))
let test0 #r i v =
  let r = new_region () in
  let x = ralloc r i in
  let j = !x in
  x := j + !v;
  !x
