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
module Bug256

assume type p : int -> Type

assume val witness: i:int{p i}


(* Fails to typecheck -- works now *)
val f1: unit -> i:int{p i}
let f1 = let g () = witness in g
(* This variant works: *)
(* let f1 = let g u = witness in g *)

(* Fails to typecheck -- works now *)
val f2: int -> ((i:int{p i}) * int)
let f2 = let g i = (witness,4) in g
