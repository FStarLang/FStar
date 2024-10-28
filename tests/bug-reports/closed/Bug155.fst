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
module Bug155

assume val pred: x:int -> Tot bool
assume val test: x:int -> Pure int
    (requires (True))
    (ensures (fun y -> pred y))
let test1 = assert (pred (test 0))

(* this works now *)
let test2' z = assert (pred (test z))

assume val myassert: b:Type -> Pure unit (requires (b)) (ensures (fun _ -> True))
assume val pred2: x:int -> Pure bool
    (requires (True))
    (ensures (fun y -> y))
let test2 x = myassert (b2t (pred2 x))

let test3 x = let y = pred2 x in assert y
