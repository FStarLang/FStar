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
module Bug1150

let positive' (s:int) : Type0 = s > 0
let positive : p:(int->Type0){p 42} = positive'

assume val witness : p:(int -> Type) -> Pure unit (requires (p 43)) (ensures (fun _ -> True))

val foo : unit -> Tot unit
let foo () = witness positive
