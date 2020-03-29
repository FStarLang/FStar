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
module Bug103


val map: ('a -> 'b) -> 'a -> 'b
let map f x = f x

val ok: list int -> list int
let ok = map Cons 3

val ok2: list int
let ok2 = map (fun l -> Cons 3 l) [17]

val bug: list int
let bug = map (Cons 3) [17]
(*
bug103.fst(14,14-14,22) : Error
Expected type "(_:U374 -> U375)";
got type "(list U376)"
 *)
