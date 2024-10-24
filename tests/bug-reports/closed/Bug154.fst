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
module Bug154

val search : x:int -> l:(list int) -> Tot (b:bool{b = false})
[@@expect_failure [19]]
let rec search x l =
  match l with
  | [] -> false
  | n :: l' ->  x = n || (if false then search x l' else false)

val search2 : x:int -> l:(list int) -> Pure bool (requires True) (ensures (fun r -> r = List.mem x l))
[@@expect_failure [19]]
let rec search2 x l =
  match l with
  | [] -> false
  | n :: l' ->  x = n || (if false then search2 x l' else false)

val search3 : x:int -> l:(list int) -> Tot (r:bool{r <==> List.mem x l})
[@@expect_failure [19]]
let rec search3 x l =
  match l with
  | [] -> false
  | n :: l' -> x = n || (search3 x l' && false)

val search4 : x:int -> l:(list int) -> Tot (r:bool{r <==> List.mem x l})
[@@expect_failure [19]]
let search4 x l =
  match l with
  | [] -> false
  | n :: l' -> x = n

val search5 : x:int -> l:(list int) -> Tot (r:bool{r <==> List.mem x l})
[@@expect_failure [19]]
let rec search5 x l =
  match l with
  | [] -> false
  | n :: l' -> if x = n then true else (if false then search5 x l' else false)
