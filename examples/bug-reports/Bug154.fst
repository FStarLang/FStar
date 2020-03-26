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
let rec search x l =
  match l with
  | [] -> false
  | n :: l' ->  x = n || (if false then search x l' else false)

(* (\* works but it shouldn't *\) *)
(* val search : x:int -> l:(list int) -> Pure bool (requires True) (ensures (fun r -> r = mem x l)) *)
(* let rec search x l = *)
(*   match l with *)
(*   | [] -> false *)
(*   | n :: l' ->  x = n || (if false then search x l' else false) *)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let rec search' x l =
  match l with
  | [] -> false
  | n :: l' -> x = n || (search' x l' && false)
*)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let search' x l =
  match l with
  | [] -> false
  | n :: l' -> x = n
*)

(* this equivalent thing fails as it should
val search' : x:int -> l:(list int) -> Tot (r:bool{r <==> mem x l})
let rec search' x l =
  match l with
  | [] -> false
  | n :: l' -> if x = n then true else (if false then search' x l' else false)
*)
