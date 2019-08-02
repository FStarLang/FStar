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
module Ex06e
//insertion-sort

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(* Definition of the [mem] function *)
val mem: int -> list int -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

(* Exercise: implement insertion sort and prove its partial correctness *)
val sort : l:list int -> Tot (m:list int{sorted m /\ (forall x. mem x l == mem x m)})
