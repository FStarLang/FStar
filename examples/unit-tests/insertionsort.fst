(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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


module InsertionSort
open Prims.PURE


(* An effect abbreviation for a lemma *)
(*ghost*) effect Fact ('res:Type) ('p:Type) = Pure 'res True (fun r => 'p)


(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x < y) && (sorted (y::xs))

(* Fact about sorted *)
val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val sorted_smaller: x:int -> y:int -> l:list int ->
                    Fact unit (sorted (x::l) ==> mem y l ==> x < y)
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs

(* Insertion in a sorted list: does not work at such for now *)
val insert : int -> l:list int{sorted l == true} -> Tot (l':list int{sorted l' == true})
let rec insert y l = match l with
    | [] -> [y]
    | x::xs -> if y < x then y::l else x::(insert y xs)

(* Insertion sort *)
val sort : list int -> Tot (l:list int{sorted l == true})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert x (sort xs)
