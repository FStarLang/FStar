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


module IntList_InsertionSort
open Prims.PURE

type intlist = 
  | Nil
  | Cons : hd:int -> tl:intlist -> intlist

(* Check that a list is sorted *)
val sorted: intlist -> Tot bool
let rec sorted l = match l with
    | Nil -> true
    | Cons x Nil -> true
    | Cons x (Cons y xs) -> (x <= y) && (sorted (Cons y xs))

val test_sorted: x:int -> l:intlist -> Fact unit ((sorted (Cons x l) /\ is_Cons l) ==> x <= Cons.hd l)
let test_sorted x l = ()

val test_sorted2: unit -> Tot (m:intlist{sorted m})
let test_sorted2 () = Nil

(* Fact about sorted *)
val mem: int -> intlist -> Tot bool
let rec mem a l = match l with
  | Nil -> false
  | Cons hd tl -> hd=a || mem a tl

val sorted_smaller: x:int -> y:int -> l:intlist ->
                    Fact unit (sorted (Cons x l) /\ mem y l ==> x <= y)
let rec sorted_smaller x y l = match l with
    | Nil -> ()
    | Cons z zs -> if z=y then () else sorted_smaller x y zs

val insert : i:int -> l:intlist{sorted l} -> Tot (m:intlist{sorted m /\ (forall x. mem x m <==> x==i \/ mem x l)})
let rec insert i l = match l with
  | Nil -> Cons i Nil
  | Cons hd tl ->
     if i <= hd
     then Cons i l
     else let i_tl = insert i tl in 
          let (Cons z _) = i_tl in
          sorted_smaller hd z tl; (* need to call the lemma explicitly, currently *)
          Cons hd i_tl

               
(* Insertion sort *)
val sort : l:intlist -> Tot (m:intlist{sorted m /\ (forall x. mem x l == mem x m)})
let rec sort l = match l with
    | Nil -> Nil
    | Cons x xs -> insert x (sort xs)
