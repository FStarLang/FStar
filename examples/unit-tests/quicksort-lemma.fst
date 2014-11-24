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


module IntList_QuickSortLemma
open Prims.PURE

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

(* Fact about sorted *)
val mem: int -> list int -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val cons_sorted:
  l:list int -> i:int ->
    Lemma (requires (sorted l) /\ (forall x. mem x l ==> x > i))
          (ensures (sorted (i::l)))
let rec cons_sorted l i = match l with
    | [] -> ()
    | x::xs -> cons_sorted xs i

val cons_mem:
  l:list int -> i:int -> j:int ->
    Lemma (ensures (mem j (i::l) <==> ((mem j l) \/ (j == i))))
let rec cons_mem l i j = match l with
    | [] -> ()
    | x::xs -> if j = i then () else cons_mem xs x j

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
    | [] -> []
    | x::xs -> x::(append xs l2)

val append_sorted:
  l1: list int -> l2: list int ->
    Lemma (requires (sorted l1 /\ (sorted l2)))
          (ensures (sorted (append l1 l2)))
          [SMTPat (sorted l1); SMTPat (sorted l2)]
let rec append_sorted l1 l2 = match l1 with
    | [] -> ()
    | x::xs -> append_sorted xs l2

val append_mem:
  l1: list int -> l2: list int -> i: int ->
    Lemma (ensures ((mem i (append l1 l2)) <==> ((mem i l1) \/ (mem i l2))))
let rec append_mem l1 l2 i = match l1 with
    | [] -> ()
    | x::xs -> if x = i then () else append_mem xs l2 i

val split: i:int -> l:list int -> Tot (list int * list int)
let rec split i l = match l with
    | [] -> ([],[])
    | x::xs ->
       let (xs1,xs2) = split i xs in
       if x <= i then
         (x::xs1,xs2)
       else
         (xs1,x::xs2)

val split_mem:
  j:int -> l:list int -> i:int ->
    Lemma (ensures (mem i l <==> ((mem i (fst (split j l))) \/ (mem i (snd (split j l))))))
let rec split_mem j l i = match l with
    | [] -> ()
    | x::xs -> if x = i then () else split_mem j xs i

(* Quick sort *)
val sort : list int -> list int
let rec sort l = match l with
    | [] -> []
    | x::xs ->
       let (xs1,xs2) = split x xs in
       append (sort xs1) (x::(sort xs2))

(* val sort_mem: *)
(*   l:list int -> i:int -> *)
(*     Lemma (ensures (mem i l) <==> (mem i (sort l))) *)
(* let rec sort_mem l i = match l with *)
(*     | [] -> [] *)
(*     | x::xs -> *)
(*        let (xs1,xs2) = split x xs in *)
(*        if i = x then *)
(*          () *)
(*        else ( *)
(*          sort_mem xs1 i; *)
(*          sort_mem xs2 i *)
(*        ) *)
