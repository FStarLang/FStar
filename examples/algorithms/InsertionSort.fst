(*
   Copyright 2008-2014 Nikhil Swamy, Chantal Keller, Catalin Hritcu

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
open FStar.List.Tot
open IntSort

(* Explicitly calling sorted_smaller lemma
   (otherwise verification takes a lot longer) *)
val insert : i:int -> l:list int{sorted l} ->
      Tot (m:list int{sorted m /\ permutation (i::l) m})
let rec insert i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else let i_tl = insert i tl in 
          let (z::_) = i_tl in
          if mem z tl then sorted_smaller hd z tl;
          hd::i_tl

(* Solver implicitly uses the lemma: sorted_smaller hd (Cons.hd i_tl) tl *)
val insert_implicit : i:int -> l:list int{sorted l} ->
      Tot (m:list int{sorted m /\ permutation (i::l) m})
let rec insert_implicit i l = match l with
  | [] -> [i]
  | hd::tl ->
     if i <= hd then i::l
     else hd::(insert_implicit i tl)

(* Insertion sort *)
val sort : l:list int -> Tot (m:list int{sorted m /\ permutation l m})
let rec sort l = match l with
    | [] -> []
    | x::xs -> insert x (sort xs)
