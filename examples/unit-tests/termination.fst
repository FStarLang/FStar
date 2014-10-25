(* Expect 3 intentional failures *)

(*
   Copyright 2008-2014 Nikhil Swamy, Chantal Keller, Microsoft Research and Inria

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
module Termination

val factorial: nat -> Tot nat
let rec factorial x =
  match x with
    | 0 -> 1
    | _ -> (x + factorial (x - 1))

val fibonacci: nat -> Tot nat
let rec fibonacci n =
  if n<=1 then 1
  else fibonacci (n - 1) + fibonacci (n - 2)

val ackermann: m:nat -> n:nat -> Tot nat
let rec ackermann m n =
  if m=0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

val ackermann_bad: m:int -> n:int -> Tot int
let rec ackermann_bad m n = (* expected failure *)
  if m=0 then n + 1
  else if n = 0 then ackermann_bad (m - 1) 1
  else ackermann_bad (m - 1) (ackermann_bad m (n - 1))

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _::tl -> 1 + length tl

val length_bad: list 'a -> Tot nat
let rec length_bad l = match l with (* expect failure *)
  | [] -> 0
  | _::tl -> 1 + length_bad l

val half_length: list 'a -> Tot nat
let rec half_length l = match l with
  | [] -> 0
  | [_] -> 0
  | _::_::tl -> 1 + half_length tl (* testing transitivity of ordering *)


(***** Coq-Club example *****)
val sumto: i:nat -> f:(x:nat{x <= i} -> Tot nat) -> Tot nat
let rec sumto i f =
  if i = 0
  then f 0
  else f i + sumto (i-1) f

val strangeZero: nat -> Tot nat
let rec strangeZero v =
  if v = 0
  then 0
  else sumto (v-1) strangeZero

val strangeZeroBad: nat -> Tot nat
let rec strangeZeroBad v = (* expect failure *)
  if v = 0
  then 0
  else sumto v strangeZeroBad
    
val map : ('a -> Tot 'b) -> list 'a -> list 'b
let rec map f l = match l with
  | [] -> []
  | hd::tl -> f hd::map f tl

val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val move_refinement: 'a:Type
                   -> 'P:('a => Type) 
                   -> l:list 'a{forall x. mem x l ==> 'P x} 
                   -> Tot (list (x:'a{'P x}))
let rec move_refinement 'a 'P l = match l with 
  | [] -> [] 
  | hd::tl -> hd::(move_refinement 'a 'P tl)


(* type T 'a = *)
(*   | Leaf : 'a -> T 'a *)
(*   | Node : list (T 'a) -> T 'a *)

(* Doesn't work yet ... *)
(* val treeMap : ('a -> Tot 'b) -> T 'a -> Tot (T 'b) *)
(* let rec treeMap f v = match v with *)
(*   | Leaf a -> Leaf (f a) *)
(*   | Node l ->  *)
(*     let l = move_refinement 'a (fun a => Precedes (LexPair f a) (LexPair f v)) l in *)
(*     Node (map (treeMap f) l) (\* doesn't work yet *\) *)
