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


module Max
val max : i:int -> j:int -> k:int{k >= i /\ k >= j /\ (k == i \/ k == j)}
let max i j = if i < j then j else i

val max2 : nat -> nat -> Tot nat
let max2 i j = if i < j then j else i

val max2_spec : i:nat -> j:nat -> Tot (u:unit{max2 i j >= i /\ max2 i j >= j /\ (max2 i j == i \/ max2 i j == j)})
let max2_spec i j = ()


module HO

val f : ('a -> 'b) -> ('a -> 'c) -> 'a -> 'b * 'c
(* val f : g:('a -> 'b) -> h:('a -> 'b){forall (y:'a), g y = h y} -> 'a -> r:('b * 'c){fst r == snd r} *)
let f g h x = (g x, h x)


module List

val length : list 'a -> nat
let rec length l = match l with
    | [] -> 0
    | _::xs -> 1 + (length xs)

val nth : int -> list 'a -> 'a
let rec nth n l = match l with
    | [] -> failwith "Not enough elements"
    | x::xs -> if n = 0 then x else nth (n-1) xs




module Effects

(* val incr : unit -> All int (fun 'p h => True) *)
let incr () =
  let x = ST.alloc 0 in
  ST.write x 1;
  ST.read x
