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
module PrettyPrinter

open FStar.Regions.RST
open FStar.Regions.RSTArray
open ArrayAlgos

open StackAndHeap
open Stack

open FStar.Regions.Heap
open FStar.Regions.Located

open FStar.Ghost

(* Missing definitions from F* *)
assume val string_of_int : int -> Tot string
assume val random_nat: y:nat -> Tot (x:nat{0 <= x /\ x < y})


type expr =
| Add: expr -> expr -> expr
| Sub: expr -> expr -> expr
| Mul: expr -> expr -> expr
| Div: expr -> expr -> expr
| Const: int -> expr


let rec print_add = function
  | Add e1 e2 ->
      print_add e1 ^ " + " ^ print_add e2
  | Sub e1 e2 ->
      print_add e1 ^ " - " ^ print_mul e2
  | e ->
      print_mul e

and print_mul = function
  | Mul e1 e2 ->
      print_mul e1 ^ " * " ^ print_mul e2
  | Div e1 e2 ->
      print_mul e1 ^ " / " ^ print_atomic e2
  | e ->
      print_atomic e

and print_atomic = function
  | Const i ->
      string_of_int i
  | e ->
      "(" ^ print_ e ^ ")"

and print_ e =
  print_add e


(* -------------------------------------------------------------------------- *)

let max = 22

let rec gen h =
  if h = 1 then
    Const (random_nat max)
  else match random_nat 4 with
  | 0 -> Add (gen (h - 1)) (gen (h - 1))
  | 1 -> Sub (gen (h - 1)) (gen (h - 1))
  | 2 -> Mul (gen (h - 1)) (gen (h - 1))
  | 3 -> Div (gen (h - 1)) (gen (h - 1))


let _main =
  let e = gen max in
  let s = print_ e in
  ignore s
