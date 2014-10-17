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


(*
   Termination checking is not yet implemented. 
   A let rec with an explicitly annotated "Tot" effect is admitted. 
   Without such an annotation, the inferred effect is "All" 
*)

module Recursion
open Prims.PURE
(*ghost*) effect Fact ('p:Type) = Pure unit True (fun r => 'p)

type z = i:int{i==0}

val zero: list 'a -> Tot z
let rec zero l = match l with
  | [] -> 0
  | hd::tl -> zero tl

val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | hd::tl -> 1 + length tl

val mem: 'a -> list 'a -> Tot bool
let rec mem a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val append: l1:list 'a -> l2:list 'a -> Tot (l3:list 'a{length l3 == length l1 + length l2})
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd::tl -> hd::append tl l2

(* val append_mem:  l1:list 'a  *)
(*               -> l2:list 'a  *)
(*               -> a:'a  *)
(*               -> Fact (b2t (mem a (append l1 l2)) <==>  b2t (mem a l1) \/ b2t(mem a l2)) *)
(* let rec append_mem l1 l2 a = match l1 with  *)
(*   | [] -> assert (append l1 l2 == l2) *)
(*   | hd::tl ->  *)
(*     if hd=a *)
(*     then () *)
(*     else append_mem tl l2 a  *)
  
