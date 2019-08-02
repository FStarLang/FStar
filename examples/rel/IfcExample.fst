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
module IfcExample

open Rel
open While
open IfcRules
open FStar.Heap
open FStar.ST

(* (Warning) Top-level let-bindings must be total; this term may have effects *)

assume val x : ref int 
assume val y : ref int 
assume val z : ref int 
assume val c : ref int 

let env (var: nat) = 
  if var = addr_of x then Low
  else if var = addr_of y then Low 
    else if var = addr_of c then Low
      else if var = addr_of z then High
        else High

(* 
  While c > 0{
    x := y; 
    y := y + 6;
    z := y + 7;
    x := z + 7;
    c := c - 1 
  }
*)


let c1_0 body = While (AVar c) body (AVar c)
let c1_1 = Assign x (AVar y)
let c1_2 = Assign y (AOp Plus (AVar x) (AInt 6))
let c1_3 = Assign z (AOp Plus (AVar y) (AInt 7))
let c1_4 = Assign x (AOp Plus (AVar z) (AInt 7))
let c1_5 = Assign c (AOp Minus (AVar c) (AInt 1))
let c1_6 = Seq c1_1 (Seq c1_2 (Seq c1_3 (Seq c1_4 c1_5)))

let c1 = c1_0 c1_6

val c1_1_ni : unit -> Lemma (ni_com env c1_1 Low)
let c1_1_ni () = ()

val c1_2_ni : unit -> Lemma (ni_com env c1_2 Low)
let c1_2_ni () = ()

val c1_3_ni : unit -> Lemma (ni_com env c1_3 Low)
let c1_3_ni () = ()

(* c1_4 cannot be shown to be non-interferent by typing since it contains an
   explicict flow from z (High) to x (Low)
   However, the sequence of c1_3 and c1_4 is fine, since in c1_3 we overwrite 
   z with the low value (y+7). 
   We can hene prove non-interference by relying on SMT.
   *)
val c1_3_4_ni : unit -> Lemma (ni_com env (Seq c1_3 c1_4) Low)
let c1_3_4_ni () = ()


(* The SMT solver cannot show noninterference of the loop without further
   guidance, so we rely on the While-rule instead *)
val c1_ni : unit -> Lemma (ni_com env c1 Low)
let c1_ni () = while_com env (AVar c) c1_6 (AVar c) Low
