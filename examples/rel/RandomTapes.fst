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
module RandomTapes

open Rel
open Bijection

(* Experimenting with random tapes *)

type random_tape = int -> Tot int

val sample : random_tape -> int -> Tot int
let sample r i =  r i

type rel_random_tape (b:(int -> Tot bij)) = r:(rel random_tape){forall i. b i (R?.l r i) = R?.r r i}

val id : bij #int #int 
let id x = x 

val minus : int -> int -> Tot int
let minus x y = y - x

  (* Proving the function used is a bijection *)
val add : int -> Tot (bij #int #int)
let add x = cut (inverses (op_Addition x) (minus x)); op_Addition x 

  (* Definition of a simple one time pad *)
val otp : int -> random_tape -> int -> Tot int
let otp n r i = n + r i

  (* Random tape used for relational verification *)
val otp_rand : x:(rel int) -> int -> Tot (bij #int #int)
let otp_rand x i = if i = 0 then 
                     add (R?.l x - R?.r x)
                   else 
                     id

  (* otp perfectly hides input *)
val otp_eq : x:(rel int) -> r:(rel_random_tape (otp_rand x)) ->
            Lemma (r_eq(lift3 otp x r (R 0 0)))
let otp_eq x r = ()

  (* Same thing for a pair of values *)
val otp2 : int -> int -> random_tape -> int -> int -> Tot (int * int)
let otp2 n m r i j = (n + r i, m + r j)

val otp2_rand : x:(rel int) -> y:(rel int) -> int -> Tot (bij #int #int)
let otp2_rand x y i = 
  match i with
  | 0 -> add (R?.l x - R?.r x)
  | 1 -> add (R?.l y - R?.r y)
  | _ -> id

val otp2_eq : x:(rel int) -> y:(rel int) -> r:(rel_random_tape (otp2_rand x y)) ->
            Lemma (r_eq(lift5 otp2 x y r (R 0 0) (R 1 1)))
let otp2_eq x y r = ()
