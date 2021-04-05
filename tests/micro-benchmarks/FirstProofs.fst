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
module FirstProofs
open FStar.Mul

val factorial: nat -> Tot nat
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

val factorial_is_positive: x:nat -> Lemma (factorial x > 0)
let rec factorial_is_positive = function
  | 0 -> ()
  | x -> factorial_is_positive (x - 1)

val factorial_is_increasing: x:nat{x >= 2} -> Lemma (factorial x >= x)
let rec factorial_is_increasing = function
  | 2 -> ()
  | x -> factorial_is_increasing (x - 1)

//As we move to non-linear arithmetic, we need to give the solver more time
#set-options "--z3rlimit 25 --max_fuel 4 --initial_fuel 4 --max_ifuel 0"
val factorial_is_doubling: x:nat{x >= 3} -> Lemma (factorial x >= 2 * x)
let rec factorial_is_doubling x = match x with
  | 3 -> ()
  | x -> factorial_is_doubling (x - 1)

(* These next two are already getting too unpredictable with Z3's
   non-linear theory. You can try to provide an more explicit proof
   using FStar.Math.Lemmas *)

(* #set-options "--z3rlimit 100 --max_fuel 5 --initial_fuel 5 --max_ifuel 0" *)
(* val factorial_is_squaring: x:nat{x >= 4} -> Lemma (factorial x > x * x) *)
(* let rec factorial_is_squaring = function *)
(*   | 4 -> () *)
(*   | x -> factorial_is_squaring (x - 1) *)

(* #set-options "--z3rlimit 100 --max_fuel 7 --initial_fuel 7 --max_ifuel 0" *)
(* val factorial_is_cubing: x:nat{x > 5} -> Tot (u:unit{factorial x >= x * x * x}) *)
(* let rec factorial_is_cubing = function *)
(*   | 6 -> () *)
(*   | x -> factorial_is_cubing (x - 1) *)

#reset-options
val fibonacci: nat -> Tot nat
let rec fibonacci = function
  | 0
  | 1 -> 1
  | n -> fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_is_increasing: n:nat -> Lemma (fibonacci n >= n)
let rec fibonacci_is_increasing n = if n > 1 then fibonacci_is_increasing (n - 1) else ()
