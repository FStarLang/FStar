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
(* ******************************************************************************** *)
module NegativeTests.Termination
val bug15 : m : int -> Tot (z : int ->
            Lemma (ensures (False)))
[@ (expect_failure [19])]
let rec bug15 m l = bug15 m l

val repeat_diverge : int -> int -> Tot int
[@ (expect_failure [19])]
let rec repeat_diverge n count =
  match count with
  | 0 -> 0
  | _ -> repeat_diverge n (count-1)


val ackermann_bad: m:int -> n:int -> Tot int
[@ (expect_failure [19])]
let rec ackermann_bad m n = (* expected failure *)
  if m=0 then n + 1
  else if n = 0 then ackermann_bad (m - 1) 1
  else ackermann_bad (m - 1) (ackermann_bad m (n - 1))

val length_bad: list 'a -> Tot nat
[@ (expect_failure [19])]
let rec length_bad l = match l with (* expect failure *)
  | [] -> 0
  | _::tl -> 1 + length_bad l

val sumto: i:nat -> f:(x:nat{x <= i} -> Tot nat) -> Tot nat
let rec sumto i f =
  if i = 0
  then f 0
  else f i + sumto (i-1) f

val strangeZeroBad: nat -> Tot nat
[@ (expect_failure [19])]
let rec strangeZeroBad v = (* expect failure *)
  if v = 0
  then 0
  else sumto v strangeZeroBad

type snat =
  | O : snat
  | S : snat -> snat

val t1 : snat -> Tot bool
[@ (expect_failure [19])]
let rec t1 n =
  match n with
  | O        -> true
  | S O      -> false
  | S (S n') -> t1 (S (S n')) //termination check should fail

val plus : snat -> snat -> Tot snat
[@ (expect_failure [19])]
let rec plus n m =
  match n with
    | O -> m
    | S O -> m
    | S (S n') -> plus (S (S n')) m //termination check should fail

val plus' : snat -> snat -> Tot snat
[@ (expect_failure [19])]
let plus' n m =
  match n with //patterns are incomplete
    | O -> m
    | S O -> m

val minus : snat -> snat -> Tot snat
[@ (expect_failure [19])]
let rec minus (n : snat) (m : snat) : snat =
  match n, m with
  | O   , _    -> O
  | S n', m' -> minus (S n') m' //termination check should fail

val xxx : snat -> Tot snat
[@ (expect_failure [19])]
let rec xxx (n : snat) : snat =
  match n, 42 with
  | O, 42   -> O
  | S n', 42 -> xxx (S n')


(* ******************************************************************************** *)
