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
module Ex05b
//fibonacci-is-ok

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fib : nat -> nat -> n:nat -> Tot nat (decreases n)
let rec fib a b n =
  match n with
  | 0 -> a
  | _ -> fib b (a+b) (n-1)

val fib_is_ok_aux : i:nat -> n:nat{i<=n} ->
      Tot (u:unit{fib (fibonacci i) (fibonacci (i+1)) (n-i) = fibonacci n})
      (decreases (n-i))
let rec fib_is_ok_aux i n =
  if i=n then ()
  else fib_is_ok_aux (i+1) n

val fib_is_ok : n:nat -> Lemma (fib 1 1 n = fibonacci n)
let fib_is_ok n = fib_is_ok_aux 0 n

(* You can write nested recursive functions, as you'd expect *)
val fib_inner_aux : nat -> Tot nat
let fib_inner_aux n =
  let rec aux : a:nat -> b:nat -> n:nat -> Tot nat (decreases n) =
    fun a b n -> match n with
      | 0 -> a
      | _ -> aux b (a + b) (n - 1) in
  aux 1 1 n

(* But, proving that the nested aux correctly computes fibonacci is
   hard, because you can't get you can't get your hands on that
   nested recursive aux function.
   Here's one way to do it. *)

#set-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 0 --max_ifuel 0"

val fib_inner_aux_2: n:nat -> Tot (f:nat{f = fibonacci n})
let fib_inner_aux_2 n =
  let rec aux: a:nat -> b:nat -> k:nat{k <= n} -> Tot
    (m:nat{a = fibonacci (n - k) /\ b = fibonacci (n - k + 1) ==> m = fibonacci n})
    (decreases k) =
  fun a b -> function
  | 0 -> a
  | k -> aux b (a + b) (k - 1)
  in
  aux 1 1 n
