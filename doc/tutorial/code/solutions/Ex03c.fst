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
module Ex03c
//fibonacci-property

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// BEGIN: FibonacciGreaterThanArgProof
let rec fibonacci_greater_than_arg n =
  match n with
  | 2 -> ()
  | _ -> fibonacci_greater_than_arg (n-1)

(*
 The proof uses the induction hypothesis:
   forall x, 2 <= x < n ==> fibonacci x >= x

 Z3 proves the base case, when n=2.

 Our remaining goal is to prove that for n >= 3
  fibonacci n >= n or equivalently fibonacci (n-1) + fibonacci (n-2) > n

 From the induction hypothesis we have,
   fibonacci(n - 1) >= n - 1

 To conclude, it suffices to prove that prove that fibonacci(n - 2) >= 1.

 Z3 is able to prove this as follows:

 We have: fibonacci(n - 1) = fib (n - 2) + fib (n - 3) >= n - 1 > 1

 Assume, for contradiction, that fibonacci (n - 2) = 0.
   Then fibonacci (n - 3) > 1. (H)

   If n = 3, then fibonacci(n - 2) = fibonacci(1) = 1. Which is a contradiction.

   If n > 3, then
     0 = //by assumption
     fibonacci (n - 2) = //by definition
     fibonacci (n - 3) + fibonacci (n - 4) >= //since fibonacci(n-4) : nat >= 0
     fibonacci (n - 3) > //by (H), above
     1

   So, we have a contradiction.

 So fibonacci (n - 2) >= 1
*)

// END: FibonacciGreaterThanArgProof
