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
module Bug058

(* Write the fibonacci function and several types for it. *)
val fibonacci: (x:int{x>=0}) -> Tot (y:int{y>=0})

let fibonacci x =
   let rec sub_fibo : n:nat{n <= x}  -> nat -> nat -> Tot nat (decreases (x-n)) =
     fun n -> fun acc1 -> fun acc2 ->
         if n = x
         then (acc1 + acc2)
         else sub_fibo (n+1) acc2 (acc1 + acc2)
   in

  if x <= 1
  then 1
  else sub_fibo 2 1 1
