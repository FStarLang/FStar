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
module Bug058b

(* Write the fibonacci function and several types for it. *)

val sub_fibo : x:nat -> n:int{n >0 /\ n <= x}  -> int -> int -> Tot int (decreases (x-n))
let rec sub_fibo x n acc1 acc2 =
  if n = x
  then (acc1 + acc2)
  else sub_fibo x (n+1) acc2 (acc1 + acc2)

val fibonacci: (x:int{x>=0}) -> Tot int
let fibonacci x =
  if x <= 1
  then 1
  else sub_fibo x 2 1 1
