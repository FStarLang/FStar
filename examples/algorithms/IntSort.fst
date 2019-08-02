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
module IntSort
open FStar.List.Tot

(* Check that a list is sorted *)
val sorted: list int -> Tot bool
let rec sorted l = match l with
    | [] | [_] -> true
    | x::y::xs -> (x <= y) && (sorted (y::xs))

val test_sorted: x:int -> l:list int ->
      Lemma ((sorted (x::l) /\ Cons? l) ==> x <= Cons?.hd l)
let test_sorted x l = ()

val test_sorted2: unit -> Tot (m:list int{sorted m})
let test_sorted2 () = Nil


(* Fact about sorted *)
val sorted_smaller: x:int
                ->  y:int
                ->  l:list int
                ->  Lemma (requires (sorted (x::l) /\ mem y l))
                          (ensures (x <= y))
                          [SMTPat (sorted (x::l)); SMTPat (mem y l)]
let rec sorted_smaller x y l = match l with
    | [] -> ()
    | z::zs -> if z=y then () else sorted_smaller x y zs


type permutation (l1:list int) (l2:list int) =
    length l1 = length l2 /\ (forall n. mem n l1 = mem n l2)

type permutation_2 (l:list int) (l1:list int) (l2:list int) =
    (forall n. mem n l = (mem n l1 || mem n l2)) /\
    length l = length l1 + length l2
