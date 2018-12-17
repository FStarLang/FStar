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
module Tuples

val split: list ('a * 'b) -> Tot (list 'a * list 'b)
let rec split l =
  match l with
  | [] -> ([], [])
  | (hd1, hd2) :: tl ->
    let tl1, tl2 = split tl in
    (hd1 :: tl1, hd2 :: tl2)

val unzip3: list ('a * 'b * 'c) -> Tot (list 'a * list 'b * list 'c)
let rec unzip3 l =
  match l with
  | [] -> ([], [], [])
  | (hd1, hd2, hd3) :: tl ->
    let tl1, tl2, tl3 = unzip3 tl in
    (hd1 :: tl1, hd2 :: tl2, hd3 :: tl3)

val l_unzip3: list (('a * 'b) * 'c) -> Tot ((list 'a * list 'b) * list 'c)

val r_unzip3: list ('a * ('b * 'c)) -> Tot (list 'a * (list 'b * list 'c))

val unzip4: list ('a * 'b * 'c * 'd) -> Tot (list 'a * list 'b * list 'c * list 'd)

val zip3: #a1: Type -> #a2: Type -> #a3: Type -> l1: list a1 -> l2: list a2 -> l3: list a3 ->
  Pure (list ((a1 * a2) * a3))

let ccc: nat * (string * int) = (123 <: nat), bbb

val a: ((a * (b * (c * d * (e * f) * g)) * h) * (i * j))

let m2 = fun x y -> x * y

let m3 = fun x y z -> x * y * z

let mul_mod #n a b = (a * b * c) @% (pow2 n)

let mul_mod #n a b = (a * (b * c)) @% (pow2 n)

let mul_mod #n a b = ((a * b) * c) @% (pow2 n)

