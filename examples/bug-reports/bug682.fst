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
module Bug682

type vec (a: Type): nat -> Type =
  | Nil: vec a 0
  | Cons: hd:a -> n:nat -> tl:vec a n -> vec a (n + 1)

(* The following snippet doesn't work: *)

val map2:
  n:nat ->
  f:('a -> 'b -> Tot 'c) ->
  l1:vec 'a n ->
  l2:vec 'b n ->
  Tot (vec 'c n)
let rec map2 n f l1 l2 =
  match l1, l2 with
  | Cons hd1 n1 tl1, Cons hd2 n2 tl2 ->
      Cons (f hd1 hd2) n1 (map2 n1 f tl1 tl2)
  | Nil, Nil ->
      Nil

(* ./bug682.fst(17,4-17,8) : (Error) (?41694 'a 'b 'c n f l1 l2) is not equal to the expected type (Bug682.vec (?41538 'a 'b 'c n f l1 l2) (Prims.op_Addition n1 1)) *)

(* The following snippet does work: *)

val map2':
  n:nat ->
  f:('a -> 'b -> Tot 'c) ->
  l1:vec 'a n ->
  l2:vec 'b n ->
  Tot (vec 'c n)
let rec map2' n f l1 l2 =
  match l1 with
  | Cons hd1 n1 tl1 ->
      begin match l2 with
      | Cons hd2 n2 tl2 ->
          Cons (f hd1 hd2) n2 (map2' n2 f tl1 tl2)
      end
  | Nil ->
      begin match l2 with
      | Nil ->
          Nil
      end
