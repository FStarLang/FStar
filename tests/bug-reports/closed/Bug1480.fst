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
module Bug1480

type even (a:Type) =
  | Nil : even a
  | ECons : a -> odd a -> even a
and odd (a:Type) =
  | OCons : a -> even a -> odd a

let rec elength (#a:Type u#a) (x:even a)
  : nat
  = match x with
    | Nil -> 0
    | ECons _ o -> 1 + olength o
and olength (#a:Type u#a) (x:odd a)
  : nat
  = let OCons _ e = x in
    1 + elength e

let rec elength' (#a:Type) (x:even a)
  : nat
  = match x with
    | Nil -> 0
    | ECons _ o -> 1 + olength' o
and olength' (#a:Type) (x:odd a)
  : nat
  = let OCons _ e = x in
    1 + elength' e

//g is universe polymorphic but f is not
[@@expect_failure [89]]
let rec f (x:nat) : nat =
    if x > 0
    then f (x-1)
    else 42
and g y = ()

let rec x (t: Type u#a) (l: list t) : Tot (Type u#(a + 1)) =
  match l with
  | [] → Type u#a
  | z :: q → y t q
and y (t: Type u#a) (l: list t) : Tot (Type u#(a + 1)) =
  match l with
  | [] → Type u#a
  | z :: q → x t q

type tree a =
  | Leaf of a
  | Branch of list (tree a)

assume
val append (l0 l1 : list 'a) : list 'a

let rec flatten' (#a:Type u#a) (t:tree a) : list a =
  match t with
  | Leaf v   -> [v]
  | Branch l -> flatten_l u#a l
and flatten_l (#a:Type u#a) (l:list (tree a)) : list a =
  match l with
  | []    -> []
  | hd::tl -> append (flatten' hd) (flatten_l u#a tl)
