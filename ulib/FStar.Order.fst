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
module FStar.Order

type order = | Lt | Eq | Gt

// Some derived checks
val ge : order -> bool
let ge o = o <> Lt

val le : order -> bool
let le o = o <> Gt

val ne : order -> bool
let ne o = o <> Eq

// Just for completeness and consistency...
val gt : order -> bool
let gt o = o = Gt

val lt : order -> bool
let lt o = o = Lt

val eq : order -> bool
let eq o = o = Eq

// Lexicographical combination, thunked to be lazy
val lex : order -> (unit -> order) -> order
let lex o1 o2 =
    match o1 with
    | Lt -> Lt
    | Eq -> o2 ()
    | Gt -> Gt

val order_from_int : int -> order
let order_from_int i =
    if i < 0 then Lt
    else if i = 0 then Eq
    else Gt

val int_of_order : order -> int
let int_of_order = function
    | Lt -> (-1)
    | Eq -> 0
    | Gt -> 1

val compare_int : int -> int -> order
let compare_int i j = order_from_int (i - j)

val compare_list : ('a -> 'a -> order) -> list 'a -> list 'a -> order
let rec compare_list f l1 l2 =
    match l1, l2 with
    | [], [] -> Eq
    | [], _ -> Lt
    | _, [] -> Gt
    | x::xs, y::ys -> lex (f x y) (fun () -> compare_list f xs ys)

val compare_option : ('a -> 'a -> order) -> option 'a -> option 'a -> order
let compare_option f x y =
    match x, y with
    | None   , None   -> Eq
    | None   , Some _ -> Lt
    | Some _ , None   -> Gt
    | Some x , Some y -> f x y
