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
module FStar.Class.TotalOrder.Raw

open FStar.Order

let flip = function
  | Lt -> Gt
  | Eq -> Eq
  | Gt -> Lt

let raw_comparator (a:Type) = a -> a -> order

class totalorder (a:Type) = {
  compare : raw_comparator a;
}

val (<) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<) x y = compare x y = Lt

val (>) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (>) x y = compare x y = Gt

val (=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (=) x y = compare x y = Eq

val (<=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<=) x y = compare x y <> Gt

val (>=) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (>=) x y = compare x y <> Lt

val (<>) : #t:Type -> {|totalorder t|} -> t -> t -> bool
let (<>) x y = compare x y <> Eq

instance _ : totalorder int = {
  compare = Order.compare_int;
}

instance _ : totalorder bool = {
  compare = (fun b1 b2 -> match b1, b2 with | false, false | true, true -> Eq | false, _ -> Lt | _ -> Gt);
}

(* Lex order on tuples *)
instance totalorder_pair #a #b (d1 : totalorder a) (d2 : totalorder b) : totalorder (a & b) = {
  compare = (fun (xa,xb) (ya, yb) ->
    match compare xa ya with
    | Lt -> Lt
    | Gt -> Gt
    | Eq -> compare xb yb);
}

instance totalorder_option #a (d : totalorder a) : totalorder (option a) = {
  compare = (fun o1 o2 -> match o1, o2 with
    | None, None -> Eq
    | None, Some _ -> Lt
    | Some _, None -> Gt
    | Some a1, Some a2 -> compare a1 a2);
}

let rec raw_compare_lists #a (d : totalorder a) : raw_comparator (list a) =
  fun l1 l2 ->
    match l1, l2 with
    | [], [] -> Eq
    | [], _::_ -> Lt
    | _::_, [] -> Gt
    | x::xs, y::ys ->
        match compare x y with
        | Lt -> Lt
        | Gt -> Gt
        | Eq -> raw_compare_lists d xs ys

instance totalorder_list #a (d : totalorder a) : totalorder (list a) = {
  compare = raw_compare_lists d;
}
