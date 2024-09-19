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
module FStar.Tactics.Util

open FStar.Tactics.Effect
open FStar.List.Tot.Base

(* Tac list functions, since there's no effect polymorphism *)
val map: ('a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

let rec concatMap (f : 'a -> Tac (list 'b)) (l : list 'a) : Tac (list 'b) =
  match l with
  | [] -> []
  | x::xs -> f x @ concatMap f xs

val __mapi: nat -> (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
let rec __mapi i f x = match x with
  | [] -> []
  | a::tl -> f i a::__mapi (i+1) f tl

val mapi: (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
let mapi f l = __mapi 0 f l

val iter : ('a -> Tac unit) -> list 'a -> Tac unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> f a; iter f tl

val iteri_aux: int -> (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

val iteri: (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let iteri f x = iteri_aux 0 f x

val fold_left: ('a -> 'b -> Tac 'a) -> 'a -> l:list 'b -> Tac 'a
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_right: ('a -> 'b -> Tac 'b) -> list 'a -> 'b -> Tac 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(* There's no unconditionally total zip like this in Tot.Base, why? Anyway use this *)
val zip : (#a:Type) -> (#b:Type) -> list a -> list b -> Tac (list (a & b))
let rec zip #a #b l1 l2 = match l1, l2 with
    | x::xs, y::ys -> (x,y) :: (zip xs ys)
    | _ -> []

val filter: ('a -> Tac bool) -> list 'a -> Tac (list 'a)
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

private let rec filter_map_acc (f:'a -> Tac (option 'b)) (acc:list 'b) (l:list 'a)
    : Tac (list 'b) =
  match l with
  | [] ->
      rev acc
  | hd :: tl ->
      match f hd with
      | Some hd ->
          filter_map_acc f (hd :: acc) tl
      | None ->
          filter_map_acc f acc tl

let filter_map (f:'a -> Tac (option 'b)) (l:list 'a) : Tac (list 'b) =
  filter_map_acc f [] l

val tryPick: ('a -> Tac (option 'b)) -> list 'a -> Tac (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

let map_opt (f:'a -> Tac 'b) (x:option 'a) : Tac (option 'b) =
  match x with
  | None -> None
  | Some x -> Some (f x)

(** Apply a given tactic [t] repeatedly [n] times and return the results. *)
let rec repeatn (#a:Type) (n : int) (t : unit -> Tac a) : Tac (l:list a{n < 0 \/ length l == n}) =
    if n <= 0
    then []
    else t () :: repeatn (n - 1) t

let rec tryFind (#a:Type) (f:a -> Tac bool) (l:list a) : Tac bool =
  match l with
  | [] -> false
  | hd::tl ->
    if f hd then true
    else tryFind f tl

let rec fold_left2 (#a #b #c:Type) (f:a -> b -> c -> Tac a) (x:a) (l1:list b) (l2:list c)
  : TacH a
      (requires fun _ -> length l1 == length l2)
      (ensures fun _ _ -> True) =
  match l1, l2 with
  | [], [] -> x
  | hd1::tl1, hd2::tl2 ->
    fold_left2 f (f x hd1 hd2) tl1 tl2

let rec string_of_list #a (f : a -> Tac string) (l : list a) : Tac string =
  match l with
  | [] -> ""
  | x::xs -> f x ^ ";" ^ string_of_list f xs

let string_of_option #a (f : a -> Tac string) (o : option a) : Tac string =
  match o with
  | Some x -> "Some " ^ f x
  | None -> "None"
