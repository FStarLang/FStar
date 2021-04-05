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
open FStar.List.Tot

#set-options "--z3rlimit 25 --fuel 0 --ifuel 0"

(* Tac list functions, since there's no effect polymorphism *)
val map: ('a -> Tac 'b) -> list 'a -> Tac (list 'b)
#push-options "--ifuel 1"
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl
#pop-options

val __mapi: nat -> (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
#push-options "--ifuel 1"
let rec __mapi i f x = match x with
  | [] -> []
  | a::tl -> f i a::__mapi (i+1) f tl
#pop-options

val mapi: (nat -> 'a -> Tac 'b) -> list 'a -> Tac (list 'b)
let mapi f l = __mapi 0 f l

val iter : ('a -> Tac unit) -> list 'a -> Tac unit
#push-options "--ifuel 1"
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> f a; iter f tl
#pop-options

val iteri_aux: int -> (int -> 'a -> Tac unit) -> list 'a -> Tac unit
#push-options "--ifuel 1"
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl
#pop-options

val iteri: (int -> 'a -> Tac unit) -> list 'a -> Tac unit
let iteri f x = iteri_aux 0 f x

val fold_left: ('a -> 'b -> Tac 'a) -> 'a -> l:list 'b -> Tac 'a
#push-options "--ifuel 1"
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl
#pop-options

val fold_right: ('a -> 'b -> Tac 'b) -> list 'a -> 'b -> Tac 'b
#push-options "--ifuel 1"
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)
#pop-options

(* There's no unconditionally total zip like this in Tot.Base, why? Anyway use this *)
val zip : (#a:Type) -> (#b:Type) -> list a -> list b -> Tac (list (a * b))
#push-options "--ifuel 1"
let rec zip #a #b l1 l2 = match l1, l2 with
    | x::xs, y::ys -> (x,y) :: (zip xs ys)
    | _ -> []
#pop-options

val filter: ('a -> Tac bool) -> list 'a -> Tac (list 'a)
#push-options "--ifuel 1"
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl
#pop-options

#push-options "--ifuel 1"
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
#pop-options

let filter_map (f:'a -> Tac (option 'b)) (l:list 'a) : Tac (list 'b) =
  filter_map_acc f [] l

val tryPick: ('a -> Tac (option 'b)) -> list 'a -> Tac (option 'b)
#push-options "--ifuel 1"
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl
#pop-options

let map_opt (f:'a -> Tac 'b) (x:option 'a) : Tac (option 'b) =
  match x with
  | None -> None
  | Some x -> Some (f x)
