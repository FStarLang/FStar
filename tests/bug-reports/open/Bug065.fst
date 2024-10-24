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
module Bug065

type pair a b : Type = | MkPair : a -> b -> pair a b

let elim (a b : Type) (c : pair a b -> Type) (f: (x:a -> y:b -> c (MkPair #a #b x y))) (p: pair a b) : c p 
= match p with | MkPair x y -> f x y

let subject_reduction_failure (x y:nat) (c:pair int int -> Type)
    (f : (x:int -> y:int -> c (MkPair #int #int x y)))
    : c (MkPair #nat #nat x y <: pair int int (* we don't have this now *)) =
  elim int int c f (MkPair #nat #nat x y <: pair int int (* we don't have this now *))

(* This returns -1 at type nat *)
let unsound () : nat =
  subject_reduction_failure 1 2 (function (MkPair #a #b x y) -> a) (fun x y -> -1)

(* type tree = *)
(*   | Leaf : tree *)
(*   | Node : n:int -> tree -> tree -> tree *)

(* val in_tree : int -> tree -> Tot bool *)
(* let rec in_tree x t = *)
(*   match t with *)
(*   | Leaf -> false *)
(*   | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2 *)

(* val ind : ta:(tree -> Type) -> *)
(*           f:(t1:tree -> t2:tree -> n:int -> ta t1 -> ta t2 -> ta (Node n t1 t2)) -> *)
(*           a:(ta Leaf) -> t:tree -> (ta t) *)
(* let rec ind ta f a t = *)
(*   match t with *)
(*   | Leaf -> a *)
(*   | Node n t1 t2 -> f t1 t2 n (ind ta f a t1) (ind ta f a t2) *)

(* (\* subtyping gets terribly confused here *\) *)
(* #set-options "--initial_fuel 10 --max_fuel 10 --initial_ifuel 10 --max_ifuel 10" *)
(* val find' : f:(int -> Tot bool) -> t:tree -> Tot (option (x:int{f x && in_tree x t})) *)
(* let find' f = ind (fun t -> option (x:int{f x && in_tree x t})) *)
(*                   (fun t1 t2 n o1 o2 -> if f n then Some n else *)
(*                                         if Some? o1 then o1 else o2) None *)
