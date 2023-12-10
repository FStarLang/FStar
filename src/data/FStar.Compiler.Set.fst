(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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

module FStar.Compiler.Set

open FStar.Class.Ord
open FStar.Compiler.Effect
open FStar.Compiler.Order
open FStar.Compiler.Util

(* This is a slow implementation that mimics FStar.Compiler.Util.set,
which is implemented with lists. As it turns out we heavily rely on
the exact order of `elems` provided by this list representation, so we
cannot (yet) do big changes here. *)

(* Inv: no duplication. We are left-biased. *)
let set t = list t

let rec add x s =
  match s with
  | [] -> [x]
  | y::yy -> if x =? y then s else y :: add x yy

let empty () = []

let from_list xs = dedup xs

let mem x s = List.existsb (fun y -> x =? y) s

let singleton x = [x]

let is_empty s = Nil? s

let addn xs ys = List.fold_right add xs ys

let rec remove x s =
  match s with
  | [] -> []
  | y::yy -> if x =? y then yy else y :: remove x yy

let elems s = s

let for_all p s = elems s |> List.for_all p
let for_any p s = elems s |> List.existsb p

let subset s1 s2 = for_all (fun y -> mem y s2) s1
let equal s1 s2 = sort s1 =? sort s2

let union s1 s2 = List.fold_left (fun s x -> add x s) s1 s2
let inter s1 s2 = List.filter (fun y -> mem y s2) s1

let diff  s1 s2 = List.filter (fun y -> not (mem y s2)) s1


let collect f l = List.fold_right (fun x acc -> f x `union` acc) l (empty ())

instance showable_set (a:Type) (_ : ord a) (_ : showable a) : Tot (showable (set a)) = {
    show = (fun s -> show (elems s));
}
