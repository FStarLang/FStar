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

(* This is a dummy implementation referring to FStar.Compiler.Util.set, which
is implemented with lists. To be changed soon. *)

let set t = Util.set t

let add x s = set_add x s
let empty () = new_set (fun x y -> match (cmp x y) with | Lt -> -1 | Eq -> 0 | Gt -> 1)
let from_list xs = as_set xs (fun x y -> match (cmp x y) with | Lt -> -1 | Eq -> 0 | Gt -> 1)
let mem x s = set_mem x s
let singleton x = set_add x (empty ())
let is_empty s = set_is_empty s
let addn xs ys = List.fold_right add xs ys
let remove x s = set_remove x s
let equal s1 s2 = set_eq s1 s2
let inter s1 s2 = set_intersect s1 s2
let union s1 s2 = set_union s1 s2
let diff s1 s2 = set_difference s1 s2
let subset s1 s2 = set_is_subset_of s1 s2
let elems s = set_elements s
let for_all p s = elems s |> List.for_all p
let for_any p s = elems s |> List.existsb p
let collect f l = List.fold_right (fun x acc -> f x `union` acc) l (empty ())

(* Note: no deduplication in the internal list, so duplicate elements will be printed here. *)
instance showable_set (a:Type) (_ : ord a) (_ : showable a) : Tot (showable (set a)) = {
    show = (fun s -> show (elems s));
}
