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

module FStarC.FlatSet

open FStarC.Class.Ord
open FStarC.Effect
open FStarC.Order
open FStarC.Class.Show

(* This is a slow implementation that mimics FStarC.Util.set,
which is implemented with lists. As it turns out we heavily rely on
the exact order of `elems` provided by this list representation, so we
cannot (yet) do big changes here. *)

(* Inv: no duplication. We are left-biased. *)
let flat_set t = list t

val add (#a:Type) {| ord a |} : a -> flat_set a -> flat_set a
let rec add x s =
  match s with
  | [] -> [x]
  | y::yy -> if x =? y then s else y :: add x yy

val empty (#a:Type) : unit -> flat_set a
let empty () = []

val from_list (#a:Type) {| ord a |} : list a -> flat_set a
let from_list xs = dedup xs

val mem (#a:Type) {| ord a |} : a -> flat_set a -> bool
let mem x s = List.existsb (fun y -> x =? y) s

val singleton (#a:Type) {| ord a |} : a -> flat_set a
let singleton x = [x]

val is_empty (#a:Type) : flat_set a -> bool
let is_empty s = Nil? s

val addn (#a:Type) {| ord a |} : list a -> flat_set a -> flat_set a
let addn xs ys = List.fold_right add xs ys

val remove (#a:Type) {| ord a |} : a -> flat_set a -> flat_set a
let rec remove x s =
  match s with
  | [] -> []
  | y::yy -> if x =? y then yy else y :: remove x yy

val elems (#a:Type) : flat_set a -> list a
let elems s = s

val for_all (#a:Type) : (a -> bool) -> flat_set a -> bool
let for_all p s = elems s |> List.for_all p

val for_any (#a:Type) : (a -> bool) -> flat_set a -> bool
let for_any p s = elems s |> List.existsb p

val subset (#a:Type) {| ord a |} : flat_set a -> flat_set a -> bool
let subset s1 s2 = for_all (fun y -> mem y s2) s1

val equal (#a:Type) {| ord a |} : flat_set a -> flat_set a -> bool
let equal s1 s2 = sort s1 =? sort s2

val union (#a:Type) {| ord a |} : flat_set a -> flat_set a -> flat_set a
let union s1 s2 = List.fold_left (fun s x -> add x s) s1 s2

val inter (#a:Type) {| ord a |} : flat_set a -> flat_set a -> flat_set a
let inter s1 s2 = List.filter (fun y -> mem y s2) s1

val diff (#a:Type) {| ord a |} : flat_set a -> flat_set a -> flat_set a
let diff s1 s2 = List.filter (fun y -> not (mem y s2)) s1

val collect (#a #b:Type) {| ord b |} : (a -> flat_set b) -> list a -> flat_set b
let collect f l = List.fold_right (fun x acc -> f x `union` acc) l (empty ())

instance showable_set (a:Type) (_ : ord a) (_ : showable a) : Tot (showable (flat_set a)) = {
    show = (fun s -> show (elems s));
}

instance setlike_flat_set (a:Type) (_ : ord a) : Tot (setlike a (flat_set a)) = {
    empty = empty;
    from_list = from_list;
    singleton = singleton;
    is_empty = is_empty;
    add = add;
    addn = addn;
    remove = remove;
    mem = mem;
    elems = elems;
    filter = List.filter;
    for_all = for_all;
    for_any = for_any;
    subset = subset;
    equal = equal;
    union = union;
    inter = inter;
    diff = diff;
    collect = collect;
}
