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

module FStarC.RBSet

open FStarC.Class.Ord
open FStarC.Class.Show
open FStarC.Class.Setlike

include FStarC.Class.Setlike

type color = | R | B

type rbset (a:Type0) : Type0 =
  | L
  | N of color & rbset a & a & rbset a

let empty () = L

let singleton (x:'a) : rbset 'a = N (R, L, x, L)

let is_empty = L?

let balance c l x r =
    match c, l, x, r with
    | B, N (R, N (R, a, x, b), y, c), z, d
    | B, a, x, N (R, N (R, b, y, c), z, d)
    | B, N (R, a, x, N (R, b, y, c)), z, d
    | B, a, x, N (R, b, y, N (R, c, z, d)) ->
        N (R, N (B, a, x, b), y, N (B, c, z, d))
    | c, l, x, r -> N (c, l, x, r)

let blackroot (t:rbset 'a{N? t}) : rbset 'a =
  match t with
  | N (_, l, x, r) -> N (B, l, x, r)

let add {| ord 'a |} (x:'a) (s:rbset 'a) : rbset 'a =
  let rec add' (s:rbset 'a) : rbset 'a =
    match s with
    | L -> N (R, L, x, L)
    | N (c, a, y, b) ->
      if x <? y then balance c (add' a) y b
      else if x >? y then balance c a y (add' b)
      else s
  in
  blackroot (add' s)

let filter {| ord 'a |} (predicate: 'a -> bool) (set: rbset 'a): rbset 'a =
  let rec aux acc = function
    | L -> acc
    | N (_, l, v, r) ->
      aux (aux (if predicate v then add v acc else acc) l) r
  in aux (empty ()) set

let rec extract_min #a {| ord a |} (t : rbset a{N? t}) : rbset a & a =
  match t with
  | N (_, L, x, r) -> r, x
  | N (c, a, x, b) ->
    let (a', y) = extract_min a in
    balance c a' x b, y

(* This is not the right way, see https://www.cs.cornell.edu/courses/cs3110/2020sp/a4/deletion.pdf
for how to do it. But if we reach that complexity, I would like for
this whole module to be verified. *)
let rec remove {| ord 'a |} (x:'a) (t:rbset 'a) : rbset 'a =
  match t with
  | L -> L
  | N (c, l, y, r) ->
    if x <? y then balance c (remove x l) y r
    else if x >? y then balance c l y (remove x r)
    else
      if L? r
      then
        l
      else
        let (r', y') = extract_min r in
        balance c l y' r'

let rec mem {| ord 'a |} (x:'a) (s:rbset 'a) : bool =
  match s with
  | L -> false
  | N (_, a, y, b) ->
    if x <? y then mem x a
    else if x >? y then mem x b
    else true

let rec elems (s:rbset 'a) : list 'a =
  match s with
  | L -> []
  | N (_, a, x, b) -> elems a @ [x] @ elems b

let equal {| ord 'a |} (s1:rbset 'a) (s2:rbset 'a) : bool =
  elems s1 =? elems s2

let rec union {| ord 'a |} (s1:rbset 'a) (s2:rbset 'a) : rbset 'a =
  match s1 with
  | L -> s2
  | N (c, a, x, b) -> union a (union b (add x s2))

let inter {| ord 'a |} (s1:rbset 'a) (s2:rbset 'a) : rbset 'a =
  let rec aux (s1:rbset 'a) (acc : rbset 'a) : rbset 'a =
    match s1 with
    | L -> acc
    | N (_, a, x, b) ->
      if mem x s2
      then add x (aux a (aux b acc))
      else aux a (aux b acc)
  in
  aux s1 L

let rec diff {| ord 'a |} (s1:rbset 'a) (s2:rbset 'a) : rbset 'a =
  match s2 with
  | L -> s1
  | N (_, a, x, b) -> diff (diff (remove x s1) a) b

let rec subset {| ord 'a |} (s1:rbset 'a) (s2:rbset 'a) : bool =
  match s1 with
  | L -> true
  | N (_, a, x, b) -> mem x s2 && subset a s2 && subset b s2

let rec for_all (p:'a -> bool) (s:rbset 'a) : bool =
  match s with
  | L -> true
  | N (_, a, x, b) -> p x && for_all p a && for_all p b

let rec for_any (p:'a -> bool) (s:rbset 'a) : bool =
  match s with
  | L -> false
  | N (_, a, x, b) -> p x || for_any p a || for_any p b

// Make this faster
let from_list {| ord 'a |} (xs : list 'a) : rbset 'a =
  List.fold_left (fun s e -> add e s) L xs

let addn {| ord 'a |} (xs : list 'a) (s : rbset 'a) : rbset 'a =
  List.fold_left (fun s e -> add e s) s xs

let collect #a {| ord a |} (f : a -> rbset a)
    (l : list a) : rbset a =
    List.fold_left (fun s e -> union (f e) s) L l

instance setlike_rbset (a:Type) (_ : ord a) : Tot (setlike a (rbset a)) = {
    empty = empty;
    singleton = singleton;
    is_empty = is_empty;
    add = add;
    remove = remove;
    mem = mem;
    equal = equal;
    subset = subset;
    union = union;
    inter = inter;
    diff = diff;
    for_all = for_all;
    for_any = for_any;
    elems = elems;
    filter;

    collect = collect;
    from_list = from_list;
    addn = addn;
}

instance showable_rbset (a:Type) (_ : showable a) : Tot (showable (rbset a)) = {
  show = (fun s -> "RBSet " ^ show (elems s));
}
