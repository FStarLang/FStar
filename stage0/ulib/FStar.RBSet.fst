(*
   Copyright 2008-2025 Microsoft Research

   Authors: Guido Martínez

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

module FStar.RBSet

open FStar.Class.Ord.Raw
open FStar.List

type color = | R | B

type t (a:Type0) : Type0 =
  | L
  | N of color & t a & a & t a

let empty () = L

let singleton (x:'a) : t 'a = N (R, L, x, L)

let is_empty = L?

let balance c l x r =
    match c, l, x, r with
    | B, N (R, N (R, a, x, b), y, c), z, d
    | B, a, x, N (R, N (R, b, y, c), z, d)
    | B, N (R, a, x, N (R, b, y, c)), z, d
    | B, a, x, N (R, b, y, N (R, c, z, d)) ->
        N (R, N (B, a, x, b), y, N (B, c, z, d))
    | c, l, x, r -> N (c, l, x, r)

let blackroot (s:t 'a{N? s}) : t 'a =
  match s with
  | N (_, l, x, r) -> N (B, l, x, r)

let add {| ord 'a |} (x:'a) (s:t 'a) : t 'a =
  let rec add' (s:t 'a) : r:(t 'a){N? r} =
    match s with
    | L -> N (R, L, x, L)
    | N (c, a, y, b) ->
      if x <? y then balance c (add' a) y b
      else if x >? y then balance c a y (add' b)
      else s
  in
  blackroot (add' s)

let filter {| ord 'a |} (predicate: 'a -> bool) (set: t 'a): t 'a =
  let rec aux (acc s : t 'a) : Tot (t 'a) (decreases s) =
    match s with
    | L -> acc
    | N (_, l, v, r) ->
      aux (aux (if predicate v then add v acc else acc) l) r
  in aux (empty ()) set

let rec extract_min #a {| ord a |} (s : t a{not (is_empty s)}) : t a & a =
  match s with
  | N (_, L, x, r) -> r, x
  | N (c, a, x, b) ->
    let (a', y) = extract_min a in
    balance c a' x b, y

(* This is not the right way, see https://www.cs.cornell.edu/courses/cs3110/2020sp/a4/deletion.pdf
for how to do it. But if we reach that complexity, I would like for
this whole module to be verified. *)
let rec remove {| ord 'a |} (x:'a) (s : t 'a) : t 'a =
  match s with
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

let rec mem {| ord 'a |} (x:'a) (s:t 'a) : bool =
  match s with
  | L -> false
  | N (_, a, y, b) ->
    if x <? y then mem x a
    else if x >? y then mem x b
    else true

let rec elems (s:t 'a) : list 'a =
  match s with
  | L -> []
  | N (_, a, x, b) -> elems a @ [x] @ elems b

let equal {| ord 'a |} (s1:t 'a) (s2:t 'a) : bool =
  let open FStar.Class.Eq.Raw in
  elems s1 = elems s2

let rec union {| ord 'a |} (s1:t 'a) (s2:t 'a) : t 'a =
  match s1 with
  | L -> s2
  | N (c, a, x, b) -> union a (union b (add x s2))

let inter {| ord 'a |} (s1:t 'a) (s2:t 'a) : t 'a =
  let rec aux (s1:t 'a) (acc : t 'a) : t 'a =
    match s1 with
    | L -> acc
    | N (_, a, x, b) ->
      if mem x s2
      then add x (aux a (aux b acc))
      else aux a (aux b acc)
  in
  aux s1 L

let rec diff {| ord 'a |} (s1 s2 : t 'a) : Tot (t 'a) (decreases s2) =
  match s2 with
  | L -> s1
  | N (_, a, x, b) -> diff (diff (remove x s1) a) b

let rec subset {| ord 'a |} (s1:t 'a) (s2:t 'a) : bool =
  match s1 with
  | L -> true
  | N (_, a, x, b) -> mem x s2 && subset a s2 && subset b s2

let rec for_all (p:'a -> bool) (s:t 'a) : bool =
  match s with
  | L -> true
  | N (_, a, x, b) -> p x && for_all p a && for_all p b

let rec for_any (p:'a -> bool) (s:t 'a) : bool =
  match s with
  | L -> false
  | N (_, a, x, b) -> p x || for_any p a || for_any p b

// Make this faster
let from_list {| ord 'a |} (xs : list 'a) : t 'a =
  List.Tot.fold_left (fun s e -> add e s) L xs

let addn {| ord 'a |} (xs : list 'a) (s : t 'a) : t 'a =
  List.Tot.fold_left (fun s e -> add e s) s xs

let collect #a {| ord a |} (f : a -> t a)
    (l : list a) : t a =
    List.Tot.fold_left (fun s e -> union (f e) s) L l
