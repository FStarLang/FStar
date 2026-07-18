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

module FStar.RBMap

open FStar.Class.Ord.Raw
open FStar.List

type color = | R | B

type t (a b :Type0) : Type0 =
  | L
  | N of color & t a b & a & b & t a b

let empty () = L

let singleton (x :'a) (y : 'b) : t 'a 'b = N (R, L, x, y, L)

let is_empty = L?

let balance c l x vx r =
    match c, l, x, vx, r with
    | B, N (R, N (R, a, x, vx, b), y, vy, c), z, vz, d
    | B, a, x, vx, N (R, N (R, b, y, vy, c), z, vz, d)
    | B, N (R, a, x, vx, N (R, b, y, vy, c)), z, vz, d
    | B, a, x, vx, N (R, b, y, vy, N (R, c, z, vz, d)) ->
        N (R, N (B, a, x, vx, b), y, vy, N (B, c, z, vz, d))
    | c, l, x, vx, r -> N (c, l, x, vx, r)

let blackroot (m : t 'a 'b{N? m}) : t 'a 'b =
  let N (_, l, x, vx, r) = m in
  N (B, l, x, vx, r)

let add {| ord 'a |} (x:'a) (vx : 'b) (s:t 'a 'b) : t 'a 'b =
  let rec add' (s:t 'a 'b) : r:(t 'a 'b){N? r} =
    match s with
    | L -> N (R, L, x, vx, L)
    | N (c, a, y, vy, b) ->
      if x <? y then balance c (add' a) y vy b
      else if x >? y then balance c a y vy (add' b)
      else s
  in
  blackroot (add' s)

let filter {| ord 'a |} (predicate: 'a -> 'b -> bool) (set: t 'a 'b): t 'a 'b =
  let rec aux (acc m : t 'a 'b) : Tot (t 'a 'b) (decreases m) =
    match m with
    | L -> acc
    | N (_, l, v, vy, r) ->
      aux (aux (if predicate v vy then add v vy acc else acc) l) r
  in aux (empty ()) set

let rec extract_min #a #b {| ord a |} (m : t a b{not (is_empty m)}) : t a b & (a & b) =
  match m with
  | N (_, L, x, vx, r) -> r, (x, vx)
  | N (c, a, x, vx, b) ->
    let (a', y) = extract_min a in
    balance c a' x vx b, y

(* This is not the right way, see https://www.cs.cornell.edu/courses/cs3110/2020sp/a4/deletion.pdf
for how to do it. But if we reach that complexity, I would like for
this whole module to be verified. *)
let rec remove {| ord 'a |} (x : 'a) (m : t 'a 'b) : t 'a 'b =
  match m with
  | L -> L
  | N (c, l, y, vy, r) ->
    if x <? y then balance c (remove x l) y vy r
    else if x >? y then balance c l y vy (remove x r)
    else
      if L? r
      then
        l
      else
        let (r', (y', vy')) = extract_min r in
        balance c l y' vy' r'

let rec mem {| ord 'a |} (x : 'a) (m : t 'a 'b) : bool =
  match m with
  | L -> false
  | N (_, a, y, _, b) ->
    if x <? y then mem x a
    else if x >? y then mem x b
    else true

let rec lookup {| ord 'a |} (x : 'a) (m : t 'a 'b) : option 'b =
  match m with
  | L -> None
  | N (_, a, y, vy, b) ->
    if x <? y then lookup x a
    else if x >? y then lookup x b
    else Some vy

let rec keys (s : t 'a 'b) : list 'a =
  match s with
  | L -> []
  | N (_, a, x, _, b) -> keys a @ [x] @ keys b

let rec to_list (s : t 'a 'b) : list ('a & 'b) =
  match s with
  | L -> []
  | N (_, a, x, vx, b) -> to_list a @ [(x, vx)] @ to_list b

let equal {| ord 'a, Class.Eq.Raw.deq 'b |} (s1 s2 : t 'a 'b) : bool =
  let open FStar.Class.Eq.Raw in
  to_list s1 = to_list s2

let rec union {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b =
  match s1 with
  | L -> s2
  | N (c, a, x, vx, b) -> union a (union b (add x vx s2))

(* Intersect the maps. It's left-biased: prefer values on the first map. *)
let inter {| ord 'a |} (s1 s2 : t 'a 'b) : t 'a 'b =
  let rec aux (s1 acc : t 'a 'b) : t 'a 'b =
    match s1 with
    | L -> acc
    | N (_, a, x, vx, b) ->
      if mem x s2
      then add x vx (aux a (aux b acc))
      else aux a (aux b acc)
  in
  aux s1 L

let rec for_all (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool =
  match s with
  | L -> true
  | N (_, a, x, vx, b) -> p x vx && for_all p a && for_all p b

let rec for_any (p : 'a -> 'b -> bool) (s : t 'a 'b) : bool =
  match s with
  | L -> false
  | N (_, a, x, vx, b) -> p x vx || for_all p a && for_all p b

// Make this faster
let from_list {| ord 'a |} (xs : list ('a & 'b)) : t 'a 'b =
  List.Tot.fold_left (fun s (k, v) -> add k v s) L xs

let addn {| ord 'a |} (xs : list ('a & 'b)) (s : t 'a 'b) : t 'a 'b =
  List.Tot.fold_left (fun s (k, v) -> add k v s) s xs
