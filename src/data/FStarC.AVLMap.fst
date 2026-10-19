(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.AVLMap

open FStarC.Effect
module SI = FStarC.SmallInt

noeq
type tree (k v : Type0) =
  | Leaf
  | Node : l:tree k v -> key:k -> value:v -> r:tree k v -> h:SI.t -> tree k v

let t k v = tree k v

let empty = Leaf

let height (#k #v : Type0) (m : tree k v) : SI.t =
  match m with
  | Leaf -> SI.zero
  | Node _ _ _ _ h -> h

let node (#k #v : Type0) (l : tree k v) (key : k) (value : v) (r : tree k v) : tree k v =
  Node l key value r (SI.(max (height l) (height r) + one))

(* [l] and [r] are balanced, and their heights differ by at most 3. *)
let bal (#k #v : Type0) (l : tree k v) (key : k) (value : v) (r : tree k v) : tree k v =
  let hl = height l in
  let hr = height r in
  let two = SI.(one + one) in
  if SI.(hl > hr + two) then
    match l with
    | Node ll lk lv lr _ ->
      if SI.(height ll >= height lr) then node ll lk lv (node lr key value r)
      else (match lr with
            | Node lrl lrk lrv lrr _ ->
              node (node ll lk lv lrl) lrk lrv (node lrr key value r)
            | Leaf -> node l key value r)
    | Leaf -> node l key value r
  else if SI.(hr > hl + two) then
    match r with
    | Node rl rk rv rr _ ->
      if SI.(height rr >= height rl) then node (node l key value rl) rk rv rr
      else (match rl with
            | Node rll rlk rlv rlr _ ->
              node (node l key value rll) rlk rlv (node rlr rk rv rr)
            | Leaf -> node l key value r)
    | Leaf -> node l key value r
  else Node l key value r (SI.(max hl hr + one))

let rec add #k #v c key value m =
  match m with
  | Leaf -> Node Leaf key value Leaf SI.one
  | Node l k' v' r h ->
    let o = c key k' in
    if o = SI.zero then Node l key value r h
    else if SI.(o < zero) then bal (add c key value l) k' v' r
    else bal l k' v' (add c key value r)

let rec find #k #v c key m =
  match m with
  | Leaf -> None
  | Node l k' v' r _ ->
    let o = c key k' in
    if o = SI.zero then Some v'
    else if SI.(o < zero) then find c key l
    else find c key r

(* The smallest binding of [Node l key value r], and the rest of it. *)
let rec pop_min (#k #v : Type0) (l : tree k v) (key : k) (value : v) (r : tree k v)
  : Tot (k & v & tree k v) (decreases l)
  = match l with
    | Leaf -> (key, value, r)
    | Node ll lk lv lr _ ->
      let (mk, mv, l') = pop_min ll lk lv lr in
      (mk, mv, bal l' key value r)

(* All keys of [l] are smaller than those of [r]. *)
let concat (#k #v : Type0) (l r : tree k v) : tree k v =
  match l, r with
  | Leaf, _ -> r
  | _, Leaf -> l
  | _, Node rl rk rv rr _ ->
    let (mk, mv, r') = pop_min rl rk rv rr in
    bal l mk mv r'

let rec remove #k #v c key m =
  match m with
  | Leaf -> Leaf
  | Node l k' v' r _ ->
    let o = c key k' in
    if o = SI.zero then concat l r
    else if SI.(o < zero) then bal (remove c key l) k' v' r
    else bal l k' v' (remove c key r)

let rec fold #k #v #a f m acc =
  match m with
  | Leaf -> acc
  | Node l key value r _ ->
    let acc = fold f l acc in
    let acc = f key value acc in
    fold f r acc

let rec fold_pure #k #v #a f m acc =
  match m with
  | Leaf -> acc
  | Node l key value r _ ->
    let acc = fold_pure f l acc in
    let acc = f key value acc in
    fold_pure f r acc

let rec iter #k #v f m =
  match m with
  | Leaf -> ()
  | Node l key value r _ ->
    iter f l;
    f key value;
    iter f r

let rec find_map #k #v #a f m =
  match m with
  | Leaf -> None
  | Node l key value r _ ->
    match find_map f l with
    | Some x -> Some x
    | None ->
      match f key value with
      | Some x -> Some x
      | None -> find_map f r
