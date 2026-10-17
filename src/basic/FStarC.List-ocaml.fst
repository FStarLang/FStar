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
module FStarC.List

(* OCaml implementation.  Most functions are bound to Batteries' BatList,
   which has tail-recursive versions of them. *)

open FStarC.Effect

let isEmpty l = match l with [] -> true | _ -> false

let singleton x = [x]

[@@custard_extern "BatList.hd"]
let hd _ = admit ()

[@@custard_extern "(fun l -> Z.of_int (BatList.length l))"]
let length _ = admit ()

[@@custard_extern "(fun l i -> BatList.nth l (Z.to_int i))"]
let nth _ _ = admit ()

[@@custard_extern "BatList.rev_append"]
let rev_acc _ _ = admit ()

[@@custard_extern "BatList.rev"]
let rev _ = admit ()

[@@custard_extern "BatList.append"]
let append _ _ = admit ()

[@@custard_extern "BatList.append"]
let ( @ ) _ _ = admit ()

[@@custard_extern "BatList.flatten"]
let flatten _ = admit ()

[@@custard_extern "BatList.iter"]
let iter _ _ = admit ()

[@@custard_extern "BatList.iter2"]
let iter2 _ _ _ = admit ()

[@@custard_extern "(fun f l -> BatList.iteri (fun i x -> f (Z.of_int i) x) l)"]
let iteri _ _ = admit ()

[@@custard_extern "BatList.map"]
let map _ _ = admit ()

let rec mapi_init f l i =
  match l with
  | [] -> []
  | hd :: tl -> let hd = f i hd in hd :: mapi_init f tl (i + 1)

[@@custard_extern "(fun f l -> BatList.mapi (fun i x -> f (Z.of_int i) x) l)"]
let mapi _ _ = admit ()

[@@custard_extern "(fun f l -> BatList.flatten (BatList.map f l))"]
let concatMap _ _ = admit ()

[@@custard_extern "BatList.map2"]
let map2 _ _ _ = admit ()

let rec map3 f l1 l2 l3 =
  match l1, l2, l3 with
  | [], [], [] -> []
  | x :: xs, y :: ys, z :: zs -> let h = f x y z in h :: map3 f xs ys zs
  | _, _, _ -> failwith "The lists do not have the same length"

[@@custard_extern "BatList.fold_left"]
let fold_left _ _ _ = admit ()

[@@custard_extern "BatList.fold_left2"]
let fold_left2 _ _ _ _ = admit ()

[@@custard_extern "BatList.fold_right"]
let fold_right _ _ _ = admit ()

[@@custard_extern "BatList.fold_right2"]
let fold_right2 _ _ _ _ = admit ()

let rev_map_onto f l acc = fold_left (fun acc x -> f x :: acc) acc l

[@@custard_extern "(fun l -> match BatList.rev l with [] -> failwith \"init: empty list\" | _ :: t -> BatList.rev t)"]
let init _ = admit ()

[@@custard_extern "BatList.last"]
let last _ = admit ()

let rec last_opt l =
  match l with
  | [] -> None
  | [x] -> Some x
  | _ :: tl -> last_opt tl

[@@custard_extern "BatList.exists"]
let existsb _ _ = admit ()

[@@custard_extern "BatList.exists"]
let existsML _ _ = admit ()

[@@custard_extern "List.find_opt"]
let find _ _ = admit ()

[@@custard_extern "BatList.filter"]
let filter _ _ = admit ()

[@@custard_extern "BatList.for_all"]
let for_all _ _ = admit ()

[@@custard_extern "BatList.for_all2"]
let forall2 _ _ _ = admit ()

[@@custard_extern "(fun f l -> BatList.flatten (BatList.map f l))"]
let collect _ _ = admit ()

[@@custard_extern "List.find_opt"]
let tryFind _ _ = admit ()

[@@custard_extern "List.find_map"]
let tryPick _ _ = admit ()

[@@custard_extern "BatList.filter_map"]
let choose _ _ = admit ()

[@@custard_extern "BatList.partition"]
let partition _ _ = admit ()

[@@custard_extern "(fun n l -> BatList.split_at (Z.to_int n) l)"]
let splitAt _ _ = admit ()

[@@custard_extern "BatList.split"]
let split _ = admit ()

let rec unzip3 l =
  match l with
  | [] -> ([], [], [])
  | (x, y, z) :: xyzs ->
    let (xs, ys, zs) = unzip3 xyzs in
    (x :: xs, y :: ys, z :: zs)

[@@custard_extern "BatList.combine"]
let zip _ _ = admit ()

[@@custard_extern "(fun l1 l2 l3 -> let rec zip3 l1 l2 l3 = match l1, l2, l3 with | [], [], [] -> [] | h1 :: t1, h2 :: t2, h3 :: t3 -> (h1, h2, h3) :: zip3 t1 t2 t3 | _ -> failwith \"zip3\" in zip3 l1 l2 l3)"]
let zip3 _ _ _ = admit ()

[@@custard_extern "(fun f l -> BatList.sort (fun x y -> Z.to_int (f x y)) l)"]
let sortWith _ _ = admit ()

[@@custard_extern "BatList.tl"]
let tail _ = admit ()

[@@custard_extern "BatList.tl"]
let tl _ = admit ()

[@@custard_extern "BatList.rev_append"]
let rev_append _ _ = admit ()

[@@custard_extern "BatList.flatten"]
let concat _ = admit ()

[@@custard_extern "BatList.split"]
let unzip _ = admit ()

[@@custard_extern "BatList.filter_map"]
let filter_map _ _ = admit ()

let rec count #a x l =
  match l with
  | [] -> 0
  | hd :: tl -> if x = hd then 1 + count x tl else count x tl

[@@custard_extern "BatList.mem"]
let mem _ _ = admit ()

let rec assoc #a #b x l =
  match l with
  | [] -> None
  | (y, v) :: tl -> if x = y then Some v else assoc x tl

[@@custard_extern "BatList.mem"]
let contains _ _ = admit ()

[@@custard_extern "(fun l -> BatList.unique l)"]
let unique _ = admit ()

[@@custard_extern "(fun f l -> Z.of_int (fst (BatList.findi (fun _ x -> f x) l)))"]
let index _ _ = admit ()

[@@custard_extern "BatList.span"]
let span _ _ = admit ()

[@@custard_extern "(fun f l -> BatList.unique ~eq:f l)"]
let deduplicate _ _ = admit ()

[@@custard_extern "BatList.fold_left_map"]
let fold_left_map _ _ _ = admit ()
