(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStar.List
open FStar.All
include FStar.List.Tot

(** Iterators **)

val iter: ('a -> ML unit) -> list 'a -> ML unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

val iteri_aux: int -> (int -> 'a -> ML unit) -> list 'a -> ML unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

val iteri: (int -> 'a -> ML unit) -> list 'a -> ML unit
let iteri f x = iteri_aux 0 f x

val map: ('a -> ML 'b) -> list 'a -> ML (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val mapT: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapT = FStar.List.Tot.map

val mapi_init: (int -> 'a -> ML 'b) -> list 'a -> int -> ML (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

val mapi: (int -> 'a -> ML 'b) -> list 'a -> ML (list 'b)
let mapi f l = mapi_init f l 0

val concatMap: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    fa @ ftl

val map2: ('a -> 'b -> ML 'c) -> list 'a -> list 'b -> ML (list 'c)
let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

val map3: ('a -> 'b -> 'c -> ML 'd) -> list 'a -> list 'b -> list 'c -> ML (list 'd)
let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

val fold_left: ('a -> 'b -> ML 'a) -> 'a -> list 'b -> ML 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_left2: ('s -> 'a -> 'b -> ML 's) -> 's -> list 'a -> list 'b -> ML 's
let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

val fold_right: ('a -> 'b -> ML 'b) -> list 'a -> 'b -> ML 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** List searching **)
val filter: ('a -> ML bool) -> list 'a -> ML (list 'a)
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val for_all: ('a -> ML bool) -> list 'a -> ML bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

val forall2: ('a -> 'b -> ML bool) -> list 'a -> list 'b -> ML bool
let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

val collect: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

val tryFind: ('a -> ML bool) -> list 'a -> ML (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

val tryPick: ('a -> ML (option 'b)) -> list 'a -> ML (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

val choose: ('a -> ML (option 'b)) -> list 'a -> ML (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

val partition: ('a -> ML bool) -> list 'a -> ML (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** List of tuples **)
val zip: list 'a -> list 'b -> ML (list ('a * 'b))
let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(** Sorting (implemented as quicksort) **)

val sortWith: ('a -> 'a -> ML int) -> list 'a -> ML (list 'a)
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (fun x -> f pivot x > 0) tl in
     sortWith f lo@(pivot::sortWith f hi)

val splitAt: nat -> list 'a -> ML (list 'a * list 'a)
let rec splitAt n l =
  if n = 0 then l, []
  else
    match l with
      | []     -> failwith "splitAt index is more that list length"
      | hd::tl ->
	let l1, l2 = splitAt (n - 1) tl in
	hd::l1, l2

let filter_map (f:'a -> ML (option 'b)) (l:list 'a) : ML (list 'b) =
  let rec filter_map_acc (acc:list 'b) (l:list 'a) : ML (list 'b) =
    match l with
    | [] ->
        rev acc
    | hd :: tl ->
        match f hd with
        | Some hd ->
            filter_map_acc (hd :: acc) tl
        | None ->
            filter_map_acc acc tl
  in
  filter_map_acc [] l

val index: ('a -> ML bool) -> list 'a -> ML int
let index f l =
  let rec index f l i =
    match l with
    | [] ->
        failwith "List.index: not found"
    | hd :: tl ->
        if f hd then
          i
        else
          index f tl (i + 1)
  in
  index f l 0
