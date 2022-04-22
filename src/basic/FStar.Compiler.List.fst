(*
   Copyright 2008-2017 Microsoft Research

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

module FStar.Compiler.List
open Prims
open FStar.Compiler.Effect

let isEmpty (l : list 'a)
  = match l with
    | [] -> true
    | _ -> false

let hd (l:list 'a)
  = match l with
    | hd :: tl -> hd
    | _ -> failwith "head of empty list"

let tail (l:list 'a)
  = match l with
    | hd::tl -> tl
    | _ -> failwith "tail of empty list"

let tl x = tail x

let rec length (l:list 'a)
  = match l with
    | [] -> 0
    | _::tl -> 1 + length tl

let rec nth (l:list 'a) (n:int)
  = if n < 0
    then failwith "nth takes a non-negative integer as input"
    else if n=0 then
        match l with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else match l with
        | [] ->  failwith "not enough elements"
        | _::tl -> nth tl (n - 1)

let rec count x l
  = match l with
    | [] -> 0
    | hd::tl ->
      if x = hd then 1 + count x tl
      else count x tl

let rec rev_acc (l:list 'a) (acc:list 'a)
  = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

let rev_append l a = rev_acc l a

let rev (l:list 'a) = rev_acc l []

let rec append x y =
  match x with
  | [] -> y
  | hd::tl -> hd :: append tl y

let ( @ ) x y = append x y

let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)

let concat x = flatten x

let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let () = f a in iter f tl

let rec iter2 f l m = match l, m with
  | [], [] -> ()
  | x::l, y::m -> f x y; iter2 f l m
  | _ -> failwith "iter2: unequal list lengths"

let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

let mapi f l = mapi_init f l 0

let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

let rec fold_right2 f l0 l1 x = match l0, l1 with
  | [], [] -> x
  | hd0::tl0, hd1::tl1 -> f hd0 hd1 (fold_right2 f tl0 tl1 x)
  | _ -> failwith "The lists do not have the same length"

let rev_map_onto f l acc = fold_left (fun acc x -> f x :: acc) acc l

let rec init = function
  | [] -> failwith "init: empty list"
  | [h] -> []
  | h::t -> h::(init t)

let last l = fold_left (fun _ x -> Some x) None l

let rec mem x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

let contains x l = mem x l

let rec existsb f l
  = match l with
    | [] -> false
    | hd::tl -> if f hd then true else existsb f tl

let rec existsML f l
  = match l with
    | [] -> false
    | hd::tl -> if f hd then true else existsML f tl

let rec find f l
  = match l with
    | [] -> None
    | hd::tl -> if f hd then Some hd else find f tl

let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

let rec assoc a x
  = match x with
    | [] -> None
    | (a', b)::tl ->
      if (a = a')
      then Some b
      else assoc a tl

let rec splitAt n l =
  if n = 0 then [], l
  else
    match l with
      | []     -> failwith "splitAt index is more that list length"
      | hd::tl ->
        let l1, l2 = splitAt (n - 1) tl in
        hd::l1, l2

let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)

let unzip x = split x

let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)

let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

let rec zip3 l1 l2 l3
  = match l1, l2, l3 with
    | [], [], [] -> []
    | (hd1::tl1, hd2::tl2, hd3::tl3) ->
      (hd1, hd2, hd3)::zip3 tl1 tl2 tl3
    | _ -> failwith "The lists do not have the same length"

let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let lo, hi  = partition (fun x -> f pivot x > 0) tl in
     append (sortWith f lo) (pivot::sortWith f hi)

let bool_of_compare (f:'a -> 'a -> Tot int) x y = f x y >= 0

let rec unique l =
  // this matches the semantics of BatList.unique.
  match l with
  | [] -> []
  | h::t ->
    if mem h t then
      unique t
    else
      h::(unique t)

let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl
let iteri f x = iteri_aux 0 f x

let filter_map (f:'a -> option 'b) (l:list 'a) =
  let rec filter_map_acc (acc:list 'b) (l:list 'a) : list 'b =
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

let index f l =
  let rec index l i =
    match l with
    | [] ->
        failwith "List.index: not found"
    | hd :: tl ->
        if f hd then
          i
        else
          index tl (i + 1)
  in
  index l 0

let span #a f l =
  match l with
  | [] -> [], []
  | hd::tl ->
    if f hd
    then let pf, rest = span f tl in
         hd::pf, rest
    else [], l

  
