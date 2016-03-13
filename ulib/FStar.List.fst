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
open FStar.List.Tot

(** Base operations **)
val hd: list 'a -> 'a
let hd = function
  | hd::tl -> hd
  | _ -> failwith "head of empty list"

let tail = function
  | hd::tl -> tl
  | _ -> failwith "tail of empty list"
let tl = tail

val nth: list 'a -> int -> 'a
let rec nth l n =
  if n < 0 then
    failwith "nth takes a non-negative integer as input"
  else
    if n = 0 then
      match l with
        | [] -> failwith "not enough elements"
        | hd::_ -> hd
    else
      match l with
        | [] -> failwith "not enough elements"
        | _::tl -> nth tl (n - 1)

(** Iterators **)

val iter: ('a -> unit) -> list 'a -> unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl
  
val iteri_aux: int -> (int -> 'a -> unit) -> list 'a -> unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

val iteri: (int -> 'a -> unit) -> list 'a -> unit
let iteri f x = iteri_aux 0 f x

val map: ('a -> 'b) -> list 'a -> list 'b
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

val mapT: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec mapT f x = match x with
  | [] -> []
  | a::tl -> f a::mapT f tl

val mapi_init: (int -> 'a -> 'b) -> list 'a -> int -> list 'b
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

val mapi_initT: (int -> 'a -> Tot 'b) -> list 'a -> int -> Tot (list 'b)
let rec mapi_initT f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_initT f tl (i+1))

val mapi: (int -> 'a -> 'b) -> list 'a -> list 'b
let mapi f l = mapi_init f l 0

val concatMap: ('a -> list 'b) -> list 'a -> list 'b
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    fa @ ftl

val map2: ('a -> 'b -> 'c) -> list 'a -> list 'b -> list 'c
let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

val map3: ('a -> 'b -> 'c -> 'd) -> list 'a -> list 'b -> list 'c -> list 'd
let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

val fold_left: ('a -> 'b -> 'a) -> 'a -> list 'b -> 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

val fold_left2: ('s -> 'a -> 'b -> 's) -> 's -> list 'a -> list 'b -> 's
let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

val fold_right: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** List searching **)
val filter: ('a -> bool) -> list 'a -> list 'a
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

val for_all: ('a -> bool) -> list 'a -> bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

val forall2: ('a -> 'b -> bool) -> list 'a -> list 'b -> bool
let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

val collect: ('a -> list 'b) -> list 'a -> list 'b
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

val tryFind: ('a -> bool) -> list 'a -> option 'a
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

val tryPick: ('a -> option 'b) -> list 'a -> option 'b
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

val choose: ('a -> option 'b) -> list 'a -> list 'b
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

val partition: ('a -> bool) -> list 'a -> (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** List of tuples **)
val zip: list 'a -> list 'b -> list ('a * 'b)
let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(** Sorting (implemented as quicksort) **)

val sortWith: ('a -> 'a -> int) -> list 'a -> list 'a
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (fun x -> f pivot x > 0) tl in
     sortWith f lo@(pivot::sortWith f hi)

