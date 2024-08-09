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

(**
F* standard library List module. 

@summary F* stdlib List module. 
*)
module FStar.List
open FStar.All
include FStar.List.Tot

(** Base operations **)

(** [hd l] returns the first element of [l]. Raises an exception if
[l] is empty (thus, [hd] hides [List.Tot.hd] which requires [l] to be
nonempty at type-checking time.) Named as in: OCaml, F#, Coq *)
val hd: list 'a -> ML 'a
let hd = function
  | hd::tl -> hd
  | _ -> failwith "head of empty list"

(** [tail l] returns [l] without its first element. Raises an
exception if [l] is empty (thus, [tail] hides [List.Tot.tail] which
requires [l] to be nonempty at type-checking time). Similar to: tl in
OCaml, F#, Coq *)
val tail: list 'a -> ML (list 'a)
let tail = function
  | hd::tl -> tl
  | _ -> failwith "tail of empty list"

(** [tl l] returns [l] without its first element. Raises an exception
if [l] is empty (thus, [tl] hides [List.Tot.tl] which requires [l] to
be nonempty at type-checking time). Named as in: tl in OCaml, F#, Coq
*)
val tl : list 'a -> ML (list 'a)
let tl l = tail l

(** [last l] returns the last element of [l]. Requires, at
type-checking time, that [l] be nonempty. Named as in: Haskell
*)
val last: list 'a -> ML 'a
let rec last = function
  | [hd] -> hd
  | _::tl -> last tl
  | _ -> failwith "last of empty list"

(** [init l] returns [l] without its last element. Requires, at
type-checking time, that [l] be nonempty. Named as in: Haskell
*)
val init: list 'a -> ML (list 'a)
let rec init = function
  | [_] -> []
  | hd::tl -> hd::(init tl)
  | _ -> failwith "init of empty list"

(** [nth l n] returns the [n]-th element in list [l] (with the first
element being the 0-th) if [l] is long enough, or raises an exception
otherwise (thus, [nth] hides [List.Tot.nth] which has [option] type.)
Named as in: OCaml, F#, Coq *)

val nth: list 'a -> int -> ML 'a
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

(** [iter f l] performs [f x] for each element [x] of [l], in the
order in which they appear in [l]. Named as in: OCaml, F# . *)
val iter: ('a -> ML unit) -> list 'a -> ML unit
let rec iter f x = match x with
  | [] -> ()
  | a::tl -> let _ = f a in iter f tl

(** [iteri_aux n f l] performs, for each i, [f (i+n) x] for the i-th
element [x] of [l], in the order in which they appear in [l]. *)
val iteri_aux: int -> (int -> 'a -> ML unit) -> list 'a -> ML unit
let rec iteri_aux i f x = match x with
  | [] -> ()
  | a::tl -> f i a; iteri_aux (i+1) f tl

(** [iteri_aux f l] performs, for each [i], [f i x] for the i-th
element [x] of [l], in the order in which they appear in [l]. Named as
in: OCaml *)
val iteri: (int -> 'a -> ML unit) -> list 'a -> ML unit
let iteri f x = iteri_aux 0 f x

(** [map f l] applies [f] to each element of [l] and returns the list
of results, in the order of the original elements in [l]. (Hides
[List.Tot.map] which requires, at type-checking time, [f] to be a pure
total function.)  Named as in: OCaml, Coq, F# *)
val map: ('a -> ML 'b) -> list 'a -> ML (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

(** [mapT f l] applies [f] to each element of [l] and returns the list
of results, in the order of the original elements in [l]. Requires, at
type-checking time, [f] to be a pure total function. *)
val mapT: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapT = FStar.List.Tot.map

(** [mapi_init f n l] applies, for each [k], [f (n+k)] to the [k]-th
element of [l] and returns the list of results, in the order of the
original elements in [l]. (Hides [List.Tot.mapi_init] which requires,
at type-checking time, [f] to be a pure total function.) *)
val mapi_init: (int -> 'a -> ML 'b) -> list 'a -> int -> ML (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

(** [mapi f l] applies, for each [k], [f k] to the [k]-th element of
[l] and returns the list of results, in the order of the original
elements in [l]. (Hides [List.Tot.mapi] which requires, at
type-checking time, [f] to be a pure total function.) Named as in:
OCaml *)
val mapi: (int -> 'a -> ML 'b) -> list 'a -> ML (list 'b)
let mapi f l = mapi_init f l 0

(** [concatMap f l] applies [f] to each element of [l] and returns the
concatenation of the results, in the order of the original elements of
[l]. This is equivalent to [flatten (map f l)]. (Hides
[List.Tot.concatMap], which requires, at type-checking time, [f] to be
a pure total function.) *)

val concatMap: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    fa @ ftl

(** [map2 f l1 l2] computes [f x1 x2] for each element x1 of [l1] and
the element [x2] of [l2] at the same position, and returns the list of
such results, in the order of the original elements in [l1]. Raises an
exception if [l1] and [l2] have different lengths.  Named as in: OCaml
*)
val map2: ('a -> 'b -> ML 'c) -> list 'a -> list 'b -> ML (list 'c)
let rec map2 f l1 l2 = match l1, l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (f hd1 hd2)::(map2 f tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(** [map3 f l1 l2 l3] computes [f x1 x2 x3] for each element x1 of
[l1] and the element [x2] of [l2] and the element [x3] of [l3] at the
same position, and returns the list of such results, in the order of
the original elements in [l1]. Raises an exception if [l1], [l2] and
[l3] have different lengths.  Named as in: OCaml *)
val map3: ('a -> 'b -> 'c -> ML 'd) -> list 'a -> list 'b -> list 'c -> ML (list 'd)
let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | hd1::tl1, hd2::tl2, hd3::tl3 -> (f hd1 hd2 hd3)::(map3 f tl1 tl2 tl3)
    | _, _, _ -> failwith "The lists do not have the same length"

(** [fold_left f x [y1; y2; ...; yn]] computes (f (... (f x y1) y2)
... yn). (Hides [List.Tot.fold_left], which requires, at type-checking
time, [f] to be a pure total function.) Named as in: OCaml, Coq *)
val fold_left: ('a -> 'b -> ML 'a) -> 'a -> list 'b -> ML 'a
let rec fold_left f x y = match y with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

(** [fold_left2 f x [y1; y2; ...; yn] [z1; z2; ...; zn]] computes (f
(... (f x y1 z1) y2 z2 ... yn zn). Raises an exception if [y1; y2;
...] and [z1; z2; ...] have different lengths. (Thus, hides
[List.Tot.fold_left2] which requires such a condition at type-checking
time.) Named as in: OCaml *)
val fold_left2: ('s -> 'a -> 'b -> ML 's) -> 's -> list 'a -> list 'b -> ML 's
let rec fold_left2 f a l1 l2 = match l1, l2 with
    | [], [] -> a
    | hd1::tl1, hd2::tl2 -> fold_left2 f (f a hd1 hd2) tl1 tl2
    | _, _ -> failwith "The lists do not have the same length"

(** [fold_right f [x1; x2; ...; xn] y] computes (f x1 (f x2 (... (f xn
y)) ... )). (Hides [List.Tot.fold_right], which requires, at
type-checking time, [f] to be a pure total function.) Named as in:
OCaml, Coq *)
val fold_right: ('a -> 'b -> ML 'b) -> list 'a -> 'b -> ML 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** List searching **)

(** [filter f l] returns [l] with all elements [x] such that [f x]
does not hold removed. (Hides [List.Tot.filter] which requires, at
type-checking time, [f] to be a pure total function.) Named as in:
OCaml, Coq *)
val filter: ('a -> ML bool) -> list 'a -> ML (list 'a)
let rec filter f = function
  | [] -> []
  | hd::tl -> if f hd then hd::(filter f tl) else filter f tl

(** [for_all f l] returns [true] if, and only if, for all elements [x]
appearing in [l], [f x] holds. (Hides [List.Tot.for_all], which
requires, at type-checking time, [f] to be a pure total function.)
Named as in: OCaml. Similar to: List.forallb in Coq *)
val for_all: ('a -> ML bool) -> list 'a -> ML bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

(** [for_all f l1 l2] returns [true] if, and only if, for all elements
[x1] appearing in [l1] and the element [x2] appearing in [l2] at the
same position, [f x1 x2] holds. Raises an exception if [l1] and [l2]
have different lengths. Similar to: List.for_all2 in OCaml. Similar
to: List.Forall2 in Coq (which is propositional) *)
val forall2: ('a -> 'b -> ML bool) -> list 'a -> list 'b -> ML bool
let rec forall2 f l1 l2 = match l1,l2 with
    | [], [] -> true
    | hd1::tl1, hd2::tl2 -> if f hd1 hd2 then forall2 f tl1 tl2 else false
    | _, _ -> failwith "The lists do not have the same length"

(** [collect f l] applies [f] to each element of [l] and returns the
concatenation of the results, in the order of the original elements of
[l]. It is equivalent to [flatten (map f l)]. (Hides
[List.Tot.collect] which requires, at type-checking time, [f] to be a
pure total function.) TODO: what is the difference with [concatMap]?
*)
val collect: ('a -> ML (list 'b)) -> list 'a -> ML (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

(** [tryFind f l] returns [Some x] for some element [x] appearing in
[l] such that [f x] holds, or [None] only if no such [x]
exists. (Hides [List.Tot.tryFind], which requires, at type-checking
time, [f] to be a pure total function.)  *)
val tryFind: ('a -> ML bool) -> list 'a -> ML (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

(** [tryPick f l] returns [y] for some element [x] appearing in [l]
such that [f x = Some y] for some y, or [None] only if [f x = None]
for all elements [x] of [l]. (Hides [List.Tot.tryPick], which
requires, at type-checking time, [f] to be a pure total function.) *)
val tryPick: ('a -> ML (option 'b)) -> list 'a -> ML (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(** [choose f l] returns the list of [y] for all elements [x]
appearing in [l] such that [f x = Some y] for some [y]. (Hides
[List.Tot.choose] which requires, at type-checking time, [f] to be a
pure total function.) *)
val choose: ('a -> ML (option 'b)) -> list 'a -> ML (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

(** [partition f l] returns the pair of lists [(l1, l2)] where all
elements [x] of [l] are in [l1] if [f x] holds, and in [l2]
otherwise. Both [l1] and [l2] retain the original order of [l]. (Hides
[List.Tot.partition], which requires, at type-checking time, [f] to be
a pure total function.) *)
val partition: ('a -> ML bool) -> list 'a -> ML (list 'a & list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** List of tuples **)

(** [zip] takes two lists [x1, ..., xn] and [y1, ..., yn] and returns
the list of pairs [(x1, y1), ..., (xn, yn)]. Raises an exception if
the two lists have different lengths. Named as in: Haskell *)
val zip: list 'a -> list 'b -> ML (list ('a & 'b))
let rec zip l1 l2 = match l1,l2 with
    | [], [] -> []
    | hd1::tl1, hd2::tl2 -> (hd1,hd2)::(zip tl1 tl2)
    | _, _ -> failwith "The lists do not have the same length"

(** Sorting (implemented as quicksort) **)

(** [sortWith compare l] returns the list [l'] containing the elements
of [l] sorted along the comparison function [compare], in such a way
that if [compare x y > 0], then [x] appears before [y] in [l']. (Hides
[List.Tot.sortWith], which requires, at type-checking time, [compare]
to be a pure total function.) *)
val sortWith: ('a -> 'a -> ML int) -> list 'a -> ML (list 'a)
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (fun x -> f pivot x > 0) tl in
     sortWith f lo@(pivot::sortWith f hi)

(** [splitAt n l] returns the pair of lists [(l1, l2)] such that [l1]
contains the first [n] elements of [l] and [l2] contains the
rest. Raises an exception if [l] has fewer than [n] elements. *)
val splitAt: nat -> list 'a -> ML (list 'a & list 'a)
let rec splitAt n l =
  if n = 0 then [], l
  else
    match l with
      | []     -> failwith "splitAt index is more that list length"
      | hd::tl ->
        let l1, l2 = splitAt (n - 1) tl in
        hd::l1, l2

(** [filter_map f l] returns the list of [y] for all elements [x]
appearing in [l] such that [f x = Some y] for some [y]. (Implemented
here as a tail-recursive version of [choose] *)
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

(** [index f l] returns the position index in list [l] of the first
element [x] in [l] such that [f x] holds. Raises an exception if no
such [x] exists. TODO: rename this function (it hides List.Tot.index
which has a completely different semantics.) *)
val index: ('a -> ML bool) -> list 'a -> ML int
let index f l =
  let rec index l i : ML int =
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
