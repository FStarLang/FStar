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
This module defines all pure and total operations on lists that can be
used in specifications.

@summary Pure total operations on lists
*)
module FStar.List.Tot.Base

module F = FStar.FunctionalExtensionality

(**
Base operations
*)

(** [isEmpty l] returns [true] if and only if [l] is empty  *)
val isEmpty: list 'a -> Tot bool
let isEmpty l = match l with
  | [] -> true
  | _ -> false

(** [hd l] returns the first element of [l]. Requires [l] to be
nonempty, at type-checking time. Named as in: OCaml, F#, Coq *)
val hd: l:list 'a{Cons? l} -> Tot 'a
let hd = function
  | hd::_ -> hd

(** [tail l] returns [l] without its first element. Requires, at
type-checking time, that [l] be nonempty. Similar to: tl in OCaml, F#, Coq
*)
val tail: l:list 'a {Cons? l} -> Tot (list 'a)
let tail = function
  | _::tl -> tl

(** [tl l] returns [l] without its first element. Requires, at
type-checking time, that [l] be nonempty. Named as in: OCaml, F#, Coq
*)
val tl: l:list 'a {Cons? l} -> Tot (list 'a)
let tl = tail

(** [last l] returns the last element of [l]. Requires, at
type-checking time, that [l] be nonempty. Named as in: Haskell
*)
val last: l:list 'a {Cons? l} -> Tot 'a
let rec last = function
  | [hd] -> hd
  | _::tl -> last tl

(** [init l] returns [l] without its last element. Requires, at
type-checking time, that [l] be nonempty. Named as in: Haskell
*)
val init: l:list 'a {Cons? l} -> Tot (list 'a)
let rec init = function
  | [_] -> []
  | hd::tl -> hd::(init tl)

(** [length l] returns the total number of elements in [l]. Named as
in: OCaml, F#, Coq *)
val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

(** [nth l n] returns the [n]-th element in list [l] (with the first
element being the 0-th) if [l] is long enough, or [None]
otherwise. Named as in: OCaml, F#, Coq *)
val nth: list 'a -> nat -> Tot (option 'a)
let rec nth l n = match l with
  | []     -> None
  | hd::tl -> if n = 0 then Some hd else nth tl (n - 1)

(** [index l n] returns the [n]-th element in list [l] (with the first
element being the 0-th). Requires, at type-checking time, that [l] be
of length at least [n+1]. *)
val index: #a:Type -> l:list a -> i:nat{i < length l} -> Tot a
let rec index #a (l: list a) (i:nat{i < length l}): Tot a =
  if i = 0 then
    hd l
  else
    index (tl l) (i - 1)

(** [count x l] returns the number of occurrences of [x] in
[l]. Requires, at type-checking time, the type of [a] to have equality
defined. Similar to: [List.count_occ] in Coq. *)
val count: #a:eqtype -> a -> list a -> Tot nat
let rec count #a x = function
  | [] -> 0
  | hd::tl -> if x=hd then 1 + count x tl else count x tl

(** [rev_acc l1 l2] appends the elements of [l1] to the beginning of
[l2], in reverse order. It is equivalent to [append (rev l1) l2], but
is tail-recursive. Similar to: [List.rev_append] in OCaml, Coq. *)
val rev_acc: list 'a -> list 'a -> Tot (list 'a)
let rec rev_acc l acc = match l with
    | [] -> acc
    | hd::tl -> rev_acc tl (hd::acc)

(** [rev l] returns the list [l] in reverse order. Named as in: OCaml,
F#, Coq. *)
val rev: list 'a -> Tot (list 'a)
let rev l = rev_acc l []

(** [append l1 l2] appends the elements of [l2] to the end of [l1]. Named as: OCaml, F#. Similar to: [List.app] in Coq. *)
val append: list 'a -> list 'a -> Tot (list 'a)
let rec append x y = match x with
  | [] -> y
  | a::tl -> a::append tl y

(** Defines notation [@] for [append], as in OCaml, F# . *)
let op_At x y = append x y

(** [snoc l x] adds [x] to the end of the list [l]. *)
val snoc: list 'a -> 'a -> Tot (list 'a)
let snoc l x = append l [x]

(** [flatten l], where [l] is a list of lists, returns the list of the
elements of the lists in [l], preserving their order. Named as in:
OCaml, Coq. *)
val flatten: list (list 'a) -> Tot (list 'a)
let rec flatten l = match l with
    | [] -> []
    | hd::tl -> append hd (flatten tl)

(** [map f l] applies [f] to each element of [l] and returns the list
of results, in the order of the original elements in [l]. Requires, at
type-checking time, [f] to be a pure total function. Named as in: OCaml, Coq, F# *)
val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f x = match x with
  | [] -> []
  | a::tl -> f a::map f tl

(** [mapi_init f n l] applies, for each [k], [f (n+k)] to the [k]-th
element of [l] and returns the list of results, in the order of the
original elements in [l]. Requires, at type-checking time, [f] to be a
pure total function. *)
val mapi_init: (int -> 'a -> Tot 'b) -> list 'a -> int -> Tot (list 'b)
let rec mapi_init f l i = match l with
    | [] -> []
    | hd::tl -> (f i hd)::(mapi_init f tl (i+1))

(** [mapi f l] applies, for each [k], [f k] to the [k]-th element of
[l] and returns the list of results, in the order of the original
elements in [l]. Requires, at type-checking time, [f] to be a pure
total function. Named as in: OCaml *)
val mapi: (int -> 'a -> Tot 'b) -> list 'a -> Tot (list 'b)
let mapi f l = mapi_init f l 0

(** [concatMap f l] applies [f] to each element of [l] and returns the
concatenation of the results, in the order of the original elements of
[l]. This is equivalent to [flatten (map f l)]. Requires, at
type-checking time, [f] to be a pure total function. *)
val concatMap: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec concatMap f = function
  | [] -> []
  | a::tl ->
    let fa = f a in
    let ftl = concatMap f tl in
    append fa ftl

(** [fold_left f x [y1; y2; ...; yn]] computes (f (... (f x y1) y2)
... yn). Requires, at type-checking time, [f] to be a pure total
function. Named as in: OCaml, Coq. *)
val fold_left: ('a -> 'b -> Tot 'a) -> 'a -> l:list 'b -> Tot 'a (decreases l)
let rec fold_left f x l = match l with
  | [] -> x
  | hd::tl -> fold_left f (f x hd) tl

(** [fold_right f [x1; x2; ...; xn] y] computes (f x1 (f x2 (... (f xn
y)) ... )). Requires, at type-checking time, [f] to be a pure total
function. Named as in: OCaml, Coq *)
val fold_right: ('a -> 'b -> Tot 'b) -> list 'a -> 'b -> Tot 'b
let rec fold_right f l x = match l with
  | [] -> x
  | hd::tl -> f hd (fold_right f tl x)

(** [fold_left2 f x [y1; y2; ...; yn] [z1; z2; ...; zn]] computes (f
(... (f x y1 z1) y2 z2) ... yn zn). Requires, at type-checking time,
[f] to be a pure total function, and the lists [y1; y2; ...; yn] and
[z1; z2; ...; zn] to have the same lengths. Named as in: OCaml *)
val fold_left2 : f:('a -> 'b -> 'c -> Tot 'a) -> accu:'a -> l1:(list 'b) -> l2:(list 'c) ->
  Pure 'a (requires (length l1 == length l2)) (ensures (fun _ -> True)) (decreases l1)
let rec fold_left2 f accu l1 l2 =
  match (l1, l2) with
  | ([], []) -> accu
  | (a1::l1, a2::l2) -> fold_left2 f (f accu a1 a2) l1 l2

(** List searching **)

(** [mem x l] returns [true] if, and only if, [x] appears as an
element of [l]. Requires, at type-checking time, the type of elements
of [l] to have decidable equality. Named as in: OCaml. See also:
List.In in Coq, which is propositional. *)
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

(** Propositional membership (as in Coq). Does not require decidable
equality. *)

(** [memP x l] holds if, and only if, [x] appears as an
element of [l]. Similar to: List.In in Coq. *)
let rec memP (#a: Type) (x: a) (l: list a) : Tot Type0 =
  match l with
  | [] -> False
  | y :: q -> x == y \/ memP x q

(** [contains x l] returns [true] if, and only if, [x] appears as an
element of [l]. Requires, at type-checking time, the type of elements
of [l] to have decidable equality. It is equivalent to: [mem x
l]. TODO: should we rather swap the order of arguments? *)
let contains = mem

(** [existsb f l] returns [true] if, and only if, there exists some
element [x] in [l] such that [f x] holds. *)
val existsb: #a:Type
       -> f:(a -> Tot bool)
       -> list a
       -> Tot bool
let rec existsb #a f l = match l with
 | [] -> false
 | hd::tl -> if f hd then true else existsb f tl

(** [find f l] returns [Some x] for some element [x] appearing in [l]
such that [f x] holds, or [None] only if no such [x] exists. *)
val find: #a:Type
        -> f:(a -> Tot bool)
        -> list a
        -> Tot (option (x:a{f x}))
let rec find #a f l = match l with
  | [] -> None #(x:a{f x}) //These type annotations are only present because it makes bootstrapping go much faster
  | hd::tl -> if f hd then Some #(x:a{f x}) hd else find f tl

(** Filtering elements of a list [l] through a Boolean pure total
predicate [f] *)

(** We would like to have a postcondition for [filter f l] saying
that, for any element [x] of [filter f l], [f x] holds. To this end,
we need to use [mem] as defined above, which would require the
underlying type [a] of list elements to have decidable
equality. However, we would still like to define [filter] on all
element types, even those that do not have decidable equality. Thus,
we define our postcondition as [mem_filter_spec f m u] below, where
[m] is the intended [filter f l] and [u] indicates whether [a] has
decidable equality ([None] if not). Requires, at type-checking time,
[f] to be a pure total function. *)
let mem_filter_spec (#a : Type) (f: (a -> Tot bool)) (m: list a) (u: option (x : unit { hasEq a } )) : Tot Type0 =
  match u with
  | None -> True
  | Some z -> forall x . mem x m ==> f x

(** [filter f l] returns [l] with all elements [x] such that [f x]
does not hold removed. Requires, at type-checking time, [f] to be a
pure total function.  Named as in: OCaml, Coq *)
val filter : #a: Type -> f:(a -> Tot bool) -> l: list a -> Tot (m:list a { forall u . mem_filter_spec f m u } )
let rec filter #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

(** Postcondition on [filter f l] for types with decidable equality:
for any element [x] of [filter f l], [f x] holds. Requires, at
type-checking time, [f] to be a pure total function.*)
val mem_filter (#a: eqtype) (f: (a -> Tot bool)) (l: list a) (x: a) : Lemma
  (requires (mem #a x (filter f l)))
  (ensures (f x))
let mem_filter #a f l x =
  let u : option ( u : unit { hasEq a } ) = Some () in
  let y : (z : unit { mem_filter_spec f (filter f l) u } ) = () in
  ()

(** Postcondition on [filter f l] for types with decidable equality,
stated with [forall]: for any element [x] of [filter f l], [f x]
holds. Requires, at type-checking time, [f] to be a pure total
function. *)
val mem_filter_forall (#a: eqtype) (f: (a -> Tot bool)) (l: list a) : Lemma
  (requires True)
  (ensures (forall x . mem #a x (filter f l) ==> f x))
  [SMTPat (filter f l)]
let mem_filter_forall #a f l = FStar.Classical.ghost_lemma (mem_filter f l)

(** [for_all f l] returns [true] if, and only if, for all elements [x]
appearing in [l], [f x] holds. Requires, at type-checking time, [f] to
be a pure total function. Named as in: OCaml. Similar to: List.forallb
in Coq *)
val for_all: ('a -> Tot bool) -> list 'a -> Tot bool
let rec for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then for_all f tl else false

(** Specification for [for_all f l] vs. mem *)
let rec for_all_mem
  (#a: eqtype)
  (f: (a -> Tot bool))
  (l: list a)
: Lemma
  (for_all f l <==> (forall x . mem x l ==> f x))
= match l with
  | [] -> ()
  | _ :: q -> for_all_mem f q

(** [collect f l] applies [f] to each element of [l] and returns the
concatenation of the results, in the order of the original elements of
[l]. It is equivalent to [flatten (map f l)]. Requires, at
type-checking time, [f] to be a pure total function. TODO: what is
the difference with [concatMap]? *)
val collect: ('a -> Tot (list 'b)) -> list 'a -> Tot (list 'b)
let rec collect f l = match l with
    | [] -> []
    | hd::tl -> append (f hd) (collect f tl)

(** [tryFind f l] returns [Some x] for some element [x] appearing in
[l] such that [f x] holds, or [None] only if no such [x]
exists. Requires, at type-checking time, [f] to be a pure total
function. Contrary to [find], [tryFind] provides no postcondition on
its result. *)
val tryFind: ('a -> Tot bool) -> list 'a -> Tot (option 'a)
let rec tryFind p l = match l with
    | [] -> None
    | hd::tl -> if p hd then Some hd else tryFind p tl

(** [tryPick f l] returns [y] for some element [x] appearing in [l]
such that [f x = Some y] for some y, or [None] only if [f x = None]
for all elements [x] of [l]. Requires, at type-checking time, [f] to
be a pure total function. *)
val tryPick: ('a -> Tot (option 'b)) -> list 'a -> Tot (option 'b)
let rec tryPick f l = match l with
    | [] -> None
    | hd::tl ->
       match f hd with
         | Some x -> Some x
         | None -> tryPick f tl

(** [choose f l] returns the list of [y] for all elements [x]
appearing in [l] such that [f x = Some y] for some [y]. Requires, at
type-checking time, [f] to be a pure total function. *)
val choose: ('a -> Tot (option 'b)) -> list 'a -> Tot (list 'b)
let rec choose f l = match l with
    | [] -> []
    | hd::tl ->
       match f hd with
         | Some x -> x::(choose f tl)
         | None -> choose f tl

(** [partition f l] returns the pair of lists [(l1, l2)] where all
elements [x] of [l] are in [l1] if [f x] holds, and in [l2]
otherwise. Both [l1] and [l2] retain the original order of
[l]. Requires, at type-checking time, [f] to be a pure total
function. *)
val partition: f:('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2

(** [subset la lb] is true if and only if all the elements from [la]
    are also in [lb]. Requires, at type-checking time, the type of
    elements of [la] and [lb] to have decidable equality. *)
val subset: #a:eqtype -> list a -> list a -> Tot bool
let rec subset #a la lb =
  match la with
  | [] -> true
  | h :: tl ->  mem h lb && subset tl lb

(** [noRepeats l] returns [true] if, and only if, no element of [l]
appears in [l] more than once. Requires, at type-checking time, the
type of elements of [la] and [lb] to have decidable equality. *)
val noRepeats : #a:eqtype -> list a -> Tot bool
let rec noRepeats #a la =
  match la with
  | [] -> true
  | h :: tl -> not(mem h tl) && noRepeats tl

(** List of tuples **)

(** [assoc x l] returns [Some y] where [(x, y)] is the first element
of [l] whose first element is [x], or [None] only if no such element
exists. Requires, at type-checking time, the type of [x] to have
decidable equality. Named as in: OCaml. *)
val assoc: #a:eqtype -> #b:Type -> a -> list (a * b) -> Tot (option b)
let rec assoc #a #b x = function
  | [] -> None
  | (x', y)::tl -> if x=x' then Some y else assoc x tl

(** [split] takes a list of pairs [(x1, y1), ..., (xn, yn)] and
returns the pair of lists ([x1, ..., xn], [y1, ..., yn]). Named as in:
OCaml *)
val split: list ('a * 'b) -> Tot (list 'a * list 'b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)

(** [unzip] takes a list of pairs [(x1, y1), ..., (xn, yn)] and
returns the pair of lists ([x1, ..., xn], [y1, ..., yn]). Named as in:
Haskell *)
let unzip = split

(** [unzip3] takes a list of triples [(x1, y1, z1), ..., (xn, yn, zn)]
and returns the triple of lists ([x1, ..., xn], [y1, ..., yn], [z1,
..., zn]). Named as in: Haskell *)
val unzip3: list ('a * 'b * 'c) -> Tot (list 'a * list 'b * list 'c)
let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)

(** Splitting a list at some index **)

(** [splitAt] takes a natural number n and a list and returns a pair
    of the maximal prefix of l of size smaller than n and the rest of
    the list *)
let rec splitAt (#a:Type) (n:nat) (l:list a) : list a * list a =
  if n = 0 then [], l
  else
    match l with
    | [] -> [], l
    | x :: xs -> let l1, l2 = splitAt (n-1) xs in x :: l1, l2

(** Sorting (implemented as quicksort) **)

(** [partition] splits a list [l] into two lists, the sum of whose
lengths is the length of [l]. *)
val partition_length: f:('a -> Tot bool)
                    -> l:list 'a
                    -> Lemma (requires True)
                            (ensures (length (fst (partition f l))
                                      + length (snd (partition f l)) = length l))
let rec partition_length f l = match l with
  | [] -> ()
  | hd::tl -> partition_length f tl

(** [bool_of_compare] turns a comparison function into a strict
order. More precisely, [bool_of_compare compare x y] returns true if,
and only if, [compare x y] is positive. Inspired from OCaml, where
polymorphic comparison using both the [compare] function and the (>)
infix operator are such that [compare x y] is positive if, and only
if, x > y. Requires, at type-checking time, [compare] to be a pure
total function. *)
val bool_of_compare : #a:Type -> (a -> a -> Tot int) -> a -> a -> Tot bool
let bool_of_compare #a f x y = f x y > 0

(** [compare_of_bool] turns a strict order into a comparison
function. More precisely, [compare_of_bool rel x y] returns a positive
number if, and only if, x `rel` y holds. Inspired from OCaml, where
polymorphic comparison using both the [compare] function and the (>)
infix operator are such that [compare x y] is positive if, and only
if, x > y. Requires, at type-checking time, [rel] to be a pure total
function.  *)
val compare_of_bool : #a:eqtype -> (a -> a -> Tot bool) -> a -> a -> Tot int
let compare_of_bool #a rel x y =
    if x `rel` y  then 1
    else if x = y then 0
    else 0-1

let compare_of_bool_of_compare (#a:eqtype) (f:a -> a -> Tot bool)
  : Lemma (forall x y. bool_of_compare (compare_of_bool f) x y == f x y)
  = ()

(** [sortWith compare l] returns the list [l'] containing the elements
of [l] sorted along the comparison function [compare], in such a way
that if [compare x y > 0], then [x] appears before [y] in
[l']. Requires, at type-checking time, [compare] to be a pure total
function. *)
val sortWith: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo  = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     append (sortWith f lo) (pivot::sortWith f hi)

(** A l1 is a strict prefix of l2. *)

let rec strict_prefix_of (#a: Type) (l1 l2: list a)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases l2)
= match l2 with
  | [] -> False
  | _ :: q -> l1 == q \/ l1 `strict_prefix_of` q

val list_unref : #a:Type -> #p:(a -> Type0) -> list (x:a{p x}) -> Tot (list a)
let rec list_unref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_unref xs
