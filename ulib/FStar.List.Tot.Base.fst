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
used in specifications. It is implemented by FStar_List_Tot_Base.ml, any
functional change and/or the addition of new functions MUST be reflected
there.

@summary Pure total operations on lists
*)
module FStar.List.Tot.Base

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

(** Defines notation [@@] for [append], as in OCaml, F# . *)
let op_At x y = append x y

(** [snoc (l, x)] adds [x] to the end of the list [l].

    Note: We use an uncurried [snoc (l, x)] instead of the curried
    [snoc l x]. This is intentional. If [snoc] takes a pair instead
    of 2 arguments, it allows for a better pattern on
    [lemma_unsnoc_snoc], which connects [snoc] and [unsnoc]. In
    particular, if we had two arguments, then either the pattern would
    either be too restrictive or would lead to over-triggering. More
    context for this can be seen in the (collapsed and uncollapsed)
    comments at https://github.com/FStarLang/FStar/pull/1560 *)
val snoc: (list 'a & 'a) -> Tot (list 'a)
let snoc (l, x) = append l [x]

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

(** [mapi_init f l n] applies, for each [k], [f (n+k)] to the [k]-th
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

(** [fold_right_gtot] is just like [fold_right], except `f` is
    a ghost function **)
let rec fold_right_gtot (#a:Type) (#b:Type) (l:list a) (f:a -> b -> GTot b) (x:b)
  : GTot b
  = match l with
    | [] -> x
    | hd::tl -> f hd (fold_right_gtot tl f x)

(* We define map in terms of fold, to share simple lemmas *)
let map_gtot #a #b (f:a -> GTot b) (x:list a)
  : GTot (list b)
  = fold_right_gtot x (fun x tl -> f x :: tl) []

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

(** Propositional membership (as in Coq). Does not require decidable
equality. *)

(** [memP x l] holds if, and only if, [x] appears as an
element of [l]. Similar to: List.In in Coq. *)
let rec memP (#a: Type) (x: a) (l: list a) : Tot Type0 =
  match l with
  | [] -> False
  | y :: q -> x == y \/ memP x q

(** List searching **)

(** [mem x l] returns [true] if, and only if, [x] appears as an
element of [l]. Requires, at type-checking time, the type of elements
of [l] to have decidable equality. Named as in: OCaml. See also:
List.In in Coq, which is propositional. *)
val mem: #a:eqtype -> a -> list a -> Tot bool
let rec mem #a x = function
  | [] -> false
  | hd::tl -> if hd = x then true else mem x tl

(** [contains x l] returns [true] if, and only if, [x] appears as an
element of [l]. Requires, at type-checking time, the type of elements
of [l] to have decidable equality. It is equivalent to: [mem x
l]. TODO: should we rather swap the order of arguments? *)
let contains : #a:eqtype -> a -> list a -> Tot bool = mem

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

(** [filter f l] returns [l] with all elements [x] such that [f x]
does not hold removed. Requires, at type-checking time, [f] to be a
pure total function.  Named as in: OCaml, Coq *)
val filter : #a: Type -> f:(a -> Tot bool) -> l: list a -> Tot (list a)
let rec filter #a f = function
  | [] -> []
  | hd::tl -> if f hd then hd::filter f tl else filter f tl

(** Postcondition on [filter f l]: for any element [x] of [filter f l],
[x] is a member of [l] and [f x] holds. Requires, at type-checking time,
[f] to be a pure total function.*)
let rec mem_filter (#a: Type) (f: (a -> Tot bool)) (l: list a) (x: a)
    : Lemma (memP x (filter f l) <==> memP x l /\ f x) =
  match l with
  | [] -> ()
  | hd :: tl -> mem_filter f tl x

(** Postcondition on [filter f l]: stated with [forall]: for any element
[x] of [filter f l], [x] is a member of [l] and [f x] holds. Requires,
at type-checking time, [f] to be a pure total function.*)
let mem_filter_forall (#a: Type) (f: (a -> Tot bool)) (l: list a)
    : Lemma (forall x. memP x (filter f l) <==> memP x l /\ f x)
            [SMTPat (filter f l)] =
  introduce forall x . memP x (filter f l) <==> memP x l /\ f x
  with mem_filter f l x

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
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
: Lemma
  (for_all f l <==> (forall x . memP x l ==> f x))
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
val partition: f:('a -> Tot bool) -> list 'a -> Tot (list 'a & list 'a)
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


(** [no_repeats_p l] valid if, and only if, no element of [l]
appears in [l] more than once. *)
val no_repeats_p : #a:Type -> list a -> Tot prop
let rec no_repeats_p #a la =
  match la with
  | [] -> True
  | h :: tl -> ~(memP h tl) /\ no_repeats_p tl

(** List of tuples **)

(** [assoc x l] returns [Some y] where [(x, y)] is the first element
of [l] whose first element is [x], or [None] only if no such element
exists. Requires, at type-checking time, the type of [x] to have
decidable equality. Named as in: OCaml. *)
val assoc: #a:eqtype -> #b:Type -> a -> list (a & b) -> Tot (option b)
let rec assoc #a #b x = function
  | [] -> None
  | (x', y)::tl -> if x=x' then Some y else assoc x tl

(** [split] takes a list of pairs [(x1, y1), ..., (xn, yn)] and
returns the pair of lists ([x1, ..., xn], [y1, ..., yn]). Named as in:
OCaml *)
val split: list ('a & 'b) -> Tot (list 'a & list 'b)
let rec split l = match l with
    | [] -> ([],[])
    | (hd1,hd2)::tl ->
       let (tl1,tl2) = split tl in
       (hd1::tl1,hd2::tl2)

(** [unzip] takes a list of pairs [(x1, y1), ..., (xn, yn)] and
returns the pair of lists ([x1, ..., xn], [y1, ..., yn]). Named as in:
Haskell *)
let unzip l = split l

(** [unzip3] takes a list of triples [(x1, y1, z1), ..., (xn, yn, zn)]
and returns the triple of lists ([x1, ..., xn], [y1, ..., yn], [z1,
..., zn]). Named as in: Haskell *)
val unzip3: list ('a & 'b & 'c) -> Tot (list 'a & list 'b & list 'c)
let rec unzip3 l = match l with
    | [] -> ([],[],[])
    | (hd1,hd2,hd3)::tl ->
       let (tl1,tl2,tl3) = unzip3 tl in
       (hd1::tl1,hd2::tl2,hd3::tl3)

(** Splitting a list at some index **)

(** [splitAt] takes a natural number n and a list and returns a pair
    of the maximal prefix of l of size smaller than n and the rest of
    the list *)
let rec splitAt (#a:Type) (n:nat) (l:list a) : Tot (list a & list a) =
  if n = 0 then [], l
  else
    match l with
    | [] -> [], l
    | x :: xs -> let l1, l2 = splitAt (n-1) xs in x :: l1, l2

let rec lemma_splitAt_snd_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures (length (snd (splitAt n l)) = length l - n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_snd_length (n - 1) l'

(** [unsnoc] is an inverse of [snoc]. It splits a list into
    all-elements-except-last and last element. *)
val unsnoc: #a:Type -> l:list a{length l > 0} -> Tot (list a & a)
let unsnoc #a l =
  let l1, l2 = splitAt (length l - 1) l in
  lemma_splitAt_snd_length (length l - 1) l;
  l1, hd l2

(** [split3] splits a list into 3 parts. This allows easy access to
    the part of the list before and after the element, as well as the
    element itself. *)
val split3: #a:Type -> l:list a -> i:nat{i < length l} -> Tot (list a & a & list a)
let split3 #a l i =
  let a, rest = splitAt i l in
  lemma_splitAt_snd_length i l;
  let b :: c = rest in
  a, b, c

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
    order. More precisely, [bool_of_compare compare x y] returns true
    if, and only if, [compare x y] is negative, meaning [x] precedes
    [y] in the ordering defined by compare.

    This is used in sorting, and is defined to be consistent with
    OCaml and F#, where sorting is performed in ascending order.
*)
val bool_of_compare : #a:Type -> (a -> a -> Tot int) -> a -> a -> Tot bool
let bool_of_compare #a f x y = f x y < 0

(** [compare_of_bool] turns a strict order into a comparison
function. More precisely, [compare_of_bool rel x y] returns a positive
number if, and only if, x `rel` y holds. Inspired from OCaml, where
polymorphic comparison using both the [compare] function and the (>)
infix operator are such that [compare x y] is positive if, and only
if, x > y. Requires, at type-checking time, [rel] to be a pure total
function.  *)
val compare_of_bool : #a:eqtype -> (a -> a -> Tot bool) -> a -> a -> Tot int
let compare_of_bool #a rel x y =
    if x `rel` y  then -1
    else if x = y then 0
    else 1

let compare_of_bool_of_compare (#a:eqtype) (f:a -> a -> Tot bool)
  : Lemma (forall x y. bool_of_compare (compare_of_bool f) x y == f x y)
  = ()

(** [sortWith compare l] returns the list [l'] containing the elements
    of [l] sorted along the comparison function [compare], in such a
    way that if [compare x y > 0], then [x] appears before [y] in
    [l']. Sorts in ascending order *)
val sortWith: ('a -> 'a -> Tot int) -> l:list 'a -> Tot (list 'a) (decreases (length l))
let rec sortWith f = function
  | [] -> []
  | pivot::tl ->
     let hi, lo = partition (bool_of_compare f pivot) tl in
     partition_length (bool_of_compare f pivot) tl;
     append (sortWith f lo) (pivot::sortWith f hi)

(** A l1 is a strict suffix of l2. *)
let rec strict_suffix_of (#a: Type) (l1 l2: list a)
: Pure Type0
  (requires True)
  (ensures (fun _ -> True))
  (decreases l2)
= match l2 with
  | [] -> False
  | _ :: q -> l1 == q \/ l1 `strict_suffix_of` q

[@@deprecated "This function was misnamed: Please use 'strict_suffix_of'"]
let strict_prefix_of = strict_suffix_of

val list_unref : #a:Type -> #p:(a -> Type0) -> list (x:a{p x}) -> Tot (list a)
let rec list_unref #a #p l =
    match l with
    | [] -> []
    | x::xs -> x :: list_unref xs

val list_refb: #a:eqtype -> #p:(a -> Tot bool) ->
  l:list a { for_all p l } ->
  Tot (l':list (x:a{ p x }) {
    length l = length l' /\
    (forall i. {:pattern (index l i) } index l i = index l' i) })
let rec list_refb #a #p l =
  match l with
  | hd :: tl -> hd :: list_refb #a #p tl
  | [] -> []

val list_ref: #a:eqtype -> #p:(a -> Tot prop) -> l:list a {
  forall x. {:pattern mem x l} mem x l ==> p x
} -> Tot (l':list (x:a{ p x }) {
    length l = length l' /\
    (forall i. {:pattern (index l i) } index l i = index l' i) })
let rec list_ref #a #p l =
  match l with
  | hd :: tl ->
      assert (mem hd l);
      assert (p hd);
      assert (forall x. {:pattern mem x tl} mem x tl ==> mem x l);
      hd :: list_ref #a #p tl
  | [] -> []
