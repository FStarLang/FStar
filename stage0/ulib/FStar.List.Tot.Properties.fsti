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
This module states and proves some properties about pure and total
operations on lists.

@summary Properties of pure total operations on lists
*)
module FStar.List.Tot.Properties
open FStar.List.Tot.Base

(** A list indexed by its length **)
let llist a (n:nat) = l:list a {length l = n}

(** Properties about mem **)

(** Correctness of [mem] for types with decidable equality. TODO:
replace [mem] with [memP] in relevant lemmas and define the right
SMTPat to automatically recover lemmas about [mem] for types with
decidable equality *)
val mem_memP
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma (ensures (mem x l <==> memP x l))
        [SMTPat (mem x l); SMTPat (memP x l)]

(** If an element can be [index]ed, then it is a [memP] of the list. *)
val lemma_index_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `memP` l))
    [SMTPat (index l i `memP` l)]

(** The empty list has no elements. *)
val memP_empty : #a: Type -> x:a ->
  Lemma (requires (memP x []))
        (ensures False)

(** Full specification for [existsb]: [existsb f xs] holds if, and
only if, there exists an element [x] of [xs] such that [f x] holds. *)
val memP_existsb: #a: Type -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ memP x xs))))

val memP_map_intro
  (#a #b: Type)
  (f: a -> Tot b)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> memP (f x) (map f l)))

val memP_map_elim
  (#a #b: Type)
  (f: a -> Tot b)
  (y: b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP y (map f l) ==> (exists (x : a) . memP x l /\ f x == y)))

(** The empty list has no elements *)
val mem_empty : #a:eqtype -> x:a ->
  Lemma (requires (mem x []))
        (ensures False)

(** Full specification for [existsb]: [existsb f xs] holds if, and
only if, there exists an element [x] of [xs] such that [f x] holds. *)
val mem_existsb: #a:eqtype -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ mem x xs))))

val mem_count
  (#a: eqtype)
  (l: list a)
  (x: a)
: Lemma
  (mem x l <==> count x l > 0)

(** Properties about rev **)

val rev_acc_length : l:list 'a -> acc:list 'a ->
  Lemma (requires True)
        (ensures (length (rev_acc l acc) = length l + length acc))

val rev_length : l:list 'a ->
  Lemma (requires True)
        (ensures (length (rev l) = length l))

val rev_acc_memP : #a:Type -> l:list a -> acc:list a -> x:a ->
  Lemma (requires True)
        (ensures (memP x (rev_acc l acc) <==> (memP x l \/ memP x acc)))

(** A list and its reversed have the same elements *)
val rev_memP : #a:Type -> l:list a -> x:a ->
  Lemma (requires True)
        (ensures (memP x (rev l) <==> memP x l))

val rev_mem : #a:eqtype -> l:list a -> x:a ->
  Lemma (requires True)
        (ensures (mem x (rev l) <==> mem x l))

(** Properties about append **)

val append_nil_l: l:list 'a ->
  Lemma (requires True)
        (ensures ([]@l == l))

val append_l_nil: l:list 'a ->
  Lemma (requires True)
        (ensures (l@[] == l)) [SMTPat (l@[])]

val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures (((hd::tl)@l) == (hd::(tl@l))))

val append_l_cons: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures ((l@(hd::tl)) == ((l@[hd])@tl)))

val append_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
  Lemma (requires True)
        (ensures ((l1@(l2@l3)) == ((l1@l2)@l3)))

val append_length: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures (length (l1@l2) = length l1 + length l2)) [SMTPat (length (l1 @ l2))]

val append_mem: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       (* [SMTPat (mem a (l1@l2))] *)

val append_memP: #t:Type ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (memP a (l1 `append` l2) <==> (memP a l1 \/ memP a l2)))
                       (* [SMTPat (mem a (l1@l2))] *)

val append_mem_forall: #a:eqtype -> l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. mem a (l1@l2) = (mem a l1 || mem a l2)))

val append_memP_forall: #a:Type -> l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. memP a (l1 `append` l2) <==> (memP a l1 \/ memP a l2)))


val append_count: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (count a (l1@l2) = (count a l1 + count a l2)))

val append_count_forall: #a:eqtype ->  l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. count a (l1@l2) = (count a l1 + count a l2)))
                       (* [SMTPat (l1@l2)] *)

val append_eq_nil: l1:list 'a -> l2:list 'a ->
  Lemma (requires (l1@l2 == []))
        (ensures (l1 == [] /\ l2 == []))

val append_eq_singl: l1:list 'a -> l2:list 'a -> x:'a ->
  Lemma (requires (l1@l2 == [x]))
        (ensures ((l1 == [x] /\ l2 == []) \/ (l1 == [] /\ l2 == [x])))

val append_inv_head: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l@l1) == (l@l2)))
        (ensures (l1 == l2))

val append_inv_tail: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l1@l) == (l2@l)))
        (ensures (l1 == l2))

val append_length_inv_head
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length left1 == length left2))
  (ensures (left1 == left2 /\ right1 == right2))

val append_length_inv_tail
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length right1 == length right2))
  (ensures (left1 == left2 /\ right1 == right2))

val append_injective #a (l0 l0':list a)
                        (l1 l1':list a)
  : Lemma
    (ensures
      (length l0 == length l0' \/ length l1 == length l1') /\
      append l0 l1 == append l0' l1' ==>
      l0 == l0' /\ l1 == l1')

(** The [last] element of a list remains the same, even after that list is
    [append]ed to another list. *)
val lemma_append_last (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0))
    (ensures (last (l1 @ l2) == last l2))

(** Properties mixing rev and append **)

let rec rev' (#a:Type) (xs : list a) : list a =
  match xs with
  | [] -> []
  | hd::tl -> (rev' tl)@[hd]
let rev'T = rev'

val rev_acc_rev': l:list 'a -> acc:list 'a ->
  Lemma (requires (True))
        (ensures ((rev_acc l acc) == ((rev' l)@acc)))

val rev_rev': l:list 'a ->
  Lemma (requires True)
        (ensures ((rev l) == (rev' l)))

val rev'_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev' (l1@l2)) == ((rev' l2)@(rev' l1))))

val rev_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev (l1@l2)) == ((rev l2)@(rev l1))))

val rev'_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev' (rev' l) == l))

val rev_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev (rev l) == l))

(** Properties about snoc *)

val lemma_snoc_length : (lx:(list 'a & 'a)) ->
  Lemma (requires True)
        (ensures (length (snoc lx) = length (fst lx) + 1))

(** Reverse induction principle **)

val rev'_list_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p (rev' tl) ==> p (rev' (hd::tl)))))
        (ensures (p (rev' l)))

val rev_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p hd ==> p (hd@[tl]))))
        (ensures (p l))

(** Properties about iterators **)

val map_lemma: f:('a -> Tot 'b)
             -> l:(list 'a)
             -> Lemma (requires True)
                      (ensures (length (map f l)) = length l)
                      [SMTPat (map f l)]

(** Properties about unsnoc *)

(** [unsnoc] is the inverse of [snoc] *)
val lemma_unsnoc_snoc: #a:Type -> l:list a{length l > 0} ->
  Lemma (requires True)
    (ensures (snoc (unsnoc l) == l))
    [SMTPat (snoc (unsnoc l))]

(** [snoc] is the inverse of [unsnoc] *)
val lemma_snoc_unsnoc: #a:Type -> lx:(list a & a) ->
  Lemma (requires True)
    (ensures (unsnoc (snoc lx) == lx))
    [SMTPat (unsnoc (snoc lx))]

(** Doing an [unsnoc] gives us a list that is shorter in length by 1 *)
val lemma_unsnoc_length: #a:Type -> l:list a{length l > 0} ->
  Lemma (requires True)
    (ensures (length (fst (unsnoc l)) == length l - 1))

(** [unsnoc] followed by [append] can be connected to the same vice-versa. *)
val lemma_unsnoc_append (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0)) // the [length l2 = 0] is trivial
    (ensures (
        let al, a = unsnoc (l1 @ l2) in
        let bl, b = unsnoc l2 in
        al == l1 @ bl /\ a == b))

(** [unsnoc] gives you [last] element, which is [index]ed at [length l - 1] *)
val lemma_unsnoc_is_last (#t:Type) (l:list t) :
  Lemma
    (requires (length l > 0))
    (ensures (snd (unsnoc l) == last l /\ snd (unsnoc l) == index l (length l - 1))) 

(** [index]ing on the left part of an [unsnoc]d list is the same as indexing
    the original list. *)
val lemma_unsnoc_index (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (
        i < length (fst (unsnoc l)) /\
        index (fst (unsnoc l)) i == index l i))

(** Definition and properties about [split_using] *)

(** [split_using] splits a list at the first instance of finding an
    element in it.

    NOTE: Uses [strong_excluded_middle] axiom. *)
let rec split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (list t & list t) =
  match l with
  | [_] -> [], l
  | a :: rest ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      [], l
    ) else (
      let l1', l2' = split_using rest x in
      a :: l1', l2'
    )

val lemma_split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  Lemma
    (ensures (
        let l1, l2 = split_using l x in
         length l2 > 0 /\
        ~(x `memP` l1) /\
         hd l2 == x /\
        append l1 l2 == l))

(** Definition of [index_of] *)

(** [index_of l x] gives the index of the leftmost [x] in [l].

    NOTE: Uses [strong_excluded_middle] axiom. *)
let rec index_of (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (i:nat{i < length l /\ index l i == x}) =
  match l with
  | [_] -> 0
  | a :: rest ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      0
    ) else (
      1 + index_of rest x
    )


(** Properties about partition **)

(** If [partition f l = (l1, l2)], then for any [x], [x] is in [l] if
and only if [x] is in either one of [l1] or [l2] *)
val partition_mem: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> x:a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition f l in
                                    mem x l = (mem x l1 || mem x l2)))

(** Same as [partition_mem], but using [forall] *)
val partition_mem_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition f l in
                                    (forall x. mem x l = (mem x l1 || mem x l2))))

(** If [partition f l = (l1, l2)], then for any [x], if [x] is in [l1]
(resp. [l2]), then [f x] holds (resp. does not hold) *)
val partition_mem_p_forall: #a:eqtype -> p:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition p l in
                                    (forall x. mem x l1 ==> p x) /\ (forall x. mem x l2 ==> not (p x))))

(** If [partition f l = (l1, l2)], then the number of occurrences of
any [x] in [l] is the same as the sum of the number of occurrences in
[l1] and [l2]. *)
val partition_count: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> x:a
                  -> Lemma (requires True)
                           (ensures (count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))

(** Same as [partition_count], but using [forall] *)
val partition_count_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                           (ensures (forall x. count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))
                           (* [SMTPat (partitionT f l)] *)

(** Properties about subset **)

val mem_subset (#a: eqtype) (la lb: list a)
    : Lemma (subset la lb <==> (forall x. mem x la ==> mem x lb))
            [SMTPat (subset la lb)]

(* NOTE: This is implied by mem_subset above, kept for compatibility *)
val subset_reflexive (#a: eqtype) (l: list a)
    : Lemma (subset l l)

(** Correctness of quicksort **)

(** Correctness of [sortWith], part 1/2: the number of occurrences of
any [x] in [sortWith f l] is the same as the number of occurrences in
[l]. *)
val sortWith_permutation: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires True)
        (ensures (forall x. count x l = count x (sortWith f l)))

(** [sorted f l] holds if, and only if, any two consecutive elements
    [x], [y] of [l] are such that [f x y] holds
 *)
let rec sorted (#a:Type) (f : a -> a -> Tot bool) : list a -> bool = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

(** [f] is a total order if, and only if, it is reflexive,
anti-symmetric, transitive and total. *)
type total_order (#a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. f a1 a2 /\ f a2 a1  ==> a1 == a2)         (* anti-symmetry *)
    /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)        (* transitivity  *)
    /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                       (* totality *)

(** Correctness of the merging of two sorted lists around a pivot. *)
val append_sorted: #a:eqtype
               ->  f:(a -> a -> Tot bool)
               ->  l1:list a{sorted f l1}
               ->  l2:list a{sorted f l2}
               ->  pivot:a
               ->  Lemma (requires (total_order #a f
                                    /\ (forall y. mem y l1 ==> not(f pivot y))
                                    /\ (forall y. mem y l2 ==> f pivot y)))
                        (ensures (sorted f (l1@(pivot::l2))))
                        [SMTPat (sorted f (l1@(pivot::l2)))]

(** Correctness of [sortWith], part 2/2: the elements of [sortWith f
l] are sorted according to comparison function [f], and the elements
of [sortWith f l] are the elements of [l]. *)
val sortWith_sorted: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires (total_order #a (bool_of_compare f)))
        (ensures ((sorted (bool_of_compare f) (sortWith f l)) /\ (forall x. mem x l = mem x (sortWith f l))))

(** Properties of [noRepeats] *)
val noRepeats_nil
  (#a: eqtype)
: Lemma
  (ensures (noRepeats #a []))

val noRepeats_cons
  (#a: eqtype)
  (h: a)
  (tl: list a)
: Lemma
  (requires ((~ (mem h tl)) /\ noRepeats tl))
  (ensures (noRepeats #a (h::tl)))

val noRepeats_append_elim
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats (l1 @ l2)))
  (ensures (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))

val noRepeats_append_intro
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))
  (ensures (noRepeats (l1 @ l2)))

(** Properties of [no_repeats_p] *)
val no_repeats_p_nil
  (#a: Type)
: Lemma
  (ensures (no_repeats_p #a []))

val no_repeats_p_cons
  (#a: Type)
  (h: a)
  (tl: list a)
: Lemma
  (requires ((~ (memP h tl)) /\ no_repeats_p tl))
  (ensures (no_repeats_p #a (h::tl)))

val no_repeats_p_append_elim
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires (no_repeats_p (l1 `append` l2)))
  (ensures (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2))))

val no_repeats_p_append_intro
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2))))
  (ensures (no_repeats_p (l1 `append` l2)))

val no_repeats_p_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (no_repeats_p (l1 `append` l2) <==> (
    (no_repeats_p l1 /\ no_repeats_p l2 /\ (forall x . memP x l1 ==> ~ (memP x l2)))
  ))

val no_repeats_p_append_swap
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (no_repeats_p (l1 `append` l2) <==> no_repeats_p (l2 `append` l1))

val no_repeats_p_append_permut
  (#a: Type)
  (l1 l2 l3 l4 l5: list a)
: Lemma
  ((no_repeats_p (l1 `append` (l2 `append` (l3 `append` (l4 `append` l5))))) <==> no_repeats_p (l1 `append` (l4 `append` (l3 `append` (l2 `append` l5)))))

val no_repeats_p_false_intro
  (#a: Type)
  (l1 l l2 l3: list a)
: Lemma
  (requires (Cons? l))
  (ensures (~ (no_repeats_p (l1 `append` (l `append` (l2 `append` (l `append` l3)))))))

(** Properties of [assoc] *)

val assoc_nil
  (#a: eqtype)
  (#b: Type)
  (x: a)
: Lemma
  (ensures (assoc #a #b x [] == None))

val assoc_cons_eq
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (q: list (a & b))
: Lemma
  (ensures (assoc x ((x, y) :: q) == Some y))

val assoc_cons_not_eq
  (#a: eqtype)
  (#b: Type)
  (x x': a)
  (y: b)
  (q: list (a & b))
: Lemma
  (requires (x <> x'))
  (ensures (assoc x' ((x, y) :: q) == assoc x' q))

val assoc_append_elim_r
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a & b))
: Lemma
  (requires (assoc x l2 == None \/ ~ (assoc x l1 == None)))
  (ensures (assoc x (l1 @ l2) == assoc x l1))

val assoc_append_elim_l
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a & b))
: Lemma
  (requires (assoc x l1 == None))
  (ensures (assoc x (l1 @ l2) == assoc x l2))

val assoc_memP_some
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (l: list (a & b))
: Lemma
  (requires (assoc x l == Some y))
  (ensures (memP (x, y) l))

val assoc_memP_none
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
: Lemma
  (requires (assoc x l == None))
  (ensures (forall y . ~ (memP (x, y) l)))

val assoc_mem
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
: Lemma
  (ensures (mem x (map fst l) <==> (exists y . assoc x l == Some y)))

(** Properties of [fold_left] *)

val fold_left_invar
  (#a #b: Type)
  (f: (a -> b -> Tot a))
  (l: list b)
  (p: (a -> Tot Type0))
  : Lemma
  (requires forall (x: a) (y: b) . p x ==> memP y l ==> p (f x y) )
  (ensures forall (x: a) . p x ==> p (fold_left f x l))

val fold_left_map
  (#a #b #c: Type)
  (f_aba: a -> b -> Tot a)
  (f_bc:  b -> Tot c)
  (f_aca: a -> c -> Tot a)
  (l: list b)
  : Lemma
  (requires forall (x: a) (y: b) . f_aba x y == f_aca x (f_bc y) )
  (ensures forall (x : a) . fold_left f_aba x l == fold_left f_aca x (map f_bc l) )

val map_append
  (#a #b: Type)
  (f: a -> Tot b)
  (l1 l2: list a)
:
  Lemma
  (ensures map f (l1 @ l2) == map f l1 @ map f l2)

val fold_left_append
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (l1 l2: list b)
  : Lemma
  (ensures forall x . fold_left f x (l1 @ l2) == fold_left f (fold_left f x l1) l2)

val fold_left_monoid
  (#a: Type)
  (opA: (a -> a -> Tot a))
  (zeroA: a)
  (l: list a)
: Lemma
  (requires
    (forall u v w . (u `opA` (v `opA` w)) == ((u `opA` v) `opA` w)) /\
    (forall x . (x `opA` zeroA) == x) /\
    (forall x . (zeroA `opA` x) == x))
  (ensures
    forall x .
    (fold_left opA x l) == (x `opA` (fold_left opA zeroA l)))

val fold_left_append_monoid
  (#a: Type)
  (f: (a -> a -> Tot a))
  (z: a)
  (l1 l2: list a)
: Lemma
  (requires
    (forall u v w . f u (f v w) == f (f u v) w) /\
    (forall x . f x z == x) /\
    (forall x . f z x == x))
  (ensures
    fold_left f z (l1 @ l2) == f (fold_left f z l1) (fold_left f z l2))

(* Properties of [index] *)

val index_extensionality
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires
    (length l1 == length l2 /\
    (forall (i: nat) . i < length l1 ==> index l1 i == index l2 i)))
  (ensures (l1 == l2))

(** Properties of [strict_suffix_of] *)

val strict_suffix_of_nil (#a: Type) (x: a) (l: list a)
: Lemma
  (requires True)
  (ensures (strict_suffix_of [] (x::l)))

val strict_suffix_of_or_eq_nil (#a: Type) (l: list a)
: Lemma
  (ensures (strict_suffix_of [] l \/ l == []))

val strict_suffix_of_cons (#a: Type) (x: a) (l: list a) :
  Lemma
  (ensures (strict_suffix_of l (x::l)))

val strict_suffix_of_trans (#a: Type) (l1 l2 l3: list a)
: Lemma
  (requires True)
  (ensures ((strict_suffix_of l1 l2 /\ strict_suffix_of l2 l3) ==> strict_suffix_of l1 l3))
  [SMTPat (strict_suffix_of l1 l2); SMTPat (strict_suffix_of l2 l3)]

val strict_suffix_of_correct (#a:Type) (l1 l2: list a)
: Lemma
  (requires True)
  (ensures (strict_suffix_of l1 l2 ==> l1 << l2))

val map_strict_suffix_of (#a #b: Type) (f: a -> Tot b) (l1: list a) (l2: list a) :
 Lemma
 (requires True)
 (ensures (strict_suffix_of l1 l2 ==> strict_suffix_of (map f l1) (map f l2)))

val mem_strict_suffix_of (#a: eqtype) (l1: list a) (m: a) (l2: list a)
: Lemma
  (requires True)
  (ensures ((mem m l1 /\ strict_suffix_of l1 l2) ==> mem m l2))

val strict_suffix_of_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures (strict_suffix_of l1 l2 ==> (exists l3 . l2 == append l3 l1)))

val strict_suffix_of_or_eq_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures ((strict_suffix_of l1 l2 \/ l1 == l2) ==> (exists l3 . l2 == append l3 l1)))

(** Properties of << with lists *)

val precedes_tl
  (#a: Type)
  (l: list a {Cons? l})
: Lemma (ensures (tl l << l))

val precedes_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (requires True)
  (ensures (x << append l1 (x :: l2)))
  [SMTPat (x << append l1 (x :: l2))]

val precedes_append_cons_prod_r
  (#a #b: Type)
  (l1: list (a & b))
  (x: a)
  (y: b)
  (l2: list (a & b))
: Lemma
  (ensures
    x << (append l1 ((x, y) :: l2)) /\
    y << (append l1 ((x, y) :: l2)))

val memP_precedes
  (#a: Type)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> x << l))

val assoc_precedes
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a & b))
  (y: b)
: Lemma
  (requires (assoc x l == Some y))
  (ensures (x << l /\ y << l))

(** Properties about find *)

val find_none
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
  (x: a)
: Lemma
  (requires (find f l == None /\ memP x l))
  (ensures (f x == false))

(** Properties of init and last *)

val append_init_last (#a: Type) (l: list a { Cons? l }) : Lemma
  (l == append (init l) [last l])

val init_last_def (#a: Type) (l: list a) (x: a) : Lemma
  (let l' = append l [x] in
  init l' == l /\ last l' == x)

val init_last_inj (#a: Type) (l1: list a { Cons? l1 } ) (l2: list a { Cons? l2 } ) : Lemma
  (requires (init l1 == init l2 /\ last l1 == last l2))
  (ensures (l1 == l2))

(* Properties of for_all *)

val for_all_append #a (f: a -> Tot bool) (s1 s2: list a): Lemma
  (ensures for_all f (s1 @ s2) <==> for_all f s1 && for_all f s2)