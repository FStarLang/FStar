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

(** The empty list has no elements *)
val mem_empty : #a:eqtype -> x:a ->
  Lemma (requires (mem x []))
        (ensures False)
let mem_empty #a x = ()

(** Full specification for [existsb]: [existsb f xs] holds if, and
only if, there exists an element [x] of [xs] such that [f x] holds. *)
val mem_existsb: #a:eqtype -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ mem x xs))))
let rec mem_existsb #a f xs =
  match xs with
  | [] -> ()
  | hd::tl -> mem_existsb f tl

let rec mem_count
  (#a: eqtype)
  (l: list a)
  (x: a)
: Lemma
  (mem x l <==> count x l > 0)
= match l with
  | [] -> ()
  | x' :: l' -> mem_count l' x

(** Properties about rev **)

val rev_acc_length : l:list 'a -> acc:list 'a ->
  Lemma (requires True)
        (ensures (length (rev_acc l acc) = length l + length acc))
let rec rev_acc_length l acc = match l with
    | [] -> ()
    | hd::tl -> rev_acc_length tl (hd::acc)

val rev_length : l:list 'a ->
  Lemma (requires True)
        (ensures (length (rev l) = length l))
let rev_length l = rev_acc_length l []

val rev_acc_mem : #a:eqtype -> l:list a -> acc:list a -> x:a ->
  Lemma (requires True)
        (ensures (mem x (rev_acc l acc) <==> (mem x l \/ mem x acc)))
let rec rev_acc_mem #a l acc x = match l with
    | [] -> ()
    | hd::tl -> rev_acc_mem tl (hd::acc) x

(** A list and its reversed have the same elements *)
val rev_mem : #a:eqtype -> l:list a -> x:a ->
  Lemma (requires True)
        (ensures (mem x (rev l) <==> mem x l))
let rev_mem #a l x = rev_acc_mem l [] x


(** Properties about append **)

val append_nil_l: l:list 'a ->
  Lemma (requires True)
        (ensures ([]@l == l))
let append_nil_l l = ()

val append_l_nil: l:list 'a ->
  Lemma (requires True)
        (ensures (l@[] == l)) [SMTPat (l@[])]
let rec append_l_nil = function
  | [] -> ()
  | hd::tl -> append_l_nil tl

val append_cons_l: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures (((hd::tl)@l) == (hd::(tl@l))))
let append_cons_l hd tl l = ()

val append_l_cons: hd:'a -> tl:list 'a -> l:list 'a ->
  Lemma (requires True)
        (ensures ((l@(hd::tl)) == ((l@[hd])@tl)))
let rec append_l_cons hd tl l = match l with
    | [] -> ()
    | hd'::tl' -> append_l_cons hd tl tl'

val append_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
  Lemma (requires True)
        (ensures ((l1@(l2@l3)) == ((l1@l2)@l3)))
let rec append_assoc l1 l2 l3 = match l1 with
    | [] -> ()
    | hd::tl -> append_assoc tl l2 l3

val append_length: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures (length (l1@l2) = length l1 + length l2)) [SMTPat (length (l1 @ l2))]
let rec append_length l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_length tl l2

val append_mem: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (mem a (l1@l2) = (mem a l1 || mem a l2)))
                       (* [SMTPat (mem a (l1@l2))] *)
let rec append_mem #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_mem tl l2 a

val append_mem_forall: #a:eqtype -> l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. mem a (l1@l2) = (mem a l1 || mem a l2)))
let rec append_mem_forall #a l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_mem_forall tl l2

val append_count: #t:eqtype ->  l1:list t
              -> l2:list t
              -> a:t
              -> Lemma (requires True)
                       (ensures (count a (l1@l2) = (count a l1 + count a l2)))
let rec append_count #t l1 l2 a = match l1 with
  | [] -> ()
  | hd::tl -> append_count tl l2 a

val append_count_forall: #a:eqtype ->  l1:list a
              -> l2:list a
              -> Lemma (requires True)
                       (ensures (forall a. count a (l1@l2) = (count a l1 + count a l2)))
                       (* [SMTPat (l1@l2)] *)
let rec append_count_forall #a l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_count_forall tl l2

val append_eq_nil: l1:list 'a -> l2:list 'a ->
  Lemma (requires (l1@l2 == []))
        (ensures (l1 == [] /\ l2 == []))
let append_eq_nil l1 l2 = ()

val append_eq_singl: l1:list 'a -> l2:list 'a -> x:'a ->
  Lemma (requires (l1@l2 == [x]))
        (ensures ((l1 == [x] /\ l2 == []) \/ (l1 == [] /\ l2 == [x])))
let append_eq_singl l1 l2 x = ()

val append_inv_head: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l@l1) == (l@l2)))
        (ensures (l1 == l2))
let rec append_inv_head l l1 l2 = match l with
    | [] -> ()
    | hd::tl -> append_inv_head tl l1 l2

val append_inv_tail: l:list 'a -> l1:list 'a -> l2:list 'a ->
  Lemma (requires ((l1@l) == (l2@l)))
        (ensures (l1 == l2))
let rec append_inv_tail l l1 l2 = match l1, l2 with
    | [], [] -> ()
    | hd1::tl1, hd2::tl2 -> append_inv_tail l tl1 tl2
    | [], hd2::tl2 ->
       (match l with
          | [] -> ()
          | hd::tl -> append_l_cons hd tl tl2; append_inv_tail tl [] (tl2@[hd])
       (* We can here apply the induction hypothesis thanks to termination on a lexicographical ordering of the arguments! *)
       )
    | hd1::tl1, [] ->
       (match l with
          | [] -> ()
          | hd::tl -> append_l_cons hd tl tl1; append_inv_tail tl (tl1@[hd]) []
       (* Idem *)
       )

let rec append_length_inv_head
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length left1 == length left2))
  (ensures (left1 == left2 /\ right1 == right2))
  (decreases left1)
= match left1 with
  | [] -> ()
  | _ :: left1' ->    
    append_length_inv_head left1' right1 (tl left2) right2

let append_length_inv_tail
  (#a: Type)
  (left1 right1 left2 right2: list a)
: Lemma
  (requires (append left1 right1 == append left2 right2 /\ length right1 == length right2))
  (ensures (left1 == left2 /\ right1 == right2))
= append_length left1 right1;
  append_length left2 right2;
  append_length_inv_head left1 right1 left2 right2

(** The [last] element of a list remains the same, even after that list is
    [append]ed to another list. *)
let rec lemma_append_last (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0))
    (ensures (last (l1 @ l2) == last l2)) =
  match l1 with
  | [] -> ()
  | _ :: l1' -> lemma_append_last l1' l2

(** Properties mixing rev and append **)

val rev': list 'a -> Tot (list 'a)
let rec rev' = function
  | [] -> []
  | hd::tl -> (rev' tl)@[hd]
let rev'T = rev'

val rev_acc_rev': l:list 'a -> acc:list 'a ->
  Lemma (requires (True))
        (ensures ((rev_acc l acc) == ((rev' l)@acc)))
let rec rev_acc_rev' l acc = match l with
    | [] -> ()
    | hd::tl -> rev_acc_rev' tl (hd::acc); append_l_cons hd acc (rev' tl)

val rev_rev': l:list 'a ->
  Lemma (requires True)
        (ensures ((rev l) == (rev' l)))
let rev_rev' l = rev_acc_rev' l []; append_l_nil (rev' l)

val rev'_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev' (l1@l2)) == ((rev' l2)@(rev' l1))))
let rec rev'_append l1 l2 = match l1 with
    | [] -> append_l_nil (rev' l2)
    | hd::tl -> rev'_append tl l2; append_assoc (rev' l2) (rev' tl) [hd]

val rev_append: l1:list 'a -> l2:list 'a ->
  Lemma (requires True)
        (ensures ((rev (l1@l2)) == ((rev l2)@(rev l1))))
let rev_append l1 l2 = rev_rev' l1; rev_rev' l2; rev_rev' (l1@l2); rev'_append l1 l2

val rev'_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev' (rev' l) == l))
let rec rev'_involutive = function
  | [] -> ()
  | hd::tl -> rev'_append (rev' tl) [hd]; rev'_involutive tl

val rev_involutive : l:list 'a ->
  Lemma (requires True)
        (ensures (rev (rev l) == l))
let rev_involutive l = rev_rev' l; rev_rev' (rev' l); rev'_involutive l

(** Properties about snoc *)

val snoc_length : (lx:(list 'a * 'a)) ->
  Lemma (requires True)
        (ensures (length (snoc lx) = length (fst lx) + 1))
let snoc_length (l, x) = append_length l [x]

(** Reverse induction principle **)

val rev'_list_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p (rev' tl) ==> p (rev' (hd::tl)))))
        (ensures (p (rev' l)))
let rec rev'_list_ind p = function
  | [] -> ()
  | hd::tl -> rev'_list_ind p tl

val rev_ind: p:(list 'a -> Tot bool) -> l:list 'a ->
  Lemma (requires ((p []) /\ (forall hd tl. p hd ==> p (hd@[tl]))))
        (ensures (p l))
let rev_ind p l = rev'_involutive l; rev'_list_ind p (rev' l)

(** Properties about iterators **)

val map_lemma: f:('a -> Tot 'b)
             -> l:(list 'a)
             -> Lemma (requires True)
                      (ensures (length (map f l)) = length l)
                      [SMTPat (map f l)]
let rec map_lemma f l =
    match l with
    | [] -> ()
    | h::t -> map_lemma f t

(** Properties about unsnoc *)

(** [unsnoc] is the inverse of [snoc] *)
val lemma_unsnoc_snoc: #a:Type -> l:list a{length l > 0} ->
  Lemma (requires True)
    (ensures (snoc (unsnoc l) == l))
    [SMTPat (snoc (unsnoc l))]
let lemma_unsnoc_snoc #a l =
  let l', x = unsnoc l in
  let l1, l2 = l', [x] in
  lemma_splitAt_snd_length (length l - 1) l;
  // assert ((l1, l2) == splitAt (length l - 1) l);
  let rec aux (l:list a{length l > 0}) :
    Lemma (let l1, l2 = splitAt (length l - 1) l in
           append l1 l2 == l) =
    if length l = 1 then () else aux (tl l) in
  aux l

(** [unsnoc] followed by [append] can be connected to the same vice-versa. *)
let rec lemma_unsnoc_append (#a:Type) (l1 l2:list a) :
  Lemma
    (requires (length l2 > 0)) // the [length l2 = 0] is trivial
    (ensures (
        let as, a = unsnoc (l1 @ l2) in
        let bs, b = unsnoc l2 in
        as == l1 @ bs /\ a == b)) =
  match l1 with
  | [] -> ()
  | _ :: l1' -> lemma_unsnoc_append l1' l2

(** [unsnoc] gives you [last] element, which is [index]ed at [length l - 1] *)
let rec lemma_unsnoc_is_last (#t:Type) (l:list t) :
  Lemma
    (requires (length l > 0))
    (ensures (snd (unsnoc l) == last l /\ snd (unsnoc l) == index l (length l - 1))) =
  match l with
  | [_] -> ()
  | _ -> lemma_unsnoc_is_last (tl l)

(** [index]ing on the left part of an [unsnoc]d list is the same as indexing
    the original list. *)
let rec lemma_unsnoc_index (#t:Type) (l:list t) (i:nat) :
  Lemma
    (requires (length l > 0 /\ i < length l - 1))
    (ensures (
        length (fst (unsnoc l)) == length l - 1 /\ // required to index
        index (fst (unsnoc l)) i == index l i)) =
  snoc_length (unsnoc l);
  match i with
  | 0 -> ()
  | _ -> lemma_unsnoc_index (tl l) (i - 1)

(** Definition and properties about [split_using] *)

(** [split_using] splits a list at the first instance of finding an
    element in it.

    NOTE: Uses [strong_excluded_middle] axiom. *)
let rec split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (r:(list t * list t)) =
  match l with
  | [_] -> [], l
  | a :: as ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      [], l
    ) else (
      let l1', l2' = split_using as x in
      a :: l1', l2'
    )

let rec lemma_split_using (#t:Type) (l:list t) (x:t{x `memP` l}) :
  Lemma
    (ensures (
        let l1, l2 = split_using l x in
         length l2 > 0 /\
        ~(x `memP` l1) /\
         hd l2 == x /\
        append l1 l2 == l)) =
  match l with
  | [_] -> ()
  | a :: as ->
    let goal =
      let l1, l2 = split_using l x in
        length l2 > 0 /\
        ~(x `memP` l1) /\
         hd l2 == x /\
        append l1 l2 == l
    in
    FStar.Classical.or_elim
      #_ #_
      #(fun () -> goal)
      (fun (_:squash (a == x)) -> ())
      (fun (_:squash (x `memP` as)) -> lemma_split_using as x)

(** Definition of [index_of] *)

(** [index_of l x] gives the index of the leftmost [x] in [l].

    NOTE: Uses [strong_excluded_middle] axiom. *)
let rec index_of (#t:Type) (l:list t) (x:t{x `memP` l}) :
  GTot (i:nat{i < length l /\ index l i == x}) =
  match l with
  | [_] -> 0
  | a :: as ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (a == x) then (
      0
    ) else (
      1 + index_of as x
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
let rec partition_mem #a f l x = match l with
  | [] -> ()
  | hd::tl -> partition_mem f tl x

(** Same as [partition_mem], but using [forall] *)
val partition_mem_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition f l in
                                    (forall x. mem x l = (mem x l1 || mem x l2))))
let rec partition_mem_forall #a f l = match l with
  | [] -> ()
  | hd::tl -> partition_mem_forall f tl

(** If [partition f l = (l1, l2)], then for any [x], if [x] is in [l1]
(resp. [l2]), then [f x] holds (resp. does not hold) *)
val partition_mem_p_forall: #a:eqtype -> p:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                          (ensures (let l1, l2 = partition p l in
                                    (forall x. mem x l1 ==> p x) /\ (forall x. mem x l2 ==> not (p x))))
let rec partition_mem_p_forall #a p l = match l with
  | [] -> ()
  | hd::tl -> partition_mem_p_forall p tl

(** If [partition f l = (l1, l2)], then the number of occurrences of
any [x] in [l] is the same as the sum of the number of occurrences in
[l1] and [l2]. *)
val partition_count: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> x:a
                  -> Lemma (requires True)
                           (ensures (count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))
let rec partition_count #a f l x = match l with
  | [] -> ()
  | hd::tl -> partition_count f tl x

(** Same as [partition_count], but using [forall] *)
val partition_count_forall: #a:eqtype -> f:(a -> Tot bool)
                  -> l:list a
                  -> Lemma (requires True)
                           (ensures (forall x. count x l = (count x (fst (partition f l)) + count x (snd (partition f l)))))
                           (* [SMTPat (partitionT f l)] *)
let rec partition_count_forall #a f l= match l with
  | [] -> ()
  | hd::tl -> partition_count_forall f tl


(** Correctness of quicksort **)

(** Correctness of [sortWith], part 1/2: the number of occurrences of
any [x] in [sortWith f l] is the same as the number of occurrences in
[l]. *)
val sortWith_permutation: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires True)
        (ensures (forall x. count x l = count x (sortWith f l)))
        (decreases (length l))
let rec sortWith_permutation #a f l = match l with
    | [] -> ()
    | pivot::tl ->
       let hi, lo  = partition (bool_of_compare f pivot) tl in
       partition_length (bool_of_compare f pivot) tl;
       partition_count_forall (bool_of_compare f pivot) tl;
       sortWith_permutation f lo;
       sortWith_permutation f hi;
       append_count_forall (sortWith f lo) (pivot::sortWith f hi)

(** [sorted f l] holds if, and only if, any two consecutive elements
[x], [y] of [l] are such that [f x y] holds. *)
val sorted: ('a -> 'a -> Tot bool) -> list 'a -> Tot bool
let rec sorted f = function
  | []
  | [_] -> true
  | x::y::tl -> f x y && sorted f (y::tl)

(** [f] is a total order if, and only if, it is reflexive,
anti-symmetric, transitive and total. *)
type total_order (#a:Type) (f: (a -> a -> Tot bool)) =
    (forall a. f a a)                                           (* reflexivity   *)
    /\ (forall a1 a2. f a1 a2 /\ f a2 a1  ==> a1 == a2)          (* anti-symmetry *)
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
let rec append_sorted #a f l1 l2 pivot = match l1 with
  | [] -> ()
  | hd::tl -> append_sorted f tl l2 pivot

(** Correctness of [sortWith], part 2/2: the elements of [sortWith f
l] are sorted according to comparison function [f], and the elements
of [sortWith f l] are the elements of [l]. *)
val sortWith_sorted: #a:eqtype -> f:(a -> a -> Tot int) -> l:list a ->
  Lemma (requires (total_order #a (bool_of_compare f)))
        (ensures ((sorted (bool_of_compare f) (sortWith f l)) /\ (forall x. mem x l = mem x (sortWith f l))))
        (decreases (length l))
let rec sortWith_sorted #a f l = match l with
    | [] -> ()
    | pivot::tl ->
       let hi, lo  = partition (bool_of_compare f pivot) tl in
       partition_length (bool_of_compare f pivot) tl;
       partition_mem_forall (bool_of_compare f pivot) tl;
       partition_mem_p_forall (bool_of_compare f pivot) tl;
       sortWith_sorted f lo;
       sortWith_sorted f hi;
       append_mem_forall (sortWith f lo) (pivot::sortWith f hi);
       append_sorted (bool_of_compare f) (sortWith f lo) (sortWith f hi) pivot


(** Correctness of [mem] for types with decidable equality. TODO:
replace [mem] with [memP] in relevant lemmas and define the right
SMTPat to automatically recover lemmas about [mem] for types with
decidable equality *)
let rec mem_memP
  (#a: eqtype)
  (x: a)
  (l: list a)
: Lemma (ensures (mem x l <==> memP x l))
= match l with
  | [] -> ()
  | a :: q -> mem_memP x q

(** If an element can be [index]ed, then it is a [memP] of the list. *)
let rec lemma_index_memP (#t:Type) (l:list t) (i:nat{i < length l}) :
  Lemma
    (ensures (index l i `memP` l))
    [SMTPat (index l i `memP` l)] =
  match i with
  | 0 -> ()
  | _ -> lemma_index_memP (tl l) (i - 1)

(** The empty list has no elements. *)
val memP_empty : #a: Type -> x:a ->
  Lemma (requires (memP x []))
        (ensures False)
let memP_empty #a x = ()

(** Full specification for [existsb]: [existsb f xs] holds if, and
only if, there exists an element [x] of [xs] such that [f x] holds. *)
val memP_existsb: #a: Type -> f:(a -> Tot bool) -> xs:list a ->
  Lemma(ensures (existsb f xs <==> (exists (x:a). (f x = true /\ memP x xs))))
let rec memP_existsb #a f xs =
  match xs with
  | [] -> ()
  | hd::tl -> memP_existsb f tl

let rec memP_map_intro
  (#a #b: Type)
  (f: a -> Tot b)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> memP (f x) (map f l)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> memP_map_intro f x q (* NOTE: would fail if [requires memP x l] instead of [ ==> ] *)

let rec memP_map_elim
  (#a #b: Type)
  (f: a -> Tot b)
  (y: b)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP y (map f l) ==> (exists (x : a) . memP x l /\ f x == y)))
  (decreases l)
= match l with
  | [] -> ()
  | _ :: q -> memP_map_elim f y q

(** Properties of [noRepeats] *)
let noRepeats_nil
  (#a: eqtype)
: Lemma
  (ensures (noRepeats #a []))
= ()

let noRepeats_cons
  (#a: eqtype)
  (h: a)
  (tl: list a)
: Lemma
  (requires ((~ (mem h tl)) /\ noRepeats tl))
  (ensures (noRepeats #a (h::tl)))
= ()

let rec noRepeats_append_elim
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats (l1 @ l2)))
  (ensures (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))
  (decreases l1)
= match l1 with
  | [] -> ()
  | x :: q1 ->
    append_mem q1 l2 x;
    noRepeats_append_elim q1 l2

let rec noRepeats_append_intro
  (#a: eqtype)
  (l1 l2: list a)
: Lemma
  (requires (noRepeats l1 /\ noRepeats l2 /\ (forall x . mem x l1 ==> ~ (mem x l2))))
  (ensures (noRepeats (l1 @ l2)))
  (decreases l1)
= match l1 with
  | [] -> ()
  | x :: q1 ->
    append_mem q1 l2 x;
    noRepeats_append_intro q1 l2

(** Properties of [assoc] *)

let assoc_nil
  (#a: eqtype)
  (#b: Type)
  (x: a)
: Lemma
  (ensures (assoc #a #b x [] == None))
= ()

let assoc_cons_eq
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (q: list (a * b))
: Lemma
  (ensures (assoc x ((x, y) :: q) == Some y))
= ()

let assoc_cons_not_eq
  (#a: eqtype)
  (#b: Type)
  (x x': a)
  (y: b)
  (q: list (a * b))
: Lemma
  (requires (x <> x'))
  (ensures (assoc x' ((x, y) :: q) == assoc x' q))
= ()

let rec assoc_append_elim_r
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a * b))
: Lemma
  (requires (assoc x l2 == None \/ ~ (assoc x l1 == None)))
  (ensures (assoc x (l1 @ l2) == assoc x l1))
  (decreases l1)
= match l1 with
  | [] -> ()
  | (x', _) :: q -> if x = x' then () else assoc_append_elim_r x q l2

let rec assoc_append_elim_l
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l1 l2: list (a * b))
: Lemma
  (requires (assoc x l1 == None))
  (ensures (assoc x (l1 @ l2) == assoc x l2))
  (decreases l1)
= match l1 with
  | [] -> ()
  | (x', _) :: q -> if x = x' then assert False else assoc_append_elim_l x q l2

let rec assoc_memP_some
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (y: b)
  (l: list (a * b))
: Lemma
  (requires (assoc x l == Some y))
  (ensures (memP (x, y) l))
  (decreases l)
= match l with
  | [] -> ()
  | (x', _) :: q -> if x = x' then () else assoc_memP_some x y q

let rec assoc_memP_none
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a * b))
: Lemma
  (requires (assoc x l == None))
  (ensures (forall y . ~ (memP (x, y) l)))
  (decreases l)
= match l with
  | [] -> ()
  | (x', _) :: q -> if x = x' then assert False else assoc_memP_none x q

let assoc_mem
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a * b))
: Lemma
  (ensures (mem x (map fst l) <==> (exists y . assoc x l == Some y)))
= match assoc x l with
  | None ->
    assoc_memP_none x l;
    mem_memP x (map fst l);
    memP_map_elim fst x l
  | Some y ->
    assoc_memP_some x y l;
    memP_map_intro fst (x, y) l;
    mem_memP x (map fst l)

(** Properties of [fold_left] *)

let rec fold_left_invar
  (#a #b: Type)
  (f: (a -> b -> Tot a))
  (l: list b)
  (p: (a -> Tot Type0))
  : Lemma
  (requires forall (x: a) (y: b) . p x ==> memP y l ==> p (f x y) )
  (ensures forall (x: a) . p x ==> p (fold_left f x l))
=
  match l with
  | [] -> ()
  | y :: q -> fold_left_invar f q p

let rec fold_left_map
  (#a #b #c: Type)
  (f_aba: a -> b -> Tot a)
  (f_bc:  b -> Tot c)
  (f_aca: a -> c -> Tot a)
  (l: list b)
  : Lemma
  (requires forall (x: a) (y: b) . f_aba x y == f_aca x (f_bc y) )
  (ensures forall (x : a) . fold_left f_aba x l == fold_left f_aca x (map f_bc l) )
  =
  match l with
  | [] -> ()
  | y :: q -> fold_left_map f_aba f_bc f_aca q

let rec map_append
  (#a #b: Type)
  (f: a -> Tot b)
  (l1 l2: list a)
:
  Lemma
  (ensures map f (l1 @ l2) == map f l1 @ map f l2)
=
  match l1 with
  | [] -> ()
  | x :: q -> map_append f q l2

let rec fold_left_append
  (#a #b: Type)
  (f: a -> b -> Tot a)
  (l1 l2: list b)
  : Lemma
  (ensures forall x . fold_left f x (l1 @ l2) == fold_left f (fold_left f x l1) l2)
= match l1 with
  | [] -> ()
  | x :: q -> fold_left_append f q l2

let rec fold_left_monoid
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
= match l with
  | [] -> ()
  | x :: q -> fold_left_monoid opA zeroA q

let fold_left_append_monoid
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
= fold_left_append f l1 l2;
  fold_left_monoid f z l2

(* Properties of [index] *)

private let rec index_extensionality_aux
  (#a: Type)
  (l1 l2: list a)
  (l_len: (l_len: unit { length l1 == length l2 } ))
  (l_index: (i: (i: nat {i < length l1})) -> Tot (l_index: unit {index l1 i == index l2 i}))
: Lemma
  (ensures (l1 == l2))
= match (l1, l2) with
  | (a1::q1, a2::q2) ->
    let a_eq : (a_eq : unit {a1 == a2}) = l_index 0 in
    let q_len : (q_len: unit {length q1 == length q2}) = () in
    let q_index (i: (i: nat {i < length q1})) : Tot (q_index: unit {index q1 i == index q2 i}) =
      l_index (i + 1) in
    let q_eq : (q_eq : unit {l1 == l2}) = index_extensionality_aux q1 q2 q_len q_index in
    ()
  | _ -> ()

let index_extensionality
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (requires
    (length l1 == length l2 /\
    (forall (i: nat) . i < length l1 ==> index l1 i == index l2 i)))
  (ensures (l1 == l2))
= index_extensionality_aux l1 l2 () (fun i -> ())

(** Properties of [strict_prefix_of] *)

let rec strict_prefix_of_nil (#a: Type) (x: a) (l: list a)
: Lemma
  (requires True)
  (ensures (strict_prefix_of [] (x::l)))
  (decreases l)
= match l with
  | [] -> ()
  | a' :: q -> strict_prefix_of_nil a' q

let strict_prefix_of_or_eq_nil (#a: Type) (l: list a)
: Lemma
  (ensures (strict_prefix_of [] l \/ l == []))
= match l with
  | [] -> ()
  | a :: q -> strict_prefix_of_nil a q

let strict_prefix_of_cons (#a: Type) (x: a) (l: list a) :
  Lemma
  (ensures (strict_prefix_of l (x::l)))
= ()

let rec strict_prefix_of_trans (#a: Type) (l1 l2 l3: list a)
: Lemma
  (requires True)
  (ensures ((strict_prefix_of l1 l2 /\ strict_prefix_of l2 l3) ==> strict_prefix_of l1 l3))
  (decreases l3)
  [SMTPat (strict_prefix_of l1 l2); SMTPat (strict_prefix_of l2 l3)]
= match l3 with
  | [] -> ()
  | _ :: q -> strict_prefix_of_trans l1 l2 q

let rec strict_prefix_of_correct (#a) (l1 l2: list a)
: Lemma
  (requires True)
  (ensures (strict_prefix_of l1 l2 ==> l1 << l2))
  (decreases l2)
= match l2 with
  | [] -> ()
  | _ :: q ->
    strict_prefix_of_correct l1 q

let rec map_strict_prefix_of (#a #b: Type) (f: a -> Tot b) (l1: list a) (l2: list a) :
 Lemma
 (requires True)
 (ensures (strict_prefix_of l1 l2 ==> strict_prefix_of (map f l1) (map f l2)))
 (decreases l2)
= match l2 with
  | [] -> ()
  | a::q ->
    map_strict_prefix_of f l1 q

let rec mem_strict_prefix_of (#a: eqtype) (l1: list a) (m: a) (l2: list a)
: Lemma
  (requires True)
  (ensures ((mem m l1 /\ strict_prefix_of l1 l2) ==> mem m l2))
= match l2 with
  | [] -> ()
  | a :: q ->
    mem_strict_prefix_of l1 m q

let rec strict_prefix_of_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures (strict_prefix_of l1 l2 ==> (exists l3 . l2 == append l3 l1)))
= match l2 with
  | [] -> ()
  | a :: q ->
    FStar.Classical.or_elim
      #(l1 == q)
      #(strict_prefix_of l1 q)
      #(fun _ -> exists l3 . l2 == append l3 l1)
      (fun _ ->
	FStar.Classical.exists_intro (fun l3 -> l2 == append l3 l1) (a :: []))
      (fun _ ->
	FStar.Classical.exists_elim
	  (exists l3 . l2 == append l3 l1)
	  #_
	  #(fun l3 -> q == append l3 l1)
	  (strict_prefix_of_exists_append l1 q)
	  (fun l3 ->
	     FStar.Classical.exists_intro (fun l3 -> l2 == append l3 l1) (a :: l3)
	     ))

let strict_prefix_of_or_eq_exists_append
  (#a: Type)
  (l1 l2: list a)
: Lemma
  (ensures ((strict_prefix_of l1 l2 \/ l1 == l2) ==> (exists l3 . l2 == append l3 l1)))
= FStar.Classical.or_elim
    #(strict_prefix_of l1 l2)
    #(l1 == l2)
    #(fun _ -> exists l3 . l2 == append l3 l1)
    (fun _ ->
      strict_prefix_of_exists_append l1 l2)
    (fun _ ->
	FStar.Classical.exists_intro
	  (fun l3 -> l2 == append l3 l1)
	  [] )

(** Properties of << with lists *)

let precedes_tl
  (#a: Type)
  (l: list a {Cons? l})
: Lemma (ensures (tl l << l))
= ()

let rec precedes_append_cons_r
  (#a: Type)
  (l1: list a)
  (x: a)
  (l2: list a)
: Lemma
  (requires True)
  (ensures (x << append l1 (x :: l2)))
  [SMTPat (x << append l1 (x :: l2))]
= match l1 with
  | [] -> ()
  | _ :: q -> precedes_append_cons_r q x l2

let precedes_append_cons_prod_r
  (#a #b: Type)
  (l l1: list (a * b))
  (x: a)
  (y: b)
  (l2: list (a * b))
: Lemma
  (requires (l == append l1 ((x, y) :: l2)))
  (ensures (x << l /\ y << l))
  [SMTPatOr [ [ SMTPat (x << l); SMTPat (l == append l1 ((x, y) :: l2))] ; [SMTPat (y << l); SMTPat (l == append l1 ((x, y) :: l2))] ] ]
= precedes_append_cons_r l1 (x, y) l2

let rec memP_precedes
  (#a: Type)
  (x: a)
  (l: list a)
: Lemma
  (requires True)
  (ensures (memP x l ==> x << l))
  (decreases l)
= match l with
  | [] -> ()
  | y :: q ->
    FStar.Classical.or_elim
      #(x == y)
      #(memP x q)
      #(fun _ -> x << l)
      (fun _ -> ())
      (fun _ -> memP_precedes x q)

let assoc_precedes
  (#a: eqtype)
  (#b: Type)
  (x: a)
  (l: list (a * b))
  (y: b)
: Lemma
  (requires (assoc x l == Some y))
  (ensures (x << l /\ y << l))
= assoc_memP_some x y l;
  memP_precedes (x, y) l

(** Properties about find *)

let rec find_none
  (#a: Type)
  (f: (a -> Tot bool))
  (l: list a)
  (x: a)
: Lemma
  (requires (find f l == None /\ memP x l))
  (ensures (f x == false))
= let (x' :: l') = l in
  Classical.or_elim
    #(x == x')
    #(~ (x == x'))
    #(fun _ -> f x == false)
    (fun h -> ())
    (fun h -> find_none f l' x)
