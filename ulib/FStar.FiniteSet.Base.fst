(*
   Copyright 2008-2021 John Li, Jay Lorch, Rustan Leino, Alex Summers,
   Dan Rosen, Nikhil Swamy, Microsoft Research, and contributors to
   the Dafny Project

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Includes material from the Dafny project
   (https://github.com/dafny-lang/dafny) which carries this license
   information:

     Created 9 February 2008 by Rustan Leino.
     Converted to Boogie 2 on 28 June 2008.
     Edited sequence axioms 20 October 2009 by Alex Summers.
     Modified 2014 by Dan Rosen.
     Copyright (c) 2008-2014, Microsoft.
     Copyright by the contributors to the Dafny Project
     SPDX-License-Identifier: MIT
*)

(**
This module declares a type and functions used for modeling
finite sets as they're modeled in Dafny.

@summary Type and functions for modeling finite sets
*)
module FStar.FiniteSet.Base

module FLT = FStar.List.Tot
open FStar.FunctionalExtensionality

let has_elements (#a: eqtype) (f: a ^-> bool) (xs: list a): prop =
  forall x. f x == x `FLT.mem` xs

// Finite sets
type set (a: eqtype) = f:(a ^-> bool){exists xs. f `has_elements` xs}

/// We represent the Dafny function [] on sets with `mem`:

let mem (#a: eqtype) (x: a) (s: set a) : bool =
  s x

/// We represent the Dafny function `Set#Card` with `cardinality`:
///
/// function Set#Card<T>(Set T): int;

let rec remove_repeats (#a: eqtype) (xs: list a)
: (ys: list a{list_nonrepeating ys /\ (forall y. FLT.mem y ys <==> FLT.mem y xs)}) =
  match xs with
  | [] -> []
  | hd :: tl -> let tl' = remove_repeats tl in if FLT.mem hd tl then tl' else hd :: tl'

let set_as_list (#a: eqtype) (s: set a): GTot (xs: list a{list_nonrepeating xs /\ (forall x. FLT.mem x xs = mem x s)}) =
  remove_repeats (FStar.IndefiniteDescription.indefinite_description_ghost (list a) (fun xs -> forall x. FLT.mem x xs = mem x s))

[@"opaque_to_smt"]
let cardinality (#a: eqtype) (s: set a) : GTot nat =
  FLT.length (set_as_list s)

let intro_set (#a: eqtype) (f: a ^-> bool) (xs: Ghost.erased (list a))
: Pure (set a)
    (requires f `has_elements` xs)
    (ensures fun _ -> True)
= Classical.exists_intro (fun xs -> f `has_elements` xs) xs;
  f 

/// We represent the Dafny function `Set#Empty` with `empty`:

let emptyset (#a: eqtype): set a = intro_set (on_dom a (fun _ -> false)) []

/// We represent the Dafny function `Set#UnionOne` with `insert`:
///
/// function Set#UnionOne<T>(Set T, T): Set T;

let insert (#a: eqtype) (x: a) (s: set a): set a =
  intro_set (on_dom _ (fun x' -> x = x' || s x')) (x :: set_as_list s)

/// We represent the Dafny function `Set#Singleton` with `singleton`:
///
/// function Set#Singleton<T>(T): Set T;

let singleton (#a: eqtype) (x: a) : set a =
  insert x emptyset

/// We represent the Dafny function `Set#Union` with `union`:
///
/// function Set#Union<T>(Set T, Set T): Set T;

let rec union_lists (#a: eqtype) (xs: list a) (ys: list a) : (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs \/ FLT.mem z ys}) =
  match xs with
  | [] -> ys
  | hd :: tl -> hd :: union_lists tl ys

let union (#a: eqtype) (s1: set a) (s2: set a) : (set a) =
  intro_set (on_dom a (fun x -> s1 x || s2 x)) (union_lists (set_as_list s1) (set_as_list s2))

/// We represent the Dafny function `Set#Intersection` with `intersection`:
///
/// function Set#Intersection<T>(Set T, Set T): Set T;

let rec intersect_lists (#a: eqtype) (xs: list a) (ys: list a)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ FLT.mem z ys}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = intersect_lists tl ys in if FLT.mem hd ys then hd :: zs' else zs'

let intersection (#a: eqtype) (s1: set a) (s2: set a) : set a =
  intro_set (on_dom a (fun x -> s1 x && s2 x)) (intersect_lists (set_as_list s1) (set_as_list s2))

/// We represent the Dafny function `Set#Difference` with `difference`:
///
/// function Set#Difference<T>(Set T, Set T): Set T;

let rec difference_lists (#a: eqtype) (xs: list a) (ys: list a)
: (zs: list a{forall z. FLT.mem z zs <==> FLT.mem z xs /\ ~(FLT.mem z ys)}) =
  match xs with
  | [] -> []
  | hd :: tl -> let zs' = difference_lists tl ys in if FLT.mem hd ys then zs' else hd :: zs'

let difference (#a: eqtype) (s1: set a) (s2: set a) : set a =
  intro_set (on_dom a (fun x -> s1 x && not (s2 x))) (difference_lists (set_as_list s1) (set_as_list s2))

/// We represent the Dafny function `Set#Subset` with `subset`:
///
/// function Set#Subset<T>(Set T, Set T): bool;

let subset (#a: eqtype) (s1: set a) (s2: set a) : Type0 =
  forall x. (s1 x = true) ==> (s2 x = true)

/// We represent the Dafny function `Set#Equal` with `equal`:
///
/// function Set#Equal<T>(Set T, Set T): bool;

let equal (#a: eqtype) (s1: set a) (s2: set a) : Type0 =
  feq s1 s2

/// We represent the Dafny function `Set#Disjoint` with `disjoint`:
///
/// function Set#Disjoint<T>(Set T, Set T): bool;

let disjoint (#a: eqtype) (s1: set a) (s2: set a) : Type0 =
  forall x. not (s1 x && s2 x)

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

let choose (#a: eqtype) (s: set a{exists x. mem x s}) : GTot (x: a{mem x s}) =
  Cons?.hd (set_as_list s)

/// We now prove each of the facts that comprise `all_finite_set_facts`.
/// For fact `xxx_fact`, we prove it with `xxx_lemma`.  Sometimes, that
/// requires a helper lemma, which we call `xxx_helper`.

let empty_set_contains_no_elements_lemma ()
: Lemma (empty_set_contains_no_elements_fact) =
  ()

let length_zero_lemma ()
: Lemma (length_zero_fact) =
  introduce forall (a: eqtype) (s: set a). (cardinality s = 0 <==> s == emptyset) /\ (cardinality s <> 0 <==> (exists x. mem x s))
  with (
    reveal_opaque (`%cardinality) (cardinality #a);
    introduce cardinality s = 0 ==> s == emptyset
    with _. assert (feq s emptyset);
    introduce s == emptyset ==> cardinality s = 0
    with _. assert (set_as_list s == []);
    introduce cardinality s <> 0 ==> _
    with _. introduce exists x. mem x s
            with (Cons?.hd (set_as_list s))
            and  ())

let singleton_contains_argument_lemma ()
: Lemma (singleton_contains_argument_fact) =
  ()

let singleton_contains_lemma ()
: Lemma (singleton_contains_fact) =
  ()

let rec singleton_cardinality_helper (#a: eqtype) (r: a) (xs: list a)
: Lemma (requires FLT.mem r xs /\ (forall x. FLT.mem x xs <==> x = r))
        (ensures  remove_repeats xs == [r]) =
  match xs with
  | [x] -> ()
  | hd :: tl ->
      assert (Cons?.hd tl = r);
      singleton_cardinality_helper r tl

let singleton_cardinality_lemma ()
: Lemma (singleton_cardinality_fact) =
  introduce forall (a: eqtype) (r: a). cardinality (singleton r) = 1
  with (
    reveal_opaque (`%cardinality) (cardinality #a);
    singleton_cardinality_helper r (set_as_list (singleton r))
  )

let insert_lemma ()
: Lemma (insert_fact) =
  ()

let insert_contains_argument_lemma ()
: Lemma (insert_contains_argument_fact) =
  ()

let insert_contains_lemma ()
: Lemma (insert_contains_fact) =
  ()

let rec remove_from_nonrepeating_list (#a: eqtype) (x: a) (xs: list a{FLT.mem x xs /\ list_nonrepeating xs})
: (xs': list a{  list_nonrepeating xs'
               /\ FLT.length xs' = FLT.length xs - 1
               /\ (forall y. FLT.mem y xs' <==> FLT.mem y xs /\ y <> x)}) =
  match xs with
  | hd :: tl -> if x = hd then tl else hd :: (remove_from_nonrepeating_list x tl)

let rec nonrepeating_lists_with_same_elements_have_same_length (#a: eqtype) (s1: list a) (s2: list a)
: Lemma (requires list_nonrepeating s1 /\ list_nonrepeating s2 /\ (forall x. FLT.mem x s1 <==> FLT.mem x s2))
        (ensures  FLT.length s1 = FLT.length s2) =
  match s1 with
  | [] -> ()
  | hd :: tl -> nonrepeating_lists_with_same_elements_have_same_length tl (remove_from_nonrepeating_list hd s2)

let insert_member_cardinality_lemma ()
: Lemma (insert_member_cardinality_fact) =
  introduce forall (a: eqtype) (s: set a) (x: a). mem x s ==> cardinality (insert x s) = cardinality s
  with
    introduce mem x s ==> cardinality (insert x s) = cardinality s
    with _. (
      reveal_opaque (`%cardinality) (cardinality #a);
      nonrepeating_lists_with_same_elements_have_same_length (set_as_list s) (set_as_list (insert x s))
    )

let insert_nonmember_cardinality_lemma ()
: Lemma (insert_nonmember_cardinality_fact) =
  introduce forall (a: eqtype) (s: set a) (x: a). not (mem x s) ==> cardinality (insert x s) = cardinality s + 1
  with
    introduce not (mem x s) ==> cardinality (insert x s) = cardinality s + 1
    with _. (
      reveal_opaque (`%cardinality) (cardinality #a);
      nonrepeating_lists_with_same_elements_have_same_length (x :: (set_as_list s)) (set_as_list (insert x s))
    )

let union_contains_lemma ()
: Lemma (union_contains_fact) =
  ()

let union_contains_element_from_first_argument_lemma ()
: Lemma (union_contains_element_from_first_argument_fact) =
  ()

let union_contains_element_from_second_argument_lemma ()
: Lemma (union_contains_element_from_second_argument_fact) =
  ()

let union_of_disjoint_lemma ()
: Lemma (union_of_disjoint_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). disjoint s1 s2 ==> difference (union s1 s2) s1 == s2 /\ difference (union s1 s2) s2 == s1
  with
    introduce disjoint s1 s2 ==> difference (union s1 s2) s1 == s2 /\ difference (union s1 s2) s2 == s1
    with _. (
      assert (feq (difference (union s1 s2) s1) s2);
      assert (feq (difference (union s1 s2) s2) s1)
    )

let intersection_contains_lemma ()
: Lemma (intersection_contains_fact) =
  ()

let union_idempotent_right_lemma ()
: Lemma (union_idempotent_right_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). union (union s1 s2) s2 == union s1 s2
  with assert (feq (union (union s1 s2) s2) (union s1 s2))

let union_idempotent_left_lemma ()
: Lemma (union_idempotent_left_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). union s1 (union s1 s2) == union s1 s2
  with assert (feq (union s1 (union s1 s2)) (union s1 s2))

let intersection_idempotent_right_lemma ()
: Lemma (intersection_idempotent_right_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). intersection (intersection s1 s2) s2 == intersection s1 s2
  with assert (feq (intersection (intersection s1 s2) s2) (intersection s1 s2))

let intersection_idempotent_left_lemma ()
: Lemma (intersection_idempotent_left_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). intersection s1 (intersection s1 s2) == intersection s1 s2
  with assert (feq (intersection s1 (intersection s1 s2)) (intersection s1 s2))

let rec union_of_disjoint_nonrepeating_lists_length_lemma (#a: eqtype) (xs1: list a) (xs2: list a) (xs3: list a)
: Lemma (requires   list_nonrepeating xs1
                  /\ list_nonrepeating xs2
                  /\ list_nonrepeating xs3
                  /\ (forall x. ~(FLT.mem x xs1 /\ FLT.mem x xs2))
                  /\ (forall x. FLT.mem x xs3 <==> FLT.mem x xs1 \/ FLT.mem x xs2))
        (ensures  FLT.length xs3 = FLT.length xs1 + FLT.length xs2) =
  match xs1 with
  | [] -> nonrepeating_lists_with_same_elements_have_same_length xs2 xs3
  | hd :: tl -> union_of_disjoint_nonrepeating_lists_length_lemma tl xs2 (remove_from_nonrepeating_list hd xs3)

let union_of_disjoint_sets_cardinality_lemma (#a: eqtype) (s1: set a) (s2: set a)
: Lemma (requires disjoint s1 s2)
        (ensures  cardinality (union s1 s2) = cardinality s1 + cardinality s2) =
  reveal_opaque (`%cardinality) (cardinality #a);
  union_of_disjoint_nonrepeating_lists_length_lemma (set_as_list s1) (set_as_list s2) (set_as_list (union s1 s2))

let union_of_three_disjoint_sets_cardinality_lemma (#a: eqtype) (s1: set a) (s2: set a) (s3: set a)
: Lemma (requires disjoint s1 s2 /\ disjoint s2 s3 /\ disjoint s1 s3)
        (ensures  cardinality (union (union s1 s2) s3) = cardinality s1 + cardinality s2 + cardinality s3) =
  union_of_disjoint_sets_cardinality_lemma s1 s2;
  union_of_disjoint_sets_cardinality_lemma (union s1 s2) s3

#restart-solver
#push-options "--z3rlimit_factor 8 --split_queries no"
let cardinality_matches_difference_plus_intersection_lemma (#a: eqtype) (s1: set a) (s2: set a)
: Lemma (ensures cardinality s1 = cardinality (difference s1 s2) + cardinality (intersection s1 s2)) =
  union_of_disjoint_sets_cardinality_lemma (difference s1 s2) (intersection s1 s2);
  assert (feq s1 (union (difference s1 s2) (intersection s1 s2)))
#pop-options
#restart-solver
let union_is_differences_and_intersection (#a: eqtype) (s1: set a) (s2: set a)
: Lemma (union s1 s2 == union (union (difference s1 s2) (intersection s1 s2)) (difference s2 s1)) =
  assert (feq (union s1 s2) (union (union (difference s1 s2) (intersection s1 s2)) (difference s2 s1)))

#restart-solver
#push-options "--z3rlimit_factor 8 --split_queries no"
let intersection_cardinality_helper (a: eqtype) (s1: set a) (s2: set a)
: Lemma (cardinality (union s1 s2) + cardinality (intersection s1 s2) = cardinality s1 + cardinality s2) =
  cardinality_matches_difference_plus_intersection_lemma s1 s2;
  cardinality_matches_difference_plus_intersection_lemma s2 s1;
  union_is_differences_and_intersection s1 s2;
  union_of_three_disjoint_sets_cardinality_lemma (difference s1 s2) (intersection s1 s2) (difference s2 s1);
  assert (feq (intersection s1 s2) (intersection s2 s1))
#pop-options 

let intersection_cardinality_lemma ()
: Lemma (intersection_cardinality_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a).
    cardinality (union s1 s2) + cardinality (intersection s1 s2) = cardinality s1 + cardinality s2
  with
    intersection_cardinality_helper a s1 s2

let difference_contains_lemma ()
: Lemma (difference_contains_fact) =
  ()

let difference_doesnt_include_lemma ()
: Lemma (difference_doesnt_include_fact) =
  ()

#restart-solver
#push-options "--z3rlimit_factor 8 --split_queries no"
let difference_cardinality_helper (a: eqtype) (s1: set a) (s2: set a)
: Lemma (  cardinality (difference s1 s2) + cardinality (difference s2 s1) + cardinality (intersection s1 s2) = cardinality (union s1 s2)
         /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2)) =
  union_is_differences_and_intersection s1 s2;
  union_of_three_disjoint_sets_cardinality_lemma (difference s1 s2) (intersection s1 s2) (difference s2 s1);
  cardinality_matches_difference_plus_intersection_lemma s1 s2
#pop-options

let difference_cardinality_lemma ()
: Lemma (difference_cardinality_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a).
                 cardinality (difference s1 s2) + cardinality (difference s2 s1) +
                   cardinality (intersection s1 s2) = cardinality (union s1 s2)
               /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2)
  with
    difference_cardinality_helper a s1 s2

let subset_helper  (a: eqtype) (s1: set a) (s2: set a)
: Lemma (subset s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 ==> mem o s2)) =
  introduce (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 ==> mem o s2) ==> subset s1 s2
  with _.
    introduce forall x. s1 x = true ==> s2 x = true
    with assert (mem x s1 = s1 x)

let subset_lemma ()
: Lemma (subset_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a). subset s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 ==> mem o s2)
  with subset_helper a s1 s2

let equal_lemma ()
: Lemma (equal_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a).
    equal s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 <==> mem o s2)
  with (
    introduce (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 <==> mem o s2) ==> equal s1 s2
    with _.
      introduce forall x. s1 x = true <==> s2 x = true
      with assert (mem x s1 = s1 x /\ mem x s2 = s2 x)
  )

let equal_extensionality_lemma ()
: Lemma (equal_extensionality_fact) =
  ()

let disjoint_lemma ()
: Lemma (disjoint_fact) =
  introduce forall (a: eqtype) (s1: set a) (s2: set a).
    disjoint s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} not (mem o s1) \/ not (mem o s2))
  with (
    introduce (forall o.{:pattern mem o s1 \/ mem o s2} not (mem o s1) \/ not (mem o s2)) ==> disjoint s1 s2
    with _. (
      introduce forall x. not (s1 x && s2 x)
      with assert (not (mem x s1) \/ not (mem x s2))
    )
  )

#restart-solver
#push-options "--z3rlimit_factor 8 --split_queries no"
let insert_remove_helper (a: eqtype) (x: a) (s: set a)
: Lemma (requires mem x s)
        (ensures  insert x (remove x s) == s) =
  assert (feq s (insert x (remove x s)))
#pop-options
#restart-solver

let insert_remove_lemma ()
: Lemma (insert_remove_fact) =
  introduce forall (a: eqtype) (x: a) (s: set a). mem x s = true ==> insert x (remove x s) == s
  with
    introduce mem x s = true ==> insert x (remove x s) == s
    with _.  insert_remove_helper a x s

let remove_insert_helper (a: eqtype) (x: a) (s: set a)
: Lemma (requires mem x s = false)
        (ensures  remove x (insert x s) == s) =
  assert (feq s (remove x (insert x s)))

let remove_insert_lemma ()
: Lemma (remove_insert_fact) =
  introduce forall (a: eqtype) (x: a) (s: set a). mem x s = false ==> remove x (insert x s) == s
  with introduce mem x s = false ==> remove x (insert x s) == s
  with _. remove_insert_helper a x s

let set_as_list_cardinality_lemma ()
: Lemma (set_as_list_cardinality_fact) = 
  introduce forall (a: eqtype) (s: set a). FLT.length (set_as_list s) = cardinality s
  with reveal_opaque (`%cardinality) (cardinality #a)

let all_finite_set_facts_lemma () : Lemma (all_finite_set_facts) =
  empty_set_contains_no_elements_lemma ();
  length_zero_lemma ();
  singleton_contains_argument_lemma ();
  singleton_contains_lemma ();
  singleton_cardinality_lemma ();
  insert_lemma ();
  insert_contains_argument_lemma ();
  insert_contains_lemma ();
  insert_member_cardinality_lemma ();
  insert_nonmember_cardinality_lemma ();
  union_contains_lemma ();
  union_contains_element_from_first_argument_lemma ();
  union_contains_element_from_second_argument_lemma ();
  union_of_disjoint_lemma ();
  intersection_contains_lemma ();
  union_idempotent_right_lemma ();
  union_idempotent_left_lemma ();
  intersection_idempotent_right_lemma ();
  intersection_idempotent_left_lemma ();
  intersection_cardinality_lemma ();
  difference_contains_lemma ();
  difference_doesnt_include_lemma ();
  difference_cardinality_lemma ();
  subset_lemma ();
  equal_lemma ();
  equal_extensionality_lemma ();
  disjoint_lemma ();
  insert_remove_lemma ();
  remove_insert_lemma ();
  set_as_list_cardinality_lemma ()
