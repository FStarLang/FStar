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
finite maps as they're modeled in Dafny.

@summary Type and functions for modeling finite maps
*)
module FStar.FiniteMap.Base

open FStar.FunctionalExtensionality
module FLT = FStar.List.Tot
module FSet = FStar.FiniteSet.Base
open FStar.FiniteSet.Ambient
module T = FStar.Tactics.V2

// Finite maps
type map (a: eqtype) (b: Type u#b) = (keys: FSet.set a & setfun_t a b keys)

let domain (#a: eqtype) (#b: Type u#b) (m: map a b) : FSet.set a =
  let (| keys, _ |) = m in 
  keys


let elements (#a: eqtype) (#b: Type u#b) (m: map a b) : (setfun_t a b (domain m)) =
  let (| _, f |) = m in
  f
  
let rec key_list_to_item_list
  (#a: eqtype)
  (#b: Type u#b)
  (m: map a b)
  (keys: list a{FSet.list_nonrepeating keys /\ (forall key. FLT.mem key keys ==> FSet.mem key (domain m))})
: GTot (items: list (a & b){item_list_doesnt_repeat_keys items /\ (forall key. FLT.mem key keys <==> key_in_item_list key items)})
       (decreases keys) =
  match keys with
  | [] -> []
  | key :: remaining_keys -> (key, Some?.v ((elements m) key)) :: key_list_to_item_list m remaining_keys

let map_as_list (#a: eqtype) (#b: Type u#b) (m: map a b)
: GTot (items: list (a & b){item_list_doesnt_repeat_keys items /\ (forall key. key_in_item_list key items <==> mem key m)}) =
  key_list_to_item_list m (FSet.set_as_list (domain m))

/// We represent the Dafny function `Map#Card` with `cardinality`:
///
/// function Map#Card<U,V>(Map U V) : int;

let cardinality (#a: eqtype) (#b: Type u#b) (m: map a b) : GTot nat =
  FSet.cardinality (domain m)

/// We represent the Dafny function `Map#Values` with `values`:
///
/// function Map#Values<U,V>(Map U V) : Set V;

let values (#a: eqtype) (#b: Type u#b) (m: map a b) : GTot (b -> prop) =
  fun value -> exists key. ((elements m) key == Some value)

/// We represent the Dafny function `Map#Items` with `items`:
///
/// function Map#Items<U,V>(Map U V) : Set Box;

let items (#a: eqtype) (#b: Type u#b) (m: map a b) : GTot ((a & b) -> prop) =
  fun item -> ((elements m) (fst item) == Some (snd item))

/// We represent the Dafny function `Map#Empty` with `emptymap`:
///
/// function Map#Empty<U, V>(): Map U V;

let emptymap (#a: eqtype) (#b: Type u#b) : (map a b) =
  (| FSet.emptyset, on_domain a (fun key -> None) |)

/// We represent the Dafny function `Map#Glue` with `glue`.
///
/// function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;

let glue (#a: eqtype) (#b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys) : map a b =
  (| keys, f |)
  
/// We represent the Dafny function `Map#Build` with `build`:
///
/// function Map#Build<U, V>(Map U V, U, V): Map U V;

let insert (#a: eqtype) (#b: Type u#b) (k: a) (v: b) (m: map a b) : map a b =
  let keys' = FSet.insert k (domain m) in
  let f' = on_domain a (fun key -> if key = k then Some v else (elements m) key) in
  (| keys', f' |)

/// We represent the Dafny function `Map#Merge` with `merge`:
///
/// function Map#Merge<U, V>(Map U V, Map U V): Map U V;

let merge (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b) : map a b =
  let keys' = FSet.union (domain m1) (domain m2) in
  let f' = on_domain a (fun key -> if FSet.mem key (domain m2) then (elements m2) key else (elements m1) key) in
  (| keys', f' |)

/// We represent the Dafny function `Map#Subtract` with `subtract`:
///
/// function Map#Subtract<U, V>(Map U V, Set U): Map U V;

let subtract (#a: eqtype) (#b: Type u#b) (m: map a b) (s: FSet.set a) : map a b =
  let keys' = FSet.difference (domain m) s in
  let f' = on_domain a (fun key -> if FSet.mem key keys' then (elements m) key else None) in
  (| keys', f' |)

/// We represent the Dafny function `Map#Equal` with `equal`:
///
/// function Map#Equal<U, V>(Map U V, Map U V): bool;

let equal (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b) : prop =
  feq (elements m1) (elements m2) /\ True //a bit ugly, a prop coercion

/// We represent the Dafny function `Map#Disjoint` with `disjoint`:
///
/// function Map#Disjoint<U, V>(Map U V, Map U V): bool;

let disjoint (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b) : prop =
  FSet.disjoint (domain m1) (domain m2) /\ True //prop coercion

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

let choose (#a: eqtype) (#b: Type u#b) (m: map a b{exists key. mem key m}) : GTot (key: a{mem key m}) =
  FSet.choose (domain m)

/// We now prove each of the facts that comprise `all_finite_map_facts`.
/// For fact `xxx_fact`, we prove it with `xxx_lemma`.

let cardinality_zero_iff_empty_lemma ()
: Lemma (cardinality_zero_iff_empty_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m: map a b). cardinality m = 0 <==> m == emptymap
  with (
    introduce cardinality m = 0 ==> m == emptymap
    with _. assert (feq (elements m) (elements emptymap))
  )


let empty_or_domain_occupied_lemma ()
  : Lemma (empty_or_domain_occupied_fact u#b)
  = introduce forall (a: eqtype) (b:Type u#b) (m: map a b). m == emptymap \/ (exists k. mem k m)
    with (  
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists k. mem k m)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma ()
      )
    else
      introduce m == emptymap \/ (exists k. mem k m)
      with Right ()
    )
    

let empty_or_values_occupied_lemma ()
: Lemma (empty_or_values_occupied_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m: map a b). m == emptymap \/ (exists v. (values m) v)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma u#b ()
      )
    else
      introduce m == emptymap \/ (exists v. (values m) v)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((values m) v)
      )

let empty_or_items_occupied_lemma ()
: Lemma (empty_or_items_occupied_fact u#b) =
  introduce forall (a: eqtype) (b: Type u#b) (m: map a b). m == emptymap \/ (exists item. (items m) item)
  with
    if FSet.cardinality (domain m) = 0 then
      introduce m == emptymap \/ (exists v. (values m) v)
      with Left (
        assert (cardinality m = 0);
        cardinality_zero_iff_empty_lemma u#b ()
      )
    else
      introduce m == emptymap \/ (exists item. (items m) item)
      with Right (
        let k = choose m in
        let v = Some?.v ((elements m) k) in
        assert ((items m) (k, v))
      )

let map_cardinality_matches_domain_lemma ()
: Lemma (map_cardinality_matches_domain_fact u#b) =
  ()

let values_contains_lemma ()
: Lemma (values_contains_fact u#b) =
  ()

let items_contains_lemma ()
: Lemma (items_contains_fact u#b) =
  ()

let empty_domain_empty_lemma ()
: Lemma (empty_domain_empty_fact u#b) =
  ()

let glue_domain_lemma ()
: Lemma (glue_domain_fact u#b) =
  ()

let glue_elements_lemma ()
: Lemma (glue_elements_fact u#b) =
  ()

let insert_elements_lemma ()
: Lemma (insert_elements_fact u#b) =
  ()

let insert_member_cardinality_lemma ()
: Lemma (insert_member_cardinality_fact u#b) =
  ()

let insert_nonmember_cardinality_lemma ()
: Lemma (insert_nonmember_cardinality_fact u#b) =
  ()

let merge_domain_is_union_lemma ()
: Lemma (merge_domain_is_union_fact u#b) =
  ()

let merge_element_lemma ()
: Lemma (merge_element_fact u#b) =
  ()

let subtract_domain_lemma ()
: Lemma (subtract_domain_fact u#b) =
  ()

let subtract_element_lemma ()
: Lemma (subtract_element_fact u#b) =
  ()


let map_equal_lemma ()
: Lemma (map_equal_fact u#b) //Surprising; needed to split this goal into two
= assert (map_equal_fact u#b)
    by (T.norm [delta_only [`%map_equal_fact]];
        let _ = T.forall_intro () in
        let _ = T.forall_intro () in
        let _ = T.forall_intro () in         
        let _ = T.forall_intro () in                 
        T.split ();
        T.smt();
        T.smt())


let map_extensionality_lemma ()
: Lemma (map_extensionality_fact u#b) =
  introduce forall (a: eqtype) (b:Type u#b) (m1: map a b) (m2: map a b). equal m1 m2 ==> m1 == m2
  with (
    introduce equal m1 m2 ==> m1 == m2
    with _. (
      assert (FSet.equal (domain m1) (domain m2));
      assert (feq (elements m1) (elements m2))
    )
  )

let disjoint_lemma ()
: Lemma (disjoint_fact u#b) =
  ()

let all_finite_map_facts_lemma (_:unit)
  : Lemma (all_finite_map_facts u#b)
  = cardinality_zero_iff_empty_lemma u#b ();
    empty_or_domain_occupied_lemma u#b ();
    empty_or_values_occupied_lemma u#b ();
    empty_or_items_occupied_lemma u#b ();
    map_cardinality_matches_domain_lemma u#b ();
    values_contains_lemma u#b ();
    items_contains_lemma u#b ();
    empty_domain_empty_lemma u#b ();
    glue_domain_lemma u#b ();
    glue_elements_lemma u#b ();
    insert_elements_lemma u#b ();
    insert_member_cardinality_lemma u#b ();
    insert_nonmember_cardinality_lemma u#b ();
    merge_domain_is_union_lemma u#b ();
    merge_element_lemma u#b ();
    subtract_domain_lemma u#b ();
    subtract_element_lemma u#b ();
    map_equal_lemma u#b ();
    map_extensionality_lemma u#b ();
    disjoint_lemma u#b ()
