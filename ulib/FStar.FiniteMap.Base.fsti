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

type setfun_t (a: eqtype)
              (b: Type u#b)
              (s: FSet.set a) =
   f: (a ^-> option b){forall (key: a). FSet.mem key s == Some? (f key)}

val map (a: eqtype) ([@@@ strictly_positive] b: Type u#b)
  : Type u#b

(**
  We translate each Dafny sequence function prefixed with `Map#`
  into an F* function.
**)

/// We represent the Dafny function `Map#Domain` with `domain`:
///
/// function Map#Domain<U,V>(Map U V) : Set U;

val domain (#a: eqtype) (#b: Type u#b) (m: map a b)
  : FSet.set a

/// We represent the Dafny function `Map#Elements` with `elements`:
///
/// function Map#Elements<U,V>(Map U V) : [U]V;

val elements (#a: eqtype) (#b: Type u#b) (m: map a b)
  : setfun_t a b (domain m)

/// We represent the Dafny operator `in` on maps with `mem`:

let mem (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b) =
  FSet.mem key (domain m)

/// We can convert a map to a list of pairs with `map_as_list`:

let rec key_in_item_list (#a: eqtype) (#b: Type u#b) (key: a) (items: list (a & b)) : bool =
  match items with
  | [] -> false
  | (k, v) :: tl -> key = k || key_in_item_list key tl

let rec item_list_doesnt_repeat_keys (#a: eqtype) (#b: Type u#b) (items: list (a & b)) : bool =
  match items with
  | [] -> true
  | (k, v) :: tl -> not (key_in_item_list k tl) && item_list_doesnt_repeat_keys tl

val map_as_list (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot (items: list (a & b){item_list_doesnt_repeat_keys items /\ (forall key. key_in_item_list key items <==> mem key m)})

/// We represent the Dafny operator [] on maps with `lookup`:

let lookup (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b{mem key m})
  : b =
  Some?.v ((elements m) key)

/// We represent the Dafny function `Map#Card` with `cardinality`:
///
/// function Map#Card<U,V>(Map U V) : int;

val cardinality (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot nat

/// We represent the Dafny function `Map#Values` with `values`:
///
/// function Map#Values<U,V>(Map U V) : Set V;

val values (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot (b -> prop)

/// We represent the Dafny function `Map#Items` with `items`:
///
/// function Map#Items<U,V>(Map U V) : Set Box;

val items (#a: eqtype) (#b: Type u#b) (m: map a b)
  : GTot ((a & b) -> prop)

/// We represent the Dafny function `Map#Empty` with `emptymap`:
///
/// function Map#Empty<U, V>(): Map U V;

val emptymap (#a: eqtype) (#b: Type u#b)
  : map a b

/// We represent the Dafny function `Map#Glue` with `glue`.
///
/// function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;

val glue (#a: eqtype) (#b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys)
  : map a b

/// We represent the Dafny function `Map#Build` with `insert`:
///
/// function Map#Build<U, V>(Map U V, U, V): Map U V;

val insert (#a: eqtype) (#b: Type u#b) (k: a) (v: b) (m: map a b)
  : map a b

/// We represent the Dafny function `Map#Merge` with `merge`:
///
/// function Map#Merge<U, V>(Map U V, Map U V): Map U V;

val merge (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : map a b

/// We represent the Dafny function `Map#Subtract` with `subtract`:
///
/// function Map#Subtract<U, V>(Map U V, Set U): Map U V;

val subtract (#a: eqtype) (#b: Type u#b) (m: map a b) (s: FSet.set a)
  : map a b

/// We represent the Dafny function `Map#Equal` with `equal`:
///
/// function Map#Equal<U, V>(Map U V, Map U V): bool;

val equal (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : prop

/// We represent the Dafny function `Map#Disjoint` with `disjoint`:
///
/// function Map#Disjoint<U, V>(Map U V, Map U V): bool;

val disjoint (#a: eqtype) (#b: Type u#b) (m1: map a b) (m2: map a b)
  : prop

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

val choose (#a: eqtype) (#b: Type u#b) (m: map a b{exists key. mem key m})
  : GTot (key: a{mem key m})

/// We add the utility functions `remove` and `notin`:

let remove (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b)
  : map a b =
  subtract m (FSet.singleton key)

let notin (#a: eqtype) (#b: Type u#b) (key: a) (m: map a b)
  : bool =
  not (mem key m)

(**
  We translate each finite map axiom from the Dafny prelude into an F*
  predicate ending in `_fact`.
**)

/// We don't need the following axiom since we return a nat from cardinality:
/// 
/// axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

/// We represent the following Dafny axiom with `cardinality_zero_iff_empty_fact`:
/// 
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Card(m) }
///  Map#Card(m) == 0 <==> m == Map#Empty());

let cardinality_zero_iff_empty_fact =
  forall (a: eqtype) (b:Type u#b) (m: map a b).{:pattern cardinality m}
    cardinality m = 0 <==> m == emptymap

/// We represent the following Dafny axiom with `empty_or_domain_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Domain(m) }
///  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));

let empty_or_domain_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern domain m}
    m == emptymap \/ (exists k.{:pattern mem k m} mem k m)

/// We represent the following Dafny axiom with `empty_or_values_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Values(m) }
///  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));

let empty_or_values_occupied_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern values m}
    m == emptymap \/ (exists v. {:pattern values m v } (values m) v)

/// We represent the following Dafny axiom with `empty_or_items_occupied_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Map#Items(m) }
///  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

let empty_or_items_occupied_fact =
  forall (a: eqtype) (b:Type u#b) (m: map a b).{:pattern items m}
    m == emptymap \/ (exists item. {:pattern items m item } (items m) item)

/// We represent the following Dafny axiom with `map_cardinality_matches_domain_fact`:
///
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Domain(m)) }
///  Set#Card(Map#Domain(m)) == Map#Card(m));

let map_cardinality_matches_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b).{:pattern FSet.cardinality (domain m)}
    FSet.cardinality (domain m) = cardinality m
    
/// We don't use the following Dafny axioms, which would require
/// treating the values and items as finite sets, which we can't do
/// because we want to allow non-eqtypes as values.
///
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Values(m)) }
///  Set#Card(Map#Values(m)) <= Map#Card(m));
/// axiom (forall<U, V> m: Map U V ::
///  { Set#Card(Map#Items(m)) }
///  Set#Card(Map#Items(m)) == Map#Card(m));

/// We represent the following Dafny axiom with `values_contains_fact`:
///
/// axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
///  Map#Values(m)[v] ==
/// 	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
///          Map#Domain(m)[u] &&
///          v == Map#Elements(m)[u]));

let values_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (v: b).{:pattern (values m) v}
    (values m) v <==>
       (exists (u: a).{:pattern FSet.mem u (domain m) \/ ((elements m) u)}
          FSet.mem u (domain m) /\ (elements m) u == Some v)

/// We represent the following Dafny axiom with `items_contains_fact`:
///
/// axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
///  Map#Items(m)[item] <==>
///    Map#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
///    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

let items_contains_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (item: a & b).{:pattern (items m) item}
    (items m) item <==>
        FSet.mem (fst item) (domain m)
      /\ (elements m) (fst item) == Some (snd item)

/// We represent the following Dafny axiom with `empty_domain_empty_fact`:
///
/// axiom (forall<U, V> u: U ::
///        { Map#Domain(Map#Empty(): Map U V)[u] }
///        !Map#Domain(Map#Empty(): Map U V)[u]);

let empty_domain_empty_fact =
  forall (a: eqtype) (b: Type u#b) (u: a).{:pattern FSet.mem u (domain (emptymap #a #b))}
    not (FSet.mem u (domain (emptymap #a #b)))

/// We represent the following Dafny axiom with `glue_domain_fact`:
///
/// axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
///  { Map#Domain(Map#Glue(a, b, t)) }
///  Map#Domain(Map#Glue(a, b, t)) == a);

let glue_domain_fact =
  forall (a: eqtype) (b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys).{:pattern domain (glue keys f)}
    domain (glue keys f) == keys

/// We represent the following Dafny axiom with `glue_elements_fact`.
/// But we have to change it because our version of `Map#Elements`
/// returns a map to an optional value.
///
/// axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
///  { Map#Elements(Map#Glue(a, b, t)) }
///  Map#Elements(Map#Glue(a, b, t)) == b);

let glue_elements_fact =
  forall (a: eqtype) (b: Type u#b) (keys: FSet.set a) (f: setfun_t a b keys).{:pattern elements (glue keys f)}
      domain (glue keys f) == keys
    /\ elements (glue keys f) == f

/// We don't need the following Dafny axiom since the type of `glue` implies it:
///
/// axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
///  { Map#Glue(a, b, TMap(t0, t1)) }
///  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
///  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
///  ==>
///  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));

/// We represent the following Dafny axiom with `insert_elements_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
///  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
///  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
///               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
///  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
///               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));

let insert_elements_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (key': a) (value: b).
    {:pattern FSet.mem key' (domain (insert key value m)) \/ ((elements (insert key value m)) key')}
      (key' = key ==>   FSet.mem key' (domain (insert key value m))
                     /\ (elements (insert key value m)) key' == Some value)
    /\ (key' <> key ==>   FSet.mem key' (domain (insert key value m)) = FSet.mem key' (domain m)
                     /\ (elements (insert key value m)) key' == (elements m) key')

/// We represent the following Dafny axiom with `insert_member_cardinality_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
///  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));

let insert_member_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (value: b).{:pattern cardinality (insert key value m)}
    FSet.mem key (domain m) ==> cardinality (insert key value m) = cardinality m

/// We represent the following Dafny axiom with `insert_nonmember_cardinality_fact`:
///
/// axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
///  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

let insert_nonmember_cardinality_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (key: a) (value: b).{:pattern cardinality (insert key value m)}
    not (FSet.mem key (domain m)) ==> cardinality (insert key value m) = cardinality m + 1

/// We represent the following Dafny axiom with `merge_domain_is_union_fact`:
///
/// axiom (forall<U, V> m: Map U V, n: Map U V ::
///  { Map#Domain(Map#Merge(m, n)) }
///  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));

let merge_domain_is_union_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern domain (merge m1 m2)}
    domain (merge m1 m2) == FSet.union (domain m1) (domain m2)

/// We represent the following Dafny axiom with `merge_element_fact`:
///
/// axiom (forall<U, V> m: Map U V, n: Map U V, u: U ::
///  { Map#Elements(Map#Merge(m, n))[u] }
///  Map#Domain(Map#Merge(m, n))[u] ==>
///    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
///    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

let merge_element_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b) (key: a).{:pattern (elements (merge m1 m2)) key}
    FSet.mem key (domain (merge m1 m2)) ==>
        (not (FSet.mem key (domain m2)) ==> FSet.mem key (domain m1) /\ (elements (merge m1 m2)) key == (elements m1) key)
      /\ (FSet.mem key (domain m2) ==> (elements (merge m1 m2)) key == (elements m2) key)

/// We represent the following Dafny axiom with `subtract_domain_fact`:
///
/// axiom (forall<U, V> m: Map U V, s: Set U ::
///  { Map#Domain(Map#Subtract(m, s)) }
///  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));

let subtract_domain_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (s: FSet.set a).{:pattern domain (subtract m s)}
    domain (subtract m s) == FSet.difference (domain m) s

/// We represent the following Dafny axiom with `subtract_element_fact`:
///
/// axiom (forall<U, V> m: Map U V, s: Set U, u: U ::
///  { Map#Elements(Map#Subtract(m, s))[u] }
///  Map#Domain(Map#Subtract(m, s))[u] ==>
///    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

let subtract_element_fact =
  forall (a: eqtype) (b: Type u#b) (m: map a b) (s: FSet.set a) (key: a).{:pattern (elements (subtract m s)) key}
    FSet.mem key (domain (subtract m s)) ==> FSet.mem key (domain m) /\ (elements (subtract m s)) key == (elements m) key

/// We represent the following Dafny axiom with `map_equal_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V::
///  { Map#Equal(m, m') }
///    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
///                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));

let map_equal_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern equal m1 m2}
    equal m1 m2 <==>   (forall key. FSet.mem key (domain m1) = FSet.mem key (domain m2))
                   /\ (forall key. FSet.mem key (domain m1) ==> (elements m1) key == (elements m2) key)

/// We represent the following Dafny axiom with `map_extensionality_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V::
///  { Map#Equal(m, m') }
///    Map#Equal(m, m') ==> m == m');

let map_extensionality_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern equal m1 m2}
    equal m1 m2 ==> m1 == m2

/// We represent the following Dafny axiom with `disjoint_fact`:
///
/// axiom (forall<U, V> m: Map U V, m': Map U V ::
///  { Map#Disjoint(m, m') }
///    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));

let disjoint_fact =
  forall (a: eqtype) (b: Type u#b) (m1: map a b) (m2: map a b).{:pattern disjoint m1 m2}
    disjoint m1 m2 <==> (forall key.{:pattern FSet.mem key (domain m1) \/ FSet.mem key (domain m2)}
                          not (FSet.mem key (domain m1)) || not (FSet.mem key (domain m2)))

(**
  The predicate `all_finite_map_facts` collects all the Dafny finite-map axioms.
  One can bring all these facts into scope with `all_finite_map_facts_lemma ()`.
**)

let all_finite_map_facts =
    cardinality_zero_iff_empty_fact u#b
  /\ empty_or_domain_occupied_fact u#b
  /\ empty_or_values_occupied_fact u#b
  /\ empty_or_items_occupied_fact u#b
  /\ map_cardinality_matches_domain_fact u#b
  /\ values_contains_fact u#b
  /\ items_contains_fact u#b
  /\ empty_domain_empty_fact u#b
  /\ glue_domain_fact u#b
  /\ glue_elements_fact u#b
  /\ insert_elements_fact u#b
  /\ insert_member_cardinality_fact u#b
  /\ insert_nonmember_cardinality_fact u#b
  /\ merge_domain_is_union_fact u#b
  /\ merge_element_fact u#b
  /\ subtract_domain_fact u#b
  /\ subtract_element_fact u#b
  /\ map_equal_fact u#b
  /\ map_extensionality_fact u#b
  /\ disjoint_fact u#b
  
val all_finite_map_facts_lemma (_:unit)
  : Lemma (all_finite_map_facts u#b)
