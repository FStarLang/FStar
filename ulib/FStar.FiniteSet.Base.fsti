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

open FStar.FunctionalExtensionality
module FLT = FStar.List.Tot

val set (a: eqtype)
  : Type0

(**
  We translate each Dafny sequence function prefixed with `Set#`
  into an F* function.
**)

/// We represent the Dafny operator [] on sets with `mem`:

val mem (#a: eqtype) (x: a) (s: set a)
  : bool

/// We can convert a set to a list with `set_as_list`:

let rec list_nonrepeating (#a: eqtype) (xs: list a) : bool =
  match xs with
  | [] -> true
  | hd :: tl -> not (FLT.mem hd tl) && list_nonrepeating tl

val set_as_list (#a: eqtype) (s: set a)
  : GTot (xs: list a{list_nonrepeating xs /\ (forall x. FLT.mem x xs = mem x s)})

/// We represent the Dafny function `Set#Card` with `cardinality`:
///
/// function Set#Card<T>(Set T): int;

val cardinality (#a: eqtype) (s: set a)
  : GTot nat

/// We represent the Dafny function `Set#Empty` with `empty`:
///
/// function Set#Empty<T>(): Set T;

val emptyset (#a: eqtype)
  : set a

/// We represent the Dafny function `Set#UnionOne` with `insert`:
///
/// function Set#UnionOne<T>(Set T, T): Set T;

val insert (#a: eqtype) (x: a) (s: set a)
  : set a

/// We represent the Dafny function `Set#Singleton` with `singleton`:
///
/// function Set#Singleton<T>(T): Set T;

val singleton (#a: eqtype) (x: a)
  : set a

/// We represent the Dafny function `Set#Union` with `union`:
///
/// function Set#Union<T>(Set T, Set T): Set T;

val union (#a: eqtype) (s1: set a) (s2: set a)
  : (set a)

/// We represent the Dafny function `Set#Intersection` with `intersection`:
///
/// function Set#Intersection<T>(Set T, Set T): Set T;

val intersection (#a: eqtype) (s1: set a) (s2: set a)
  : set a

/// We represent the Dafny function `Set#Difference` with `difference`:
///
/// function Set#Difference<T>(Set T, Set T): Set T;

val difference (#a: eqtype) (s1: set a) (s2: set a)
  : set a

/// We represent the Dafny function `Set#Subset` with `subset`:
///
/// function Set#Subset<T>(Set T, Set T): bool;

val subset (#a: eqtype) (s1: set a) (s2: set a)
  : Type0

/// We represent the Dafny function `Set#Equal` with `equal`:
///
/// function Set#Equal<T>(Set T, Set T): bool;

val equal (#a: eqtype) (s1: set a) (s2: set a)
  : Type0

/// We represent the Dafny function `Set#Disjoint` with `disjoint`:
///
/// function Set#Disjoint<T>(Set T, Set T): bool;

val disjoint (#a: eqtype) (s1: set a) (s2: set a)
  : Type0

/// We represent the Dafny choice operator by `choose`:
///
/// var x: T :| x in s;

val choose (#a: eqtype) (s: set a{exists x. mem x s})
  : GTot (x: a{mem x s})

/// We add the utility functions `remove` and `notin`:

let remove (#a: eqtype) (x: a) (s: set a)
  : set a =
  difference s (singleton x)

let notin (#a: eqtype) (x: a) (s: set a)
  : bool =
  not (mem x s)

(**
  We translate each finite set axiom from the Dafny prelude into an F*
  predicate ending in `_fact`.
**)

/// We don't need the following axiom since we return a nat from cardinality:
/// 
/// axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));

/// We represent the following Dafny axiom with `empty_set_contains_no_elements_fact`:
///
/// axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);

let empty_set_contains_no_elements_fact =
  forall (a: eqtype) (o: a).{:pattern mem o (emptyset)} not (mem o (emptyset #a))

/// We represent the following Dafny axiom with `length_zero_fact`:
///
/// axiom (forall<T> s: Set T :: { Set#Card(s) }
///  (Set#Card(s) == 0 <==> s == Set#Empty()) &&
///  (Set#Card(s) != 0 ==> (exists x: T :: s[x])));

let length_zero_fact =
  forall (a: eqtype) (s: set a).{:pattern cardinality s}
      (cardinality s = 0 <==> s == emptyset)
    /\ (cardinality s <> 0 <==> (exists x. mem x s))
    
/// We represent the following Dafny axiom with `singleton_contains_argument_fact`:
///
/// axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);

let singleton_contains_argument_fact =
  forall (a: eqtype) (r: a).{:pattern singleton r} mem r (singleton r)
    
/// We represent the following Dafny axiom with `singleton_contains_fact`:
///
/// axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);

let singleton_contains_fact =
  forall (a: eqtype) (r: a) (o: a).{:pattern mem o (singleton r)} mem o (singleton r) <==> r == o
    
/// We represent the following Dafny axiom with `singleton_cardinality_fact`:
///
/// axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);

let singleton_cardinality_fact =
  forall (a: eqtype) (r: a).{:pattern cardinality (singleton r)} cardinality (singleton r) = 1
    
/// We represent the following Dafny axiom with `insert_fact`:
///
/// axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
///  Set#UnionOne(a,x)[o] <==> o == x || a[o]);

let insert_fact =
  forall (a: eqtype) (s: set a) (x: a) (o: a).{:pattern mem o (insert x s)}
    mem o (insert x s) <==> o == x \/ mem o s
    
/// We represent the following Dafny axiom with `insert_contains_argument_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
///  Set#UnionOne(a, x)[x]);

let insert_contains_argument_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern insert x s}
    mem x (insert x s)
    
/// We represent the following Dafny axiom with `insert_contains_fact`:
///
/// axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
///  a[y] ==> Set#UnionOne(a, x)[y]);

let insert_contains_fact =
  forall (a: eqtype) (s: set a) (x: a) (y: a).{:pattern insert x s; mem y s}
    mem y s ==> mem y (insert x s)
    
/// We represent the following Dafny axiom with `insert_member_cardinality_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
///  a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));

let insert_member_cardinality_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern cardinality (insert x s)}
    mem x s ==> cardinality (insert x s) = cardinality s
    
/// We represent the following Dafny axiom with `insert_nonmember_cardinality_fact`:
///
/// axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
///  !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);

let insert_nonmember_cardinality_fact =
  forall (a: eqtype) (s: set a) (x: a).{:pattern cardinality (insert x s)}
    not (mem x s) ==> cardinality (insert x s) = cardinality s + 1
    
/// We represent the following Dafny axiom with `union_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
///  Set#Union(a,b)[o] <==> a[o] || b[o]);

let union_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (union s1 s2)}
    mem o (union s1 s2) <==> mem o s1 \/ mem o s2
    
/// We represent the following Dafny axiom with `union_contains_element_from_first_argument_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
///  a[y] ==> Set#Union(a, b)[y]);

let union_contains_element_from_first_argument_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern union s1 s2; mem y s1}
    mem y s1 ==> mem y (union s1 s2)
    
/// We represent the following Dafny axiom with `union_contains_element_from_second_argument_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
///  b[y] ==> Set#Union(a, b)[y]);

let union_contains_element_from_second_argument_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern union s1 s2; mem y s2}
    mem y s2 ==> mem y (union s1 s2)

/// We represent the following Dafny axiom with `union_of_disjoint_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
///  Set#Disjoint(a, b) ==>
///    Set#Difference(Set#Union(a, b), a) == b &&
///    Set#Difference(Set#Union(a, b), b) == a);

let union_of_disjoint_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union s1 s2}
    disjoint s1 s2 ==> difference (union s1 s2) s1 == s2 /\ difference (union s1 s2) s2 == s1

/// We represent the following Dafny axiom with `intersection_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
///  Set#Intersection(a,b)[o] <==> a[o] && b[o]);

let intersection_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (intersection s1 s2)}
    mem o (intersection s1 s2) <==> mem o s1 /\ mem o s2

/// We represent the following Dafny axiom with `union_idempotent_right_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
///  Set#Union(Set#Union(a, b), b) == Set#Union(a, b));

let union_idempotent_right_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union (union s1 s2) s2}
    union (union s1 s2) s2 == union s1 s2

/// We represent the following Dafny axiom with `union_idempotent_left_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
///  Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));

let union_idempotent_left_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern union s1 (union s1 s2)}
    union s1 (union s1 s2) == union s1 s2

/// We represent the following Dafny axiom with `intersection_idempotent_right_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
///  Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));

let intersection_idempotent_right_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern intersection (intersection s1 s2) s2}
    intersection (intersection s1 s2) s2 == intersection s1 s2

/// We represent the following Dafny axiom with `intersection_idempotent_left_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
///  Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));

let intersection_idempotent_left_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern intersection s1 (intersection s1 s2)}
    intersection s1 (intersection s1 s2) == intersection s1 s2

/// We represent the following Dafny axiom with `intersection_cardinality_fact`:
///
/// axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }{ Set#Card(Set#Intersection(a, b)) }
///  Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b)) == Set#Card(a) + Set#Card(b));

let intersection_cardinality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern cardinality (intersection s1 s2)}
    cardinality (union s1 s2) + cardinality (intersection s1 s2) = cardinality s1 + cardinality s2

/// We represent the following Dafny axiom with `difference_contains_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
///  Set#Difference(a,b)[o] <==> a[o] && !b[o]);

let difference_contains_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (o: a).{:pattern mem o (difference s1 s2)}
    mem o (difference s1 s2) <==> mem o s1 /\ not (mem o s2)

/// We represent the following Dafny axiom with `difference_doesnt_include_fact`:
///
/// axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
///  b[y] ==> !Set#Difference(a, b)[y] );

let difference_doesnt_include_fact =
  forall (a: eqtype) (s1: set a) (s2: set a) (y: a).{:pattern difference s1 s2; mem y s2}
    mem y s2 ==> not (mem y (difference s1 s2))

/// We represent the following Dafny axiom with `difference_cardinality_fact`:
///
/// axiom (forall<T> a, b: Set T ::
///  { Set#Card(Set#Difference(a, b)) }
///  Set#Card(Set#Difference(a, b)) + Set#Card(Set#Difference(b, a))
///  + Set#Card(Set#Intersection(a, b))
///    == Set#Card(Set#Union(a, b)) &&
///  Set#Card(Set#Difference(a, b)) == Set#Card(a) - Set#Card(Set#Intersection(a, b)));

let difference_cardinality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern cardinality (difference s1 s2)}
      cardinality (difference s1 s2) + cardinality (difference s2 s1) + cardinality (intersection s1 s2) = cardinality (union s1 s2)
    /\ cardinality (difference s1 s2) = cardinality s1 - cardinality (intersection s1 s2)

/// We represent the following Dafny axiom with `subset_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
///  Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));

let subset_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern subset s1 s2}
    subset s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 ==> mem o s2)

/// We represent the following Dafny axiom with `equal_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
///  Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));

let equal_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern equal s1 s2}
    equal s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} mem o s1 <==> mem o s2)

/// We represent the following Dafny axiom with `equal_extensionality_fact`:
///
/// axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
///  Set#Equal(a,b) ==> a == b);

let equal_extensionality_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern equal s1 s2}
    equal s1 s2 ==> s1 == s2

/// We represent the following Dafny axiom with `disjoint_fact`:
///
/// axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
///  Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));

let disjoint_fact =
  forall (a: eqtype) (s1: set a) (s2: set a).{:pattern disjoint s1 s2}
    disjoint s1 s2 <==> (forall o.{:pattern mem o s1 \/ mem o s2} not (mem o s1) \/ not (mem o s2))

/// We add a few more facts for the utility function `remove` and for `set_as_list`:

let insert_remove_fact =
  forall (a: eqtype) (x: a) (s: set a).{:pattern insert x (remove x s)}
    mem x s = true ==> insert x (remove x s) == s

let remove_insert_fact =
  forall (a: eqtype) (x: a) (s: set a).{:pattern remove x (insert x s)}
    mem x s = false ==> remove x (insert x s) == s

let set_as_list_cardinality_fact =
  forall (a: eqtype) (s: set a).{:pattern FLT.length (set_as_list s)}
    FLT.length (set_as_list s) = cardinality s

(**
  The predicate `all_finite_set_facts` collects all the Dafny finite-set axioms.
  One can bring all these facts into scope with `all_finite_set_facts_lemma ()`.
**)

let all_finite_set_facts =
    empty_set_contains_no_elements_fact
  /\ length_zero_fact
  /\ singleton_contains_argument_fact
  /\ singleton_contains_fact
  /\ singleton_cardinality_fact
  /\ insert_fact
  /\ insert_contains_argument_fact
  /\ insert_contains_fact
  /\ insert_member_cardinality_fact
  /\ insert_nonmember_cardinality_fact
  /\ union_contains_fact
  /\ union_contains_element_from_first_argument_fact
  /\ union_contains_element_from_second_argument_fact
  /\ union_of_disjoint_fact
  /\ intersection_contains_fact
  /\ union_idempotent_right_fact
  /\ union_idempotent_left_fact
  /\ intersection_idempotent_right_fact
  /\ intersection_idempotent_left_fact
  /\ intersection_cardinality_fact
  /\ difference_contains_fact
  /\ difference_doesnt_include_fact
  /\ difference_cardinality_fact
  /\ subset_fact
  /\ equal_fact
  /\ equal_extensionality_fact
  /\ disjoint_fact
  /\ insert_remove_fact
  /\ remove_insert_fact
  /\ set_as_list_cardinality_fact

val all_finite_set_facts_lemma : unit -> Lemma (all_finite_set_facts)
