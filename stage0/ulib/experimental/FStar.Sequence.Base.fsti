(*
   Copyright 2008-2021 Jay Lorch, Rustan Leino, Alex Summers, Dan
   Rosen, Nikhil Swamy, Microsoft Research, and contributors to
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
sequences as they're modeled in Dafny.

@summary Type and functions for modeling sequences
*)
module FStar.Sequence.Base

new val seq ([@@@ strictly_positive] a: Type u#a) : Type u#a

(**
  We translate each Dafny sequence function prefixed with `Seq#`
  into an F* function.
**)

/// We represent the Dafny function `Seq#Length` with `length`:
///
/// function Seq#Length<T>(Seq T): int;

val length : #ty: Type -> seq ty -> nat

/// We represent the Dafny function `Seq#Empty` with `empty`:
/// 
/// function Seq#Empty<T>(): Seq T;
///
/// We also provide an alias `nil` for it.

val empty : #ty: Type -> seq ty

/// We represent the Dafny function `Seq#Singleton` with `singleton`:
///
/// function Seq#Singleton<T>(T): Seq T;

val singleton : #ty: Type -> ty -> seq ty

/// We represent the Dafny function `Seq#Index` with `index`:
///
/// function Seq#Index<T>(Seq T, int): T;
///
/// We also provide the infix symbol `$@` for it.

val index: #ty: Type -> s: seq ty -> i: nat{i < length s} -> ty
let ($@) = index

/// We represent the Dafny function `Seq#Build` with `build`:
/// 
/// function Seq#Build<T>(s: Seq T, val: T): Seq T;
///
/// We also provide the infix symbol `$::` for it.

val build: #ty: Type -> seq ty -> ty -> seq ty
let ($::) = build

/// We represent the Dafny function `Seq#Append` with `append`:
///
/// function Seq#Append<T>(Seq T, Seq T): Seq T;
///
/// We also provide the infix notation `$+` for it.

val append: #ty: Type -> seq ty -> seq ty -> seq ty
let ($+) = append

/// We represent the Dafny function `Seq#Update` with `update`:
///
/// function Seq#Update<T>(Seq T, int, T): Seq T;

val update: #ty: Type -> s: seq ty -> i: nat{i < length s} -> ty -> seq ty

/// We represent the Dafny function `Seq#Contains` with `contains`:
///
/// function Seq#Contains<T>(Seq T, T): bool;

val contains: #ty: Type -> seq ty -> ty -> Type0

/// We represent the Dafny function `Seq#Take` with `take`:
///
/// function Seq#Take<T>(s: Seq T, howMany: int): Seq T;

val take: #ty: Type -> s: seq ty -> howMany: nat{howMany <= length s} -> seq ty

/// We represent the Dafny function `Seq#Drop` with `drop`:
///
/// function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;

val drop: #ty: Type -> s: seq ty -> howMany: nat{howMany <= length s} -> seq ty

/// We represent the Dafny function `Seq#Equal` with `equal`.
///
/// function Seq#Equal<T>(Seq T, Seq T): bool;
///
/// We also provide the infix symbol `$==` for it.

val equal: #ty: Type -> seq ty -> seq ty -> Type0
let ($==) = equal

/// Instead of representing the Dafny function `Seq#SameUntil`, which
/// is only ever used in Dafny to represent prefix relations, we
/// instead use `is_prefix`.
///
/// function Seq#SameUntil<T>(Seq T, Seq T, int): bool;
///
/// We also provide the infix notation `$<=` for it.

val is_prefix: #ty: Type -> seq ty -> seq ty -> Type0
let ($<=) = is_prefix

/// We represent the Dafny function `Seq#Rank` with `rank`.
///
/// function Seq#Rank<T>(Seq T): int;

val rank: #ty: Type -> ty -> ty

(**
  We translate each sequence axiom from the Dafny prelude into an F*
  predicate ending in `_fact`.
**)

/// We don't need the following axiom since we return a nat from length:
/// 
/// axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

/// We represent the following Dafny axiom with `length_of_empty_is_zero_fact`:
///
/// axiom (forall<T> :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);

private let length_of_empty_is_zero_fact =
  forall (ty: Type u#a).{:pattern empty #ty} length (empty #ty) = 0

/// We represent the following Dafny axiom with `length_zero_implies_empty_fact`:
///
/// axiom (forall<T> s: Seq T :: { Seq#Length(s) }
///   (Seq#Length(s) == 0 ==> s == Seq#Empty())

private let length_zero_implies_empty_fact =
  forall (ty: Type u#a) (s: seq ty).{:pattern length s} length s = 0 ==> s == empty

/// We represent the following Dafny axiom with `singleton_length_one_fact`:
/// 
/// axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

private let singleton_length_one_fact =
  forall (ty: Type u#a) (v: ty).{:pattern length (singleton v)} length (singleton v) = 1

/// We represent the following Dafny axiom with `build_increments_length_fact`:
///
/// axiom (forall<T> s: Seq T, v: T ::
///   { Seq#Build(s,v) }
///   Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));

private let build_increments_length_fact =
  forall (ty: Type u#a) (s: seq ty) (v: ty).{:pattern build s v}
    length (build s v) = 1 + length s

/// We represent the following Dafny axiom with `index_into_build_fact`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
///   (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
///   (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

private let index_into_build_fact (_: squash (build_increments_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (v: ty) (i: nat{i < length (build s v)})
    .{:pattern index (build s v) i}
      (i = length s ==> index (build s v) i == v)
    /\ (i <> length s ==> index (build s v) i == index s i)

/// We represent the following Dafny axiom with `append_sums_lengths_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
///   Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

private let append_sums_lengths_fact =
  forall (ty: Type u#a) (s0: seq ty) (s1: seq ty).{:pattern length (append s0 s1)}
    length (append s0 s1) = length s0 + length s1

/// We represent the following Dafny axiom with `index_into_singleton_fact`:
///
/// axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);

private let index_into_singleton_fact (_: squash (singleton_length_one_fact u#a)) =
  forall (ty: Type u#a) (v: ty).{:pattern index (singleton v) 0}
     index (singleton v) 0 == v

/// We represent the following axiom with `index_after_append_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
///   (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
///   (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

private let index_after_append_fact (_: squash (append_sums_lengths_fact u#a)) =
  forall (ty: Type u#a) (s0: seq ty) (s1: seq ty) (n: nat{n < length (append s0 s1)})
    .{:pattern index (append s0 s1) n}
      (n < length s0 ==> index (append s0 s1) n == index s0 n)
    /\ (length s0 <= n ==> index (append s0 s1) n == index s1 (n - length s0))

/// We represent the following Dafny axiom with `update_maintains_length`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
///   0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));

private let update_maintains_length_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat{i < length s}) (v: ty).{:pattern length (update s i v)}
    length (update s i v) = length s

/// We represent the following Dafny axiom with `update_then_index_fact`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
///   0 <= n && n < Seq#Length(s) ==>
///     (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
///     (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

private let update_then_index_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat{i < length s}) (v: ty) (n: nat{n < length (update s i v)})
      .{:pattern index (update s i v) n}
      n < length s ==>
          (i = n ==> index (update s i v) n == v)
        /\ (i <> n ==> index (update s i v) n == index s n)

/// We represent the following Dafny axiom with `contains_iff_exists_index_fact`:
///
/// axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
///   Seq#Contains(s,x) <==>
///     (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));

private let contains_iff_exists_index_fact =
  forall (ty: Type u#a) (s: seq ty) (x: ty).{:pattern contains s x}
    contains s x <==> (exists (i: nat).{:pattern index s i} i < length s /\ index s i == x)

/// We represent the following Dafny axiom with `empty_doesnt_contain_fact`:
///
/// axiom (forall<T> x: T ::
///   { Seq#Contains(Seq#Empty(), x) }
///   !Seq#Contains(Seq#Empty(), x));

private let empty_doesnt_contain_anything_fact =
  forall (ty: Type u#a) (x: ty).{:pattern contains empty x} ~(contains empty x)

/// We represent the following Dafny axiom with `build_contains_equiv_fact`:
///
/// axiom (forall<T> s: Seq T, v: T, x: T ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
///   { Seq#Contains(Seq#Build(s, v), x) }
///     Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

private let build_contains_equiv_fact =
  forall (ty: Type u#a) (s: seq ty) (v: ty) (x: ty).{:pattern contains (build s v) x}
    contains (build s v) x <==> (v == x \/ contains s x)

/// We represent the following Dafny axiom with `take_contains_equiv_exists_fact`:
///
/// axiom (forall<T> s: Seq T, n: int, x: T ::
///   { Seq#Contains(Seq#Take(s, n), x) }
///   Seq#Contains(Seq#Take(s, n), x) <==>
///     (exists i: int :: { Seq#Index(s, i) }
///       0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

private let take_contains_equiv_exists_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat{n <= length s}) (x: ty).{:pattern contains (take s n) x}
    contains (take s n) x <==>
    (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)

/// We represent the following Dafny axiom with `drop_contains_equiv_exists_fact`:
///
/// axiom (forall<T> s: Seq T, n: int, x: T ::
///   { Seq#Contains(Seq#Drop(s, n), x) }
///   Seq#Contains(Seq#Drop(s, n), x) <==>
///     (exists i: int :: { Seq#Index(s, i) }
///       0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

private let drop_contains_equiv_exists_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat{n <= length s}) (x: ty).{:pattern contains (drop s n) x}
    contains (drop s n) x <==>
    (exists (i: nat).{:pattern index s i} n <= i && i < length s /\ index s i == x)

/// We represent the following Dafny axiom with `equal_def_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
///   Seq#Equal(s0,s1) <==>
///     Seq#Length(s0) == Seq#Length(s1) &&
///     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
///         0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

private let equal_def_fact =
  forall (ty: Type u#a) (s0: seq ty) (s1: seq ty).{:pattern equal s0 s1}
    equal s0 s1 <==>
    length s0 == length s1 /\
      (forall j.{:pattern index s0 j \/ index s1 j}
       0 <= j && j < length s0 ==> index s0 j == index s1 j)

/// We represent the following Dafny axiom with `extensionality_fact`:
///
/// axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
///   Seq#Equal(a,b) ==> a == b);

private let extensionality_fact =
  forall (ty: Type u#a) (a: seq ty) (b: seq ty).{:pattern equal a b}
    equal a b ==> a == b

/// We represent an analog of the following Dafny axiom with
/// `is_prefix_def_fact`.  Our analog uses `is_prefix` instead
/// of `Seq#SameUntil`.
///
/// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
///   Seq#SameUntil(s0,s1,n) <==>
///     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
///         0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

private let is_prefix_def_fact =
  forall (ty: Type u#a) (s0: seq ty) (s1: seq ty).{:pattern is_prefix s0 s1}
    is_prefix s0 s1 <==>
      length s0 <= length s1
    /\ (forall (j: nat).{:pattern index s0 j \/ index s1 j}
         j < length s0 ==> index s0 j == index s1 j)

/// We represent the following Dafny axiom with `take_length_fact`:
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
///   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);

private let take_length_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat).{:pattern length (take s n)}
    n <= length s ==> length (take s n) = n

/// We represent the following Dafny axiom with `index_into_take_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, j: int ::
///   {:weight 25}
///   { Seq#Index(Seq#Take(s,n), j) }
///   { Seq#Index(s, j), Seq#Take(s,n) }
///   0 <= j && j < n && j < Seq#Length(s) ==>
///     Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

private let index_into_take_fact (_ : squash (take_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (n: nat) (j: nat).
    {:pattern index (take s n) j \/ index s j ; take s n}
    j < n && n <= length s ==> index (take s n) j == index s j

/// We represent the following Dafny axiom with `drop_length_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
///   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);

private let drop_length_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat).
    {:pattern length (drop s n)}
    n <= length s ==> length (drop s n) = length s - n

/// We represent the following Dafny axiom with `index_into_drop_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, j: int ::
///   {:weight 25}
///   { Seq#Index(Seq#Drop(s,n), j) }
///   0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
///     Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

private let index_into_drop_fact (_ : squash (drop_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (n: nat) (j: nat).
    {:pattern index (drop s n) j}
    j < length s - n ==> index (drop s n) j == index s (j + n)

/// We represent the following Dafny axiom with `drop_index_offset_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, k: int ::
///   {:weight 25}
///   { Seq#Index(s, k), Seq#Drop(s,n) }
///   0 <= n && n <= k && k < Seq#Length(s) ==>
///     Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

private let drop_index_offset_fact (_ : squash (drop_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (n: nat) (k: nat).
    {:pattern index s k; drop s n}
    n <= k && k < length s ==> index (drop s n) (k - n) == index s k

/// We represent the following Dafny axiom with `append_then_take_or_drop_fact`.
///
/// axiom (forall<T> s, t: Seq T, n: int ::
///   { Seq#Take(Seq#Append(s, t), n) }
///   { Seq#Drop(Seq#Append(s, t), n) }
///   n == Seq#Length(s)
///   ==>
///   Seq#Take(Seq#Append(s, t), n) == s &&
///   Seq#Drop(Seq#Append(s, t), n) == t);

private let append_then_take_or_drop_fact (_ : squash (append_sums_lengths_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (t: seq ty) (n: nat).
    {:pattern take (append s t) n \/ drop (append s t) n}
    n = length s ==> take (append s t) n == s /\ drop (append s t) n == t

/// We represent the following Dafny axiom with `take_commutes_with_in_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Take(Seq#Update(s, i, v), n) }
///         0 <= i && i < n && n <= Seq#Length(s) ==>
///         Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );

private let take_commutes_with_in_range_update_fact
  (_ : squash (update_maintains_length_fact u#a /\ take_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern take (update s i v) n}
    i < n && n <= length s ==>
    take (update s i v) n == update (take s n) i v

/// We represent the following Dafny axiom with `take_ignores_out_of_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Take(Seq#Update(s, i, v), n) }
///         n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

private let take_ignores_out_of_range_update_fact (_ : squash (update_maintains_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern take (update s i v) n}
    n <= i && i < length s ==>
    take (update s i v) n == take s n

/// We represent the following Dafny axiom with `drop_commutes_with_in_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Drop(Seq#Update(s, i, v), n) }
///         0 <= n && n <= i && i < Seq#Length(s) ==>
///         Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );

private let drop_commutes_with_in_range_update_fact
  (_ : squash (update_maintains_length_fact u#a /\ drop_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern drop (update s i v) n}
    n <= i && i < length s ==>
    drop (update s i v) n == update (drop s n) (i - n) v

/// We represent the following Dafny axiom with `drop_ignores_out_of_range_update_fact`.
/// Jay noticed that it was unnecessarily weak, possibly due to a typo, so he reported this as
/// Dafny issue #1423 (https://github.com/dafny-lang/dafny/issues/1423) and updated it here.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Drop(Seq#Update(s, i, v), n) }
///         0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

private let drop_ignores_out_of_range_update_fact (_ : squash (update_maintains_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern drop (update s i v) n}
    i < n && n <= length s ==>
    drop (update s i v) n == drop s n

/// We represent the following Dafny axiom with `drop_commutes_with_build_fact`.
///
/// axiom (forall<T> s: Seq T, v: T, n: int ::
///         { Seq#Drop(Seq#Build(s, v), n) }
///         0 <= n && n <= Seq#Length(s) ==>
///         Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

private let drop_commutes_with_build_fact (_ : squash (build_increments_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (v: ty) (n: nat).{:pattern drop (build s v) n}
    n <= length s ==> drop (build s v) n == build (drop s n) v

/// We include the definition of `rank` among our facts.

private let rank_def_fact =
  forall (ty: Type u#a) (v: ty).{:pattern rank v} rank v == v

/// We represent the following Dafny axiom with `element_ranks_less_fact`.
///
/// axiom (forall s: Seq Box, i: int ::
///         { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
///         0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );

private let element_ranks_less_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat).{:pattern rank (index s i)}
    i < length s ==> rank (index s i) << rank s

/// We represent the following Dafny axiom with `drop_ranks_less_fact`.
///
/// axiom (forall<T> s: Seq T, i: int ::
///         { Seq#Rank(Seq#Drop(s, i)) }
///         0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );

private let drop_ranks_less_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat).{:pattern rank (drop s i)}
    0 < i && i <= length s ==> rank (drop s i) << rank s

/// We represent the following Dafny axiom with
/// `take_ranks_less_fact`.  However, since it isn't true in F* (which
/// has strong requirements for <<), we instead substitute length,
/// requiring decreases clauses to use length in this case.
///
/// axiom (forall<T> s: Seq T, i: int ::
///         { Seq#Rank(Seq#Take(s, i)) }
///         0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );

private let take_ranks_less_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat).{:pattern length (take s i)}
    i < length s ==> length (take s i) << length s

/// We represent the following Dafny axiom with
/// `append_take_drop_ranks_less_fact`.  However, since it isn't true
/// in F* (which has strong requirements for <<), we instead
/// substitute length, requiring decreases clauses to use
/// length in this case.
///
/// axiom (forall<T> s: Seq T, i: int, j: int ::
///         { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
///         0 <= i && i < j && j <= Seq#Length(s) ==>
///         Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

private let append_take_drop_ranks_less_fact =
  forall (ty: Type u#a) (s: seq ty) (i: nat) (j: nat).{:pattern length (append (take s i) (drop s j))}
    i < j && j <= length s ==> length (append (take s i) (drop s j)) << length s

/// We represent the following Dafny axiom with `drop_zero_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) }
///         n == 0 ==> Seq#Drop(s, n) == s);

private let drop_zero_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat).{:pattern drop s n}
    n = 0 ==> drop s n == s

/// We represent the following Dafny axiom with `take_zero_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) }
///         n == 0 ==> Seq#Take(s, n) == Seq#Empty());

private let take_zero_fact =
  forall (ty: Type u#a) (s: seq ty) (n: nat).{:pattern take s n}
    n = 0 ==> take s n == empty

/// We represent the following Dafny axiom with `drop_then_drop_fact`.
///
/// axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
///         0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
///         Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));

private let drop_then_drop_fact (_: squash (drop_length_fact u#a)) =
  forall (ty: Type u#a) (s: seq ty) (m: nat) (n: nat).{:pattern drop (drop s m) n}
    m + n <= length s ==> drop (drop s m) n == drop s (m + n)

(**
  The predicate `all_dafny_seq_facts` collects all the Dafny sequence axioms.
  One can bring all these facts into scope with `all_dafny_seq_facts_lemma ()`.
**)

let all_seq_facts =
    length_of_empty_is_zero_fact u#a
  /\ length_zero_implies_empty_fact u#a
  /\ singleton_length_one_fact u#a
  /\ build_increments_length_fact u#a
  /\ index_into_build_fact u#a ()
  /\ append_sums_lengths_fact u#a
  /\ index_into_singleton_fact u#a ()
  /\ index_after_append_fact u#a ()
  /\ update_maintains_length_fact u#a
  /\ update_then_index_fact u#a
  /\ contains_iff_exists_index_fact u#a
  /\ empty_doesnt_contain_anything_fact u#a
  /\ build_contains_equiv_fact u#a
  /\ take_contains_equiv_exists_fact u#a
  /\ drop_contains_equiv_exists_fact u#a
  /\ equal_def_fact u#a
  /\ extensionality_fact u#a
  /\ is_prefix_def_fact u#a
  /\ take_length_fact u#a
  /\ index_into_take_fact u#a ()
  /\ drop_length_fact u#a
  /\ index_into_drop_fact u#a ()
  /\ drop_index_offset_fact u#a ()
  /\ append_then_take_or_drop_fact u#a ()
  /\ take_commutes_with_in_range_update_fact u#a ()
  /\ take_ignores_out_of_range_update_fact u#a ()
  /\ drop_commutes_with_in_range_update_fact u#a ()
  /\ drop_ignores_out_of_range_update_fact u#a ()
  /\ drop_commutes_with_build_fact u#a ()
  /\ rank_def_fact u#a
  /\ element_ranks_less_fact u#a
  /\ drop_ranks_less_fact u#a
  /\ take_ranks_less_fact u#a
  /\ append_take_drop_ranks_less_fact u#a
  /\ drop_zero_fact u#a
  /\ take_zero_fact u#a
  /\ drop_then_drop_fact u#a ()

val all_seq_facts_lemma : unit -> Lemma (all_seq_facts u#a)
