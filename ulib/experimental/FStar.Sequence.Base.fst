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
This module declares a type and functions used for modeling sequences
as they're modeled in Dafny. It also states and proves some properties
about sequences, and provides a lemma `all_seq_facts_lemma` one
can call to bring them into context.  The properties are modeled after
those in the Dafny sequence axioms, with patterns for quantifiers
chosen as in those axioms.

@summary Type, functions, and properties of sequences
*)
module FStar.Sequence.Base

module FLT = FStar.List.Tot

/// Internally, we represent a sequence as a list.

type seq (ty: Type) = list ty

/// We represent the Dafny function `Seq#Length` with `length`:
///
/// function Seq#Length<T>(Seq T): int;

let length = FLT.length

/// We represent the Dafny function `Seq#Empty` with `empty`:
/// 
/// function Seq#Empty<T>(): Seq T;

let empty (#ty: Type) : seq ty = []

/// We represent the Dafny function `Seq#Singleton` with `singleton`:
///
/// function Seq#Singleton<T>(T): Seq T;

let singleton (#ty: Type) (v: ty) : seq ty =
  [v]

/// We represent the Dafny function `Seq#Index` with `index`:
///
/// function Seq#Index<T>(Seq T, int): T;

let index (#ty: Type) (s: seq ty) (i: nat{i < length s}) : ty =
  FLT.index s i

/// We represent the Dafny function `Seq#Build` with `build`:
/// 
/// function Seq#Build<T>(s: Seq T, val: T): Seq T;

let build (#ty: Type) (s: seq ty) (v: ty) : seq ty =
  FLT.append s [v]

/// We represent the Dafny function `Seq#Append` with `append`:
///
/// function Seq#Append<T>(Seq T, Seq T): Seq T;

let append = FLT.append

/// We represent the Dafny function `Seq#Update` with `update`:
///
/// function Seq#Update<T>(Seq T, int, T): Seq T;

let update (#ty: Type) (s: seq ty) (i: nat{i < length s}) (v: ty) : seq ty =
  let s1, _, s2 = FLT.split3 s i in
  append s1 (append [v] s2)

/// We represent the Dafny function `Seq#Contains` with `contains`:
///
/// function Seq#Contains<T>(Seq T, T): bool;

let contains (#ty: Type) (s: seq ty) (v: ty) : Type0 =
  FLT.memP v s

/// We represent the Dafny function `Seq#Take` with `take`:
///
/// function Seq#Take<T>(s: Seq T, howMany: int): Seq T;

let take (#ty: Type) (s: seq ty) (howMany: nat{howMany <= length s}) : seq ty =
  let result, _ = FLT.splitAt howMany s in
  result

/// We represent the Dafny function `Seq#Drop` with `drop`:
///
/// function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;

let drop (#ty: Type) (s: seq ty) (howMany: nat{howMany <= length s}) : seq ty =
  let _, result = FLT.splitAt howMany s in
  result

/// We represent the Dafny function `Seq#Equal` with `equal`.
///
/// function Seq#Equal<T>(Seq T, Seq T): bool;

let equal (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
  length s0 == length s1 /\
    (forall j.{:pattern index s0 j \/ index s1 j}
      0 <= j && j < length s0 ==> index s0 j == index s1 j)

/// Instead of representing the Dafny function `Seq#SameUntil`, which
/// is only ever used in Dafny to represent prefix relations, we
/// instead use `is_prefix`.
///
/// function Seq#SameUntil<T>(Seq T, Seq T, int): bool;

let is_prefix (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
    length s0 <= length s1
  /\ (forall (j: nat).{:pattern index s0 j \/ index s1 j}
     j < length s0 ==> index s0 j == index s1 j)

/// We represent the Dafny function `Seq#Rank` with `rank`.
///
/// function Seq#Rank<T>(Seq T): int;

let rank (#ty: Type) (v: ty) = v

/// We now prove each of the facts that comprise `all_seq_facts`.
/// For fact `xxx_fact`, we prove it with `xxx_lemma`.  Sometimes, that
/// requires a helper lemma, which we call `xxx_helper`.  In some cases,
/// we need multiple helpers, so we suffix their names with integers.

private let length_of_empty_is_zero_lemma () : Lemma (length_of_empty_is_zero_fact) =
  ()

private let length_zero_implies_empty_lemma () : Lemma (length_zero_implies_empty_fact) =
  ()

private let singleton_length_one_lemma () : Lemma (singleton_length_one_fact) =
  ()

private let build_increments_length_lemma () : Lemma (build_increments_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (v: ty). length (build s v) = 1 + length s
  with (
    FLT.append_length s [v]
  )

private let rec index_into_build_helper (#ty: Type) (s: list ty) (v: ty) (i: nat{i < length (append s [v])})
  : Lemma (requires i <= length s)
          (ensures  index (append s [v]) i == (if i = length s then v else index s i)) =
  FLT.append_length s [v];
  match s with
  | [] -> ()
  | hd :: tl ->
      if i = 0 then () else index_into_build_helper tl v (i - 1)

private let index_into_build_lemma ()
  : Lemma (requires build_increments_length_fact u#a)
          (ensures  index_into_build_fact u#a ()) =
  introduce forall (ty: Type) (s: seq ty) (v: ty) (i: nat{i < length (build s v)}).
                (i = length s ==> index (build s v) i == v)
              /\ (i <> length s ==> index (build s v) i == index s i)
  with (
    index_into_build_helper u#a s v i
  )

private let append_sums_lengths_lemma () : Lemma (append_sums_lengths_fact) =
  introduce forall (ty: Type) (s0: seq ty) (s1: seq ty). length (append s0 s1) = length s0 + length s1
  with (
    FLT.append_length s0 s1
  )

private let index_into_singleton_lemma (_: squash (singleton_length_one_fact u#a)) : Lemma (index_into_singleton_fact u#a ()) =
  ()

private let rec index_after_append_helper (ty: Type) (s0: list ty) (s1: list ty) (n: nat)
  : Lemma (requires n < length (append s0 s1) && length (append s0 s1) = length s0 + length s1)
          (ensures  index (append s0 s1) n == (if n < length s0 then index s0 n else index s1 (n - length s0))) =
  match s0 with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else index_after_append_helper ty tl s1 (n - 1)

private let index_after_append_lemma (_: squash (append_sums_lengths_fact u#a)) : Lemma (index_after_append_fact u#a ()) =
  introduce
    forall (ty: Type) (s0: seq ty) (s1: seq ty) (n: nat{n < length (append s0 s1)}).
        (n < length s0 ==> index (append s0 s1) n == index s0 n)
      /\ (length s0 <= n ==> index (append s0 s1) n == index s1 (n - length s0))
  with (
    index_after_append_helper ty s0 s1 n
  )

private let rec lemma_splitAt_fst_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures  (length (fst (FLT.splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n - 1) l'

private let update_maintains_length_helper (#ty: Type) (s: list ty) (i: nat{i < length s}) (v: ty)
  : Lemma (length (update s i v) = length s) =
  let s1, _, s2 = FLT.split3 s i in
    lemma_splitAt_fst_length i s;
    FLT.lemma_splitAt_snd_length i s;
    FLT.append_length [v] s2;
    FLT.append_length s1 (append [v] s2)

private let update_maintains_length_lemma () : Lemma (update_maintains_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat{i < length s}) (v: ty).
    length (update s i v) = length s
  with (
    update_maintains_length_helper s i v
  )

#restart-solver
#push-options "--z3rlimit_factor 4"
private let rec update_then_index_helper
  (#ty: Type)
  (s: list ty)
  (i: nat{i < length s})
  (v: ty)
  (n: nat{n < length (update s i v)})
  : Lemma (requires n < length s)
          (ensures  index (update s i v) n == (if i = n then v else index s n)) =
  match s with
  | hd :: tl ->
      if i = 0 || n = 0 then ()
      else update_then_index_helper tl (i - 1) v (n - 1)
#pop-options

private let update_then_index_lemma () : Lemma (update_then_index_fact) =
  update_maintains_length_lemma ();
  introduce
    forall (ty: Type) (s: seq ty) (i: nat{i < length s}) (v: ty) (n: nat{n < length (update s i v)}).
      n < length s ==>
          (i = n ==> index (update s i v) n == v)
        /\ (i <> n ==> index (update s i v) n == index s n)
  with
    introduce _ ==> _
    with given_antecedent. (
      update_then_index_helper s i v n
    )

private let contains_iff_exists_index_lemma () : Lemma (contains_iff_exists_index_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (x: ty).
      contains s x <==> (exists (i: nat).{:pattern index s i} i < length s /\ index s i == x)
  with (
    introduce contains s x ==> (exists (i: nat).{:pattern index s i} i < length s /\ index s i == x)
    with given_antecedent. (
      introduce exists (i: nat). i < length s /\ index s i == x
      with (FLT.index_of s x) and ()
    );
    introduce (exists (i: nat).{:pattern index s i} i < length s /\ index s i == x) ==> contains s x
    with given_antecedent. (
      eliminate exists (i: nat). i < length s /\ index s i == x
      returns _
      with _. FLT.lemma_index_memP s i
    )
  )

private let empty_doesnt_contain_anything_lemma () : Lemma (empty_doesnt_contain_anything_fact) =
  ()

private let rec build_contains_equiv_helper (ty: Type) (s: list ty) (v: ty) (x: ty)
  : Lemma (FLT.memP x (append s [v]) <==> (v == x \/ FLT.memP x s)) =
  match s with
  | [] -> ()
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns FLT.memP x (append s [v]) <==> (v == x \/ FLT.memP x s)
     with _. ()
     and _. build_contains_equiv_helper ty tl v x

private let build_contains_equiv_lemma () : Lemma (build_contains_equiv_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (v: ty) (x: ty).
      contains (build s v) x <==> (v == x \/ contains s x)
  with (
    build_contains_equiv_helper ty s v x
  )

private let rec take_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires FLT.memP x (take s n))
          (ensures (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)) =
  match s with
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x
     with case_x_eq_hd.
       assert(index s 0 == x)
     and case_x_ne_hd. (
      take_contains_equiv_exists_helper1 ty tl (n - 1) x;
      eliminate exists (i_tl: nat). i_tl < n - 1 /\ i_tl < length tl /\ index tl i_tl == x
      returns exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x
      with _.
        introduce exists (i: nat). i < n /\ i < length s /\ index s i == x
        with (i_tl + 1)
        and ())

private let rec take_contains_equiv_exists_helper2 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty) (i: nat)
  : Lemma (requires (i < n /\ i < length s /\ index s i == x))
          (ensures  FLT.memP x (take s n)) =
  match s with
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns FLT.memP x (take s n)
     with case_x_eq_hd. ()
     and case_x_ne_hd. take_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1)

private let take_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (FLT.memP x (take s n) <==>
           (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)) =
  introduce FLT.memP x (take s n) ==>
              (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)
  with given_antecedent. (take_contains_equiv_exists_helper1 ty s n x);
  introduce (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x) ==>
              FLT.memP x (take s n)
  with given_antecedent. (
    eliminate exists (i: nat). i < n /\ i < length s /\ index s i == x
    returns _
    with _. take_contains_equiv_exists_helper2 ty s n x i
  )

private let take_contains_equiv_exists_lemma () : Lemma (take_contains_equiv_exists_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat{n <= length s}) (x: ty).
              contains (take s n) x <==>
              (exists (i: nat). i < n /\ i < length s /\ index s i == x)
  with (
    take_contains_equiv_exists_helper3 ty s n x
  )

#push-options "--z3rlimit_factor 10 --fuel 1 --ifuel 1"
private let rec drop_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires FLT.memP x (drop s n))
          (ensures (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)) =
  match s with
  | hd :: tl ->
     eliminate n == 0 \/ n <> 0
     returns  exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x
     with case_n_eq_0. (
       eliminate x == hd \/ ~(x == hd)
       returns _
       with _. assert(index s 0 == x)
       and _. (
         drop_contains_equiv_exists_helper1 ty tl n x;
         eliminate exists (i_tl: nat). (n <= i_tl /\ i_tl < length tl /\ index tl i_tl == x)
         returns _
         with _. introduce exists i. n <= i /\ i < length s /\ index s i == x with (i_tl + 1) and ()
       ))
     and case_n_ne_0. (
       drop_contains_equiv_exists_helper1 ty tl (n - 1) x;
       eliminate exists (i_tl: nat). n - 1 <= i_tl /\ i_tl < length tl /\ index tl i_tl == x
       returns _
       with _. introduce exists i. n <= i /\ i < length s /\ index s i == x with (i_tl + 1) and ())
#pop-options

private let rec drop_contains_equiv_exists_helper2 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty) (i: nat)
  : Lemma (requires (n <= i /\ i < length s /\ index s i == x))
          (ensures  FLT.memP x (drop s n)) =
  match s with
  | hd :: tl ->
     eliminate n == 0 \/ n <> 0
     returns FLT.memP x (drop s n)
     with _. FLT.lemma_index_memP s i
     and _. (
       drop_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1);
       eliminate exists (i_tl: nat). n - 1 <= i_tl /\ i_tl < length tl /\ index tl i_tl == x
       returns _
       with _.
         introduce exists i. n <= i /\ i < length s /\ index s i == x with (i_tl + 1) and ())

private let drop_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (FLT.memP x (drop s n) <==>
           (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)) =
  introduce FLT.memP x (drop s n) ==>
              (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)
  with given_antecedent. (
    drop_contains_equiv_exists_helper1 ty s n x);
    introduce (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x) ==>
                FLT.memP x (drop s n)
    with given_antecedent. (
      eliminate exists (i: nat). n <= i /\ i < length s /\ index s i == x
      returns _
      with _. drop_contains_equiv_exists_helper2 ty s n x i
    )

private let drop_contains_equiv_exists_lemma () : Lemma (drop_contains_equiv_exists_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat{n <= length s}) (x: ty).
      contains (drop s n) x <==>
      (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)
  with (
    drop_contains_equiv_exists_helper3 ty s n x;
    assert (FLT.memP x (drop s n) <==>
            (exists (i: nat). n <= i /\ i < length s /\ index s i == x))
  )

private let equal_def_lemma () : Lemma (equal_def_fact) =
  ()

private let extensionality_lemma () : Lemma (extensionality_fact) =
  introduce forall (ty: Type) (a: seq ty) (b: seq ty). equal a b ==> a == b
  with
    introduce _ ==> _
    with given_antecedent. (
      introduce forall (i: nat) . i < length a ==> index a i == index b i
      with
        introduce _ ==> _
        with given_antecedent. (
          assert (index a i == index b i) // needed to trigger
        );
      FStar.List.Tot.Properties.index_extensionality a b
    )

private let is_prefix_def_lemma () : Lemma (is_prefix_def_fact) =
  ()

private let take_length_lemma () : Lemma (take_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
    n <= length s ==> length (take s n) = n
  with
    introduce _ ==> _
    with given_antecedent. (
      lemma_splitAt_fst_length n s
    )

private let rec index_into_take_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < n && n <= length s /\ length (take s n) = n)
          (ensures  index (take s n) j == index s j) =
  match s with
  | hd :: tl -> if j = 0 || n = 0 then () else index_into_take_helper tl (n - 1) (j - 1)

private let index_into_take_lemma ()
  : Lemma (requires take_length_fact u#a) (ensures index_into_take_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
      j < n && n <= length s ==> index (take s n) j == index s j
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (take s n) == n); // triggers take_length_fact
      index_into_take_helper s n j
    )

private let drop_length_lemma () : Lemma (drop_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
              n <= length s ==> length (drop s n) = length s - n
  with
    introduce _ ==> _
    with given_antecedent. (
      FLT.lemma_splitAt_snd_length n s
    )

private let rec index_into_drop_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < length s - n /\ length (drop s n) = length s - n)
          (ensures  index (drop s n) j == index s (j + n)) =
  match s with
  | hd :: tl -> if n = 0 then () else index_into_drop_helper tl (n - 1) j

private let index_into_drop_lemma ()
  : Lemma (requires drop_length_fact u#a) (ensures index_into_drop_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
      j < length s - n ==> index (drop s n) j == index s (j + n)
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (drop s n) = length s - n); // triggers drop_length_fact
      index_into_drop_helper s n j
    )

private let drop_index_offset_lemma ()
  : Lemma (requires drop_length_fact u#a) (ensures drop_index_offset_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (k: nat).
      n <= k && k < length s ==> index (drop s n) (k - n) == index s k
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (drop s n) = length s - n); // triggers drop_length_fact
      index_into_drop_helper s n (k - n)
    )

private let rec append_then_take_or_drop_helper (#ty: Type) (s: list ty) (t: list ty) (n: nat)
  : Lemma (requires n = length s /\ length (append s t) = length s + length t)
          (ensures  take (append s t) n == s /\ drop (append s t) n == t) =
  match s with
  | [] -> ()
  | hd :: tl -> append_then_take_or_drop_helper tl t (n - 1)

private let append_then_take_or_drop_lemma ()
  : Lemma (requires append_sums_lengths_fact u#a) (ensures append_then_take_or_drop_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (t: seq ty) (n: nat).
      n = length s ==> take (append s t) n == s /\ drop (append s t) n == t
  with
    introduce _ ==> _
    with given_antecedent. (
      append_then_take_or_drop_helper s t n
    )

#push-options "--z3rlimit 20"
private let rec take_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (update s i v) = length s
                    /\ length (take s n) = n)
          (ensures  take (update s i v) n == update (take s n) i v) =
  match s with
  | hd :: tl -> if i = 0 then () else (update_maintains_length_lemma() ; take_commutes_with_in_range_update_helper tl (i - 1) v (n - 1))
#pop-options

private let take_commutes_with_in_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact u#a /\ take_length_fact u#a)
          (ensures take_commutes_with_in_range_update_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      i < n && n <= length s ==>
      take (update s i v) n == update (take s n) i v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (update s i v) = length s); // triggers update_maintains_length_fact
      assert (length (take s n) = n);            // triggers take_length_fact
      take_commutes_with_in_range_update_helper s i v n
    )

private let rec take_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (update s i v) = length s)
          (ensures  take (update s i v) n == take s n) =
  match s with
  | hd :: tl -> if n = 0 then () else take_ignores_out_of_range_update_helper tl (i - 1) v (n - 1)

private let take_ignores_out_of_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact u#a)
          (ensures take_ignores_out_of_range_update_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      n <= i && i < length s ==>
      take (update s i v) n == take s n
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (update s i v) = length s); // triggers update_maintains_length_fact
      take_ignores_out_of_range_update_helper s i v n
    )

#push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 4"
private let rec drop_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (update s i v) = length s
                    /\ length (drop s n) = length s - n)
          (ensures  drop (update s i v) n ==
                      update (drop s n) (i - n) v) =
  match s with
  | hd :: tl ->
    if n = 0
    then ()
    else (
      update_maintains_length_lemma ();
      drop_length_lemma ();
      drop_commutes_with_in_range_update_helper tl (i - 1) v (n - 1)
    )
#pop-options

private let drop_commutes_with_in_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact u#a /\ drop_length_fact u#a)
          (ensures drop_commutes_with_in_range_update_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      n <= i && i < length s ==>
      drop (update s i v) n == update (drop s n) (i - n) v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (update s i v) = length s); // triggers update_maintains_length_fact
      assert (length (drop s n) = length s - n); // triggers drop_length_fact
      drop_commutes_with_in_range_update_helper s i v n
    )

private let rec drop_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (update s i v) = length s)
          (ensures  drop (update s i v) n == drop s n) =
  match s with
  | hd :: tl -> if i = 0 then () else drop_ignores_out_of_range_update_helper tl (i - 1) v (n - 1)

private let drop_ignores_out_of_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact u#a)
          (ensures drop_ignores_out_of_range_update_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      i < n && n <= length s ==>
      drop (update s i v) n == drop s n
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (update s i v) = length s); // triggers update_maintains_length_fact
      drop_ignores_out_of_range_update_helper s i v n
    )

private let rec drop_commutes_with_build_helper (#ty: Type) (s: list ty) (v: ty) (n: nat)
  : Lemma (requires n <= length s /\ length (append s [v]) = 1 + length s)
          (ensures  drop (append s [v]) n == append (drop s n) [v]) =
  match s with
  | [] -> 
    assert (append s [v] == [v]);
    assert (n == 0);
    ()
  | hd :: tl -> if n = 0 then () else drop_commutes_with_build_helper tl v (n - 1)

private let drop_commutes_with_build_lemma ()
  : Lemma (requires build_increments_length_fact u#a)
          (ensures  drop_commutes_with_build_fact u#a ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (v: ty) (n: nat).
      n <= length s ==> drop (build s v) n == build (drop s n) v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (build s v) = 1 + length s); // triggers build_increments_length_fact
      drop_commutes_with_build_helper s v n
    )

private let rank_def_lemma () : Lemma (rank_def_fact) =
  ()

private let element_ranks_less_lemma () : Lemma (element_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat). i < length s ==> rank (index s i) << rank s
  with
    introduce _ ==> _
    with given_antecedent. (
      contains_iff_exists_index_lemma ();
      assert (contains s (index s i));
      FLT.memP_precedes (index s i) s
    )

private let rec drop_ranks_less_helper (ty: Type) (s: list ty) (i: nat)
  : Lemma (requires 0 < i && i <= length s)
          (ensures  drop s i << s) =
  match s with
  | [] -> ()
  | hd :: tl -> if i = 1 then () else drop_ranks_less_helper ty tl (i - 1)

private let drop_ranks_less_lemma () : Lemma (drop_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat).
              0 < i && i <= length s ==> rank (drop s i) << rank s
  with
    introduce _ ==> _
    with given_antecedent. (
      drop_ranks_less_helper ty s i
    )

private let take_ranks_less_lemma () : Lemma (take_ranks_less_fact) =
  take_length_lemma ()

private let append_take_drop_ranks_less_lemma () : Lemma (append_take_drop_ranks_less_fact) =
  take_length_lemma ();
  drop_length_lemma ();
  append_sums_lengths_lemma ()

private let drop_zero_lemma () : Lemma (drop_zero_fact) =
  ()

private let take_zero_lemma () : Lemma (take_zero_fact) =
  ()

private let rec drop_then_drop_helper (#ty: Type) (s: seq ty) (m: nat) (n: nat)
  : Lemma (requires m + n <= length s /\ length (drop s m) = length s - m)
          (ensures  drop (drop s m) n == drop s (m + n)) =
  match s with
  | [] -> ()
  | hd :: tl -> 
    if m = 0
    then () 
    else (
      drop_length_lemma ();
      drop_then_drop_helper tl (m - 1) n
    )

private let drop_then_drop_lemma () : Lemma (requires drop_length_fact u#a) (ensures drop_then_drop_fact u#a ()) =
  introduce forall (ty: Type) (s: seq ty) (m: nat) (n: nat).
              m + n <= length s ==> drop (drop s m) n == drop s (m + n)
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (drop s m) = length s - m); // triggers drop_length_fact
      drop_then_drop_helper s m n
    )

/// Finally, we use all the lemmas for all the facts to establish
/// `all_seq_facts`.  To get all those facts in scope, one can
/// invoke `all_seq_facts_lemma`.

let all_seq_facts_lemma () : Lemma (all_seq_facts u#a) =
  length_of_empty_is_zero_lemma u#a ();
  length_zero_implies_empty_lemma u#a ();
  singleton_length_one_lemma u#a ();
  build_increments_length_lemma u#a ();
  index_into_build_lemma u#a ();
  append_sums_lengths_lemma u#a ();
  index_into_singleton_lemma u#a ();
  index_after_append_lemma u#a ();
  update_maintains_length_lemma u#a ();
  update_then_index_lemma u#a ();
  contains_iff_exists_index_lemma u#a ();
  empty_doesnt_contain_anything_lemma u#a ();
  build_contains_equiv_lemma u#a ();
  take_contains_equiv_exists_lemma u#a ();
  drop_contains_equiv_exists_lemma u#a ();
  equal_def_lemma u#a ();
  extensionality_lemma u#a ();
  is_prefix_def_lemma u#a ();
  take_length_lemma u#a ();
  index_into_take_lemma u#a ();
  drop_length_lemma u#a ();
  index_into_drop_lemma u#a ();
  drop_index_offset_lemma u#a ();
  append_then_take_or_drop_lemma u#a ();
  take_commutes_with_in_range_update_lemma u#a ();
  take_ignores_out_of_range_update_lemma u#a ();
  drop_commutes_with_in_range_update_lemma u#a ();
  drop_ignores_out_of_range_update_lemma u#a ();
  drop_commutes_with_build_lemma u#a ();
  rank_def_lemma u#a ();
  element_ranks_less_lemma u#a ();
  drop_ranks_less_lemma u#a ();
  take_ranks_less_lemma u#a ();
  append_take_drop_ranks_less_lemma u#a ();
  drop_zero_lemma u#a ();
  take_zero_lemma u#a ();
  drop_then_drop_lemma u#a ()
