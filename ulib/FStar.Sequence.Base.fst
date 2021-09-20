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
about sequences, and provides a lemma `all_dafny_seq_facts_lemma` one
can call to bring them into context.  The properties are modeled after
those in the Dafny sequence axioms, with patterns for quantifiers
chosen as in those axioms.

@summary Type, functions, and properties of sequences
*)
module FStar.Sequence.Base

open FStar.List.Tot

/// Internally, we represent a sequence as a list.

type seq (ty: Type) = list ty

/// We represent the Dafny function `Seq#Length` with `seq_length`:
///
/// function Seq#Length<T>(Seq T): int;

let seq_length = length

/// We represent the Dafny function `Seq#Empty` with `seq_empty`:
/// 
/// function Seq#Empty<T>(): Seq T;

let seq_empty (#ty: Type) : seq ty = []

/// We represent the Dafny function `Seq#Singleton` with `seq_singleton`:
///
/// function Seq#Singleton<T>(T): Seq T;

let seq_singleton (#ty: Type) (v: ty) : seq ty =
  [v]

/// We represent the Dafny function `Seq#Index` with `seq_index`:
///
/// function Seq#Index<T>(Seq T, int): T;

let seq_index (#ty: Type) (s: seq ty) (i: nat{i < seq_length s}) : ty =
  index s i

/// We represent the Dafny function `Seq#Build` with `seq_build`:
/// 
/// function Seq#Build<T>(s: Seq T, val: T): Seq T;

let seq_build (#ty: Type) (s: seq ty) (v: ty) : seq ty =
  append s [v]

/// We represent the Dafny function `Seq#Append` with `seq_append`:
///
/// function Seq#Append<T>(Seq T, Seq T): Seq T;

let seq_append = append

/// We represent the Dafny function `Seq#Update` with `seq_update`:
///
/// function Seq#Update<T>(Seq T, int, T): Seq T;

let seq_update (#ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty) : seq ty =
  let s1, _, s2 = split3 s i in
  append s1 (append [v] s2)

/// We represent the Dafny function `Seq#Contains` with `seq_contains`:
///
/// function Seq#Contains<T>(Seq T, T): bool;

let seq_contains (#ty: Type) (s: seq ty) (v: ty) : Type0 =
  memP v s

/// We represent the Dafny function `Seq#Take` with `seq_take`:
///
/// function Seq#Take<T>(s: Seq T, howMany: int): Seq T;

let seq_take (#ty: Type) (s: seq ty) (howMany: nat{howMany <= seq_length s}) : seq ty =
  let result, _ = splitAt howMany s in
  result

/// We represent the Dafny function `Seq#Drop` with `seq_drop`:
///
/// function Seq#Drop<T>(s: Seq T, howMany: int): Seq T;

let seq_drop (#ty: Type) (s: seq ty) (howMany: nat{howMany <= seq_length s}) : seq ty =
  let _, result = splitAt howMany s in
  result

/// We represent the Dafny function `Seq#Equal` with `seq_equal`.
///
/// function Seq#Equal<T>(Seq T, Seq T): bool;

let seq_equal (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
  seq_length s0 == seq_length s1 /\
    (forall j.{:pattern seq_index s0 j \/ seq_index s1 j}
      0 <= j && j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

/// Instead of representing the Dafny function `Seq#SameUntil`, which
/// is only ever used in Dafny to represent prefix relations, we
/// instead use `seq_is_prefix`.
///
/// function Seq#SameUntil<T>(Seq T, Seq T, int): bool;

let seq_is_prefix (#ty: Type) (s0: seq ty) (s1: seq ty) : Type0 =
    seq_length s0 <= seq_length s1
  /\ (forall (j: nat).{:pattern seq_index s0 j \/ seq_index s1 j}
     j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

/// We represent the Dafny function `Seq#Rank` with `seq_rank`.
///
/// function Seq#Rank<T>(Seq T): int;

let seq_rank (#ty: Type) (v: ty) = v

/// We now prove each of the facts that comprise `all_dafny_seq_facts`.
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
  introduce forall (ty: Type) (s: seq ty) (v: ty). seq_length (seq_build s v) = 1 + seq_length s
  with (
    append_length s [v]
  )

private let rec index_into_build_helper (#ty: Type) (s: list ty) (v: ty) (i: nat{i < length (append s [v])})
  : Lemma (requires i <= length s)
          (ensures  index (append s [v]) i == (if i = length s then v else index s i)) =
  append_length s [v];
  match s with
  | [] -> ()
  | hd :: tl ->
      if i = 0 then () else index_into_build_helper tl v (i - 1)

private let index_into_build_lemma ()
  : Lemma (requires build_increments_length_fact)
          (ensures  index_into_build_fact ()) =
  introduce forall (ty: Type) (s: seq ty) (v: ty) (i: nat{i < seq_length (seq_build s v)}).
                (i = seq_length s ==> seq_index (seq_build s v) i == v)
              /\ (i <> seq_length s ==> seq_index (seq_build s v) i == seq_index s i)
  with (
    index_into_build_helper s v i
  )

private let append_sums_lengths_lemma () : Lemma (append_sums_lengths_fact) =
  introduce forall (ty: Type) (s0: seq ty) (s1: seq ty). seq_length (seq_append s0 s1) = seq_length s0 + seq_length s1
  with (
    append_length s0 s1
  )

private let index_into_singleton_lemma (_: squash singleton_length_one_fact) : Lemma (index_into_singleton_fact ()) =
  ()

private let rec index_after_append_helper (ty: Type) (s0: list ty) (s1: list ty) (n: nat)
  : Lemma (requires n < length (append s0 s1) && length (append s0 s1) = length s0 + length s1)
          (ensures  index (append s0 s1) n == (if n < length s0 then index s0 n else index s1 (n - length s0))) =
  match s0 with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else index_after_append_helper ty tl s1 (n - 1)

private let index_after_append_lemma (_: squash append_sums_lengths_fact) : Lemma (index_after_append_fact ()) =
  introduce
    forall (ty: Type) (s0: seq ty) (s1: seq ty) (n: nat{n < seq_length (seq_append s0 s1)}).
        (n < seq_length s0 ==> seq_index (seq_append s0 s1) n == seq_index s0 n)
      /\ (seq_length s0 <= n ==> seq_index (seq_append s0 s1) n == seq_index s1 (n - seq_length s0))
  with (
    index_after_append_helper ty s0 s1 n
  )

private let rec lemma_splitAt_fst_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures  (length (fst (splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n - 1) l'

private let update_maintains_length_helper (#ty: Type) (s: list ty) (i: nat{i < length s}) (v: ty)
  : Lemma (length (seq_update s i v) = length s) =
  let s1, _, s2 = split3 s i in
    lemma_splitAt_fst_length i s;
    lemma_splitAt_snd_length i s;
    append_length [v] s2;
    append_length s1 (append [v] s2)

private let update_maintains_length_lemma () : Lemma (update_maintains_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty).
    seq_length (seq_update s i v) = seq_length s
  with (
    update_maintains_length_helper s i v
  )

private let rec update_then_index_helper
  (#ty: Type)
  (s: list ty)
  (i: nat{i < length s})
  (v: ty)
  (n: nat{n < length (seq_update s i v)})
  : Lemma (requires n < length s)
          (ensures  index (seq_update s i v) n == (if i = n then v else index s n)) =
  match s with
  | hd :: tl ->
      if i = 0 || n = 0 then ()
      else update_then_index_helper tl (i - 1) v (n - 1)

private let update_then_index_lemma () : Lemma (update_then_index_fact) =
  update_maintains_length_lemma ();
  introduce
    forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty) (n: nat{n < seq_length (seq_update s i v)}).
      n < seq_length s ==>
          (i = n ==> seq_index (seq_update s i v) n == v)
        /\ (i <> n ==> seq_index (seq_update s i v) n == seq_index s n)
  with
    introduce _ ==> _
    with given_antecedent. (
      update_then_index_helper s i v n
    )

private let contains_iff_exists_index_lemma () : Lemma (contains_iff_exists_index_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (x: ty).
      seq_contains s x <==> (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x)
  with (
    introduce seq_contains s x ==> (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x)
    with given_antecedent. (
      introduce exists (i: nat). i < seq_length s /\ seq_index s i == x
      with (index_of s x) and ()
    );
    introduce (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x) ==> seq_contains s x
    with given_antecedent. (
      eliminate exists (i: nat). i < seq_length s /\ seq_index s i == x
      returns _
      with _. lemma_index_memP s i
    )
  )

private let empty_doesnt_contain_anything_lemma () : Lemma (empty_doesnt_contain_anything_fact) =
  ()

private let rec build_contains_equiv_helper (ty: Type) (s: list ty) (v: ty) (x: ty)
  : Lemma (memP x (append s [v]) <==> (v == x \/ memP x s)) =
  match s with
  | [] -> ()
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns memP x (append s [v]) <==> (v == x \/ memP x s)
     with _. ()
     and _. build_contains_equiv_helper ty tl v x

private let build_contains_equiv_lemma () : Lemma (build_contains_equiv_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (v: ty) (x: ty).
      seq_contains (seq_build s v) x <==> (v == x \/ seq_contains s x)
  with (
    build_contains_equiv_helper ty s v x
  )

private let rec take_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires memP x (seq_take s n))
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
          (ensures  memP x (seq_take s n)) =
  match s with
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns memP x (seq_take s n)
     with case_x_eq_hd. ()
     and case_x_ne_hd. take_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1)

private let take_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (memP x (seq_take s n) <==>
           (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)) =
  introduce memP x (seq_take s n) ==>
              (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)
  with given_antecedent. (take_contains_equiv_exists_helper1 ty s n x);
  introduce (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x) ==>
              memP x (seq_take s n)
  with given_antecedent. (
    eliminate exists (i: nat). i < n /\ i < length s /\ index s i == x
    returns _
    with _. take_contains_equiv_exists_helper2 ty s n x i
  )

private let take_contains_equiv_exists_lemma () : Lemma (take_contains_equiv_exists_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).
              seq_contains (seq_take s n) x <==>
              (exists (i: nat). i < n /\ i < seq_length s /\ seq_index s i == x)
  with (
    take_contains_equiv_exists_helper3 ty s n x
  )

private let rec drop_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires memP x (seq_drop s n))
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

private let rec drop_contains_equiv_exists_helper2 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty) (i: nat)
  : Lemma (requires (n <= i /\ i < length s /\ index s i == x))
          (ensures  memP x (seq_drop s n)) =
  match s with
  | hd :: tl ->
     eliminate n == 0 \/ n <> 0
     returns memP x (seq_drop s n)
     with _. lemma_index_memP s i
     and _. (
       drop_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1);
       eliminate exists (i_tl: nat). n - 1 <= i_tl /\ i_tl < length tl /\ index tl i_tl == x
       returns _
       with _.
         introduce exists i. n <= i /\ i < length s /\ index s i == x with (i_tl + 1) and ())

private let drop_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (memP x (seq_drop s n) <==>
           (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)) =
  introduce memP x (seq_drop s n) ==>
              (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)
  with given_antecedent. (
    drop_contains_equiv_exists_helper1 ty s n x);
    introduce (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x) ==>
                memP x (seq_drop s n)
    with given_antecedent. (
      eliminate exists (i: nat). n <= i /\ i < length s /\ index s i == x
      returns _
      with _. drop_contains_equiv_exists_helper2 ty s n x i
    )

private let drop_contains_equiv_exists_lemma () : Lemma (drop_contains_equiv_exists_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).
      seq_contains (seq_drop s n) x <==>
      (exists (i: nat).{:pattern seq_index s i} n <= i /\ i < seq_length s /\ seq_index s i == x)
  with (
    drop_contains_equiv_exists_helper3 ty s n x;
    assert (memP x (seq_drop s n) <==>
            (exists (i: nat). n <= i /\ i < length s /\ seq_index s i == x))
  )

private let seq_equal_def_lemma () : Lemma (seq_equal_def_fact) =
  ()

private let seq_extensionality_lemma () : Lemma (seq_extensionality_fact) =
  introduce forall (ty: Type) (a: seq ty) (b: seq ty). seq_equal a b ==> a == b
  with
    introduce _ ==> _
    with given_antecedent. (
      introduce forall (i: nat) . i < length a ==> index a i == index b i
      with
        introduce _ ==> _
        with given_antecedent. (
          assert (seq_index a i == seq_index b i) // needed to trigger
        );
      FStar.List.Tot.Properties.index_extensionality a b
    )

private let seq_is_prefix_def_lemma () : Lemma (seq_is_prefix_def_fact) =
  ()

private let take_length_lemma () : Lemma (take_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
    n <= seq_length s ==> seq_length (seq_take s n) = n
  with
    introduce _ ==> _
    with given_antecedent. (
      lemma_splitAt_fst_length n s
    )

private let rec index_into_take_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < n && n <= length s /\ length (seq_take s n) = n)
          (ensures  index (seq_take s n) j == index s j) =
  match s with
  | hd :: tl -> if j = 0 || n = 0 then () else index_into_take_helper tl (n - 1) (j - 1)

private let index_into_take_lemma ()
  : Lemma (requires take_length_fact) (ensures index_into_take_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
      j < n && n <= seq_length s ==> seq_index (seq_take s n) j == seq_index s j
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (length (seq_take s n) == n); // triggers take_length_fact
      index_into_take_helper s n j
    )

private let drop_length_lemma () : Lemma (drop_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
              n <= seq_length s ==> seq_length (seq_drop s n) = seq_length s - n
  with
    introduce _ ==> _
    with given_antecedent. (
      lemma_splitAt_snd_length n s
    )

private let rec index_into_drop_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < length s - n /\ length (seq_drop s n) = length s - n)
          (ensures  index (seq_drop s n) j == index s (j + n)) =
  match s with
  | hd :: tl -> if n = 0 then () else index_into_drop_helper tl (n - 1) j

private let index_into_drop_lemma ()
  : Lemma (requires drop_length_fact) (ensures index_into_drop_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
      j < seq_length s - n ==> seq_index (seq_drop s n) j == seq_index s (j + n)
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_drop s n) = seq_length s - n); // triggers drop_length_fact
      index_into_drop_helper s n j
    )

private let drop_index_offset_lemma ()
  : Lemma (requires drop_length_fact) (ensures drop_index_offset_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (k: nat).
      n <= k && k < seq_length s ==> seq_index (seq_drop s n) (k - n) == seq_index s k
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_drop s n) = seq_length s - n); // triggers drop_length_fact
      index_into_drop_helper s n (k - n)
    )

private let rec append_then_take_or_drop_helper (#ty: Type) (s: list ty) (t: list ty) (n: nat)
  : Lemma (requires n = length s /\ length (append s t) = length s + length t)
          (ensures  seq_take (append s t) n == s /\ seq_drop (append s t) n == t) =
  match s with
  | [] -> ()
  | hd :: tl -> append_then_take_or_drop_helper tl t (n - 1)

private let append_then_take_or_drop_lemma ()
  : Lemma (requires append_sums_lengths_fact) (ensures append_then_take_or_drop_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (t: seq ty) (n: nat).
      n = seq_length s ==> seq_take (seq_append s t) n == s /\ seq_drop (seq_append s t) n == t
  with
    introduce _ ==> _
    with given_antecedent. (
      append_then_take_or_drop_helper s t n
    )

private let rec take_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (seq_update s i v) = length s
                    /\ length (seq_take s n) = n)
          (ensures  seq_take (seq_update s i v) n == seq_update (seq_take s n) i v) =
  match s with
  | hd :: tl -> if i = 0 then () else take_commutes_with_in_range_update_helper tl (i - 1) v (n - 1)

private let take_commutes_with_in_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact /\ take_length_fact)
          (ensures take_commutes_with_in_range_update_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      i < n && n <= seq_length s ==>
      seq_take (seq_update s i v) n == seq_update (seq_take s n) i v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      assert (seq_length (seq_take s n) = n);                // triggers take_length_fact
      take_commutes_with_in_range_update_helper s i v n
    )

private let rec take_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (seq_update s i v) = length s)
          (ensures  seq_take (seq_update s i v) n == seq_take s n) =
  match s with
  | hd :: tl -> if n = 0 then () else take_ignores_out_of_range_update_helper tl (i - 1) v (n - 1)

private let take_ignores_out_of_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact)
          (ensures take_ignores_out_of_range_update_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      n <= i && i < seq_length s ==>
      seq_take (seq_update s i v) n == seq_take s n
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      take_ignores_out_of_range_update_helper s i v n
    )

private let rec drop_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (seq_update s i v) = length s
                    /\ length (seq_drop s n) = length s - n)
          (ensures  seq_drop (seq_update s i v) n ==
                      seq_update (seq_drop s n) (i - n) v) =
  match s with
  | hd :: tl -> if n = 0 then () else drop_commutes_with_in_range_update_helper tl (i - 1) v (n - 1)

private let drop_commutes_with_in_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact /\ drop_length_fact)
          (ensures drop_commutes_with_in_range_update_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      n <= i && i < seq_length s ==>
      seq_drop (seq_update s i v) n == seq_update (seq_drop s n) (i - n) v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      assert (seq_length (seq_drop s n) = length s - n);     // triggers drop_length_fact
      drop_commutes_with_in_range_update_helper s i v n
    )

private let rec drop_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (seq_update s i v) = length s)
          (ensures  seq_drop (seq_update s i v) n == seq_drop s n) =
  match s with
  | hd :: tl -> if i = 0 then () else drop_ignores_out_of_range_update_helper tl (i - 1) v (n - 1)

private let drop_ignores_out_of_range_update_lemma ()
  : Lemma (requires update_maintains_length_fact)
          (ensures drop_ignores_out_of_range_update_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).
      i < n && n <= seq_length s ==>
      seq_drop (seq_update s i v) n == seq_drop s n
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      drop_ignores_out_of_range_update_helper s i v n
    )

private let rec drop_commutes_with_build_helper (#ty: Type) (s: list ty) (v: ty) (n: nat)
  : Lemma (requires n <= length s /\ length (append s [v]) = 1 + length s)
          (ensures  seq_drop (append s [v]) n == append (seq_drop s n) [v]) =
  match s with
  | [] -> ()
  | hd :: tl -> if n = 0 then () else drop_commutes_with_build_helper tl v (n - 1)

private let drop_commutes_with_build_lemma ()
  : Lemma (requires build_increments_length_fact)
          (ensures  drop_commutes_with_build_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (v: ty) (n: nat).
      n <= seq_length s ==> seq_drop (seq_build s v) n == seq_build (seq_drop s n) v
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_build s v) = 1 + seq_length s); // triggers build_increments_length_fact
      drop_commutes_with_build_helper s v n
    )

private let seq_rank_def_lemma () : Lemma (seq_rank_def_fact) =
  ()

private let element_ranks_less_lemma () : Lemma (element_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat). i < seq_length s ==> seq_rank (seq_index s i) << seq_rank s
  with
    introduce _ ==> _
    with given_antecedent. (
      contains_iff_exists_index_lemma ();
      assert (seq_contains s (seq_index s i));
      memP_precedes (seq_index s i) s
    )

private let rec drop_ranks_less_helper (ty: Type) (s: list ty) (i: nat)
  : Lemma (requires 0 < i && i <= length s)
          (ensures  seq_drop s i << s) =
  match s with
  | [] -> ()
  | hd :: tl -> if i = 1 then () else drop_ranks_less_helper ty tl (i - 1)

private let drop_ranks_less_lemma () : Lemma (drop_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat).
              0 < i && i <= seq_length s ==> seq_rank (seq_drop s i) << seq_rank s
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
  : Lemma (requires m + n <= length s /\ length (seq_drop s m) = length s - m)
          (ensures  seq_drop (seq_drop s m) n == seq_drop s (m + n)) =
  match s with
  | [] -> ()
  | hd :: tl -> if m = 0 then () else drop_then_drop_helper tl (m - 1) n

private let drop_then_drop_lemma () : Lemma (requires drop_length_fact) (ensures drop_then_drop_fact ()) =
  introduce forall (ty: Type) (s: seq ty) (m: nat) (n: nat).
              m + n <= seq_length s ==> seq_drop (seq_drop s m) n == seq_drop s (m + n)
  with
    introduce _ ==> _
    with given_antecedent. (
      assert (seq_length (seq_drop s m) = seq_length s - m); // triggers drop_length_fact
      drop_then_drop_helper s m n
    )

/// Finally, we use all the lemmas for all the facts to establish
/// `all_dafny_seq_facts`.  To get all those facts in scope, one can
/// invoke `all_dafny_seq_facts_lemma`.

let all_dafny_seq_facts_lemma () : Lemma (all_dafny_seq_facts) =
  length_of_empty_is_zero_lemma ();
  length_zero_implies_empty_lemma ();
  singleton_length_one_lemma ();
  build_increments_length_lemma ();
  index_into_build_lemma ();
  append_sums_lengths_lemma ();
  index_into_singleton_lemma ();
  index_after_append_lemma ();
  update_maintains_length_lemma ();
  update_then_index_lemma ();
  contains_iff_exists_index_lemma ();
  empty_doesnt_contain_anything_lemma ();
  build_contains_equiv_lemma ();
  take_contains_equiv_exists_lemma ();
  drop_contains_equiv_exists_lemma ();
  seq_equal_def_lemma ();
  seq_extensionality_lemma ();
  seq_is_prefix_def_lemma ();
  take_length_lemma ();
  index_into_take_lemma ();
  drop_length_lemma ();
  index_into_drop_lemma ();
  drop_index_offset_lemma ();
  append_then_take_or_drop_lemma ();
  take_commutes_with_in_range_update_lemma ();
  take_ignores_out_of_range_update_lemma ();
  drop_commutes_with_in_range_update_lemma ();
  drop_ignores_out_of_range_update_lemma ();
  drop_commutes_with_build_lemma ();
  seq_rank_def_lemma ();
  element_ranks_less_lemma ();
  drop_ranks_less_lemma ();
  take_ranks_less_lemma ();
  append_take_drop_ranks_less_lemma ();
  drop_zero_lemma ();
  take_zero_lemma ();
  drop_then_drop_lemma ()
