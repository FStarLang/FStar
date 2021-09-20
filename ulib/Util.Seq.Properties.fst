(*
   Copyright 2008-2021 Jay Lorch, Rustan Leino, Alex Summers, Dan
   Rosen, Microsoft Research, and contributors to the Dafny Project

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
This module states and proves some properties about sequences, and
provides a lemma `all_dafny_seq_facts_lemma` one can call to bring
them into context.  The properties are modeled after those in the
Dafny sequence axioms, with patterns for quantifiers chosen as in
those axioms.

@summary Properties of sequences
*)
module Util.Seq.Properties

open FStar.List.Tot
open Util.Seq.Defs

/// We don't need the following axiom since we return a nat from seq_length:
/// 
/// axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));

/// We represent the following Dafny axiom with `length_of_empty_is_zero_fact`:
///
/// axiom (forall<T> :: { Seq#Empty(): Seq T } Seq#Length(Seq#Empty(): Seq T) == 0);

private let length_of_empty_is_zero_fact =
  forall (ty: Type).{:pattern seq_empty ty} seq_length (seq_empty ty) = 0

private let length_of_empty_is_zero_lemma () : Lemma (length_of_empty_is_zero_fact) =
  introduce forall (ty: Type). seq_length (seq_empty ty) = 0
  with (
    reveal_seq_length ty;
    reveal_seq_empty ty
  )

/// We represent the following Dafny axiom with `length_zero_implies_empty_fact`:
///
/// axiom (forall<T> s: Seq T :: { Seq#Length(s) }
///   (Seq#Length(s) == 0 ==> s == Seq#Empty())

private let length_zero_implies_empty_fact =
  forall (ty: Type) (s: seq ty).{:pattern seq_length s} seq_length s = 0 ==> s == seq_empty ty

private let length_zero_implies_empty_lemma () : Lemma (length_zero_implies_empty_fact) =
  introduce forall (ty: Type) (s: seq ty). seq_length s = 0 ==> s == seq_empty ty
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_empty ty
    )

/// We represent the following Dafny axiom with `singleton_length_one_fact`:
/// 
/// axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);

private let singleton_length_one_fact =
  forall (ty: Type) (v: ty).{:pattern seq_length (seq_singleton v)} seq_length (seq_singleton v) = 1

private let singleton_length_one_lemma () : Lemma (singleton_length_one_fact) =
  introduce forall (ty: Type) (v: ty). seq_length (seq_singleton v) = 1
  with (
    reveal_seq_singleton ty;
    reveal_seq_length ty
  )

/// We represent the following Dafny axiom with `build_increments_length_fact`:
///
/// axiom (forall<T> s: Seq T, v: T ::
///   { Seq#Build(s,v) }
///   Seq#Length(Seq#Build(s,v)) == 1 + Seq#Length(s));

private let build_increments_length_fact =
  forall (ty: Type) (s: seq ty) (v: ty).{:pattern seq_build s v}
    seq_length (seq_build s v) = 1 + seq_length s

private let build_increments_length_lemma () : Lemma (build_increments_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (v: ty). seq_length (seq_build s v) = 1 + seq_length s
  with (
    reveal_seq_length ty;
    reveal_seq_build ty;
    append_length s [v]
  )

/// We represent the following Dafny axiom with `index_into_build_fact`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Index(Seq#Build(s,v), i) }
///   (i == Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == v) &&
///   (i != Seq#Length(s) ==> Seq#Index(Seq#Build(s,v), i) == Seq#Index(s, i)));

private let index_into_build_fact (_: squash build_increments_length_fact) =
  forall (ty: Type) (s: seq ty) (v: ty) (i: nat{i < seq_length (seq_build s v)})
    .{:pattern seq_index (seq_build s v) i}
      (i = seq_length s ==> seq_index (seq_build s v) i == v)
    /\ (i <> seq_length s ==> seq_index (seq_build s v) i == seq_index s i)

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
    reveal_seq_index ty;
    reveal_seq_build ty;
    reveal_seq_length ty;
    index_into_build_helper s v i
  )

/// We represent the following Dafny axiom with `append_sums_lengths_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
///   Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));

private let append_sums_lengths_fact =
  forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_length (seq_append s0 s1)}
    seq_length (seq_append s0 s1) = seq_length s0 + seq_length s1

private let append_sums_lengths_lemma () : Lemma (append_sums_lengths_fact) =
  introduce forall (ty: Type) (s0: seq ty) (s1: seq ty). seq_length (seq_append s0 s1) = seq_length s0 + seq_length s1
  with (
    reveal_seq_length ty;
    reveal_seq_append ty;
    append_length s0 s1
  )

/// We represent the following Dafny axiom with `index_into_singleton_fact`:
///
/// axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);

private let index_into_singleton_fact (_: squash singleton_length_one_fact) =
  forall (ty: Type) (v: ty).{:pattern seq_index (seq_singleton v) 0}
     seq_index (seq_singleton v) 0 == v

private let index_into_singleton_lemma (_: squash singleton_length_one_fact) : Lemma (index_into_singleton_fact ()) =
  introduce forall (ty: Type) (v: ty). seq_index (seq_singleton v) 0 == v
  with (
    reveal_seq_index ty;
    reveal_seq_singleton ty
  )

/// We represent the following axiom with `index_after_append_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
///   (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
///   (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));

private let index_after_append_fact (_: squash append_sums_lengths_fact) =
  forall (ty: Type) (s0: seq ty) (s1: seq ty) (n: nat{n < seq_length (seq_append s0 s1)})
    .{:pattern seq_index (seq_append s0 s1) n}
      (n < seq_length s0 ==> seq_index (seq_append s0 s1) n == seq_index s0 n)
    /\ (seq_length s0 <= n ==> seq_index (seq_append s0 s1) n == seq_index s1 (n - seq_length s0))

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
    reveal_seq_append ty;
    reveal_seq_index ty;
    reveal_seq_length ty;
    index_after_append_helper ty s0 s1 n
  )

/// We represent the following Dafny axiom with `update_maintains_length`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
///   0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));

private let update_maintains_length_fact =
  forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty).{:pattern seq_length (seq_update s i v)}
    seq_length (seq_update s i v) = seq_length s

private let rec lemma_splitAt_fst_length (#a:Type) (n:nat) (l:list a) :
  Lemma
    (requires (n <= length l))
    (ensures  (length (fst (splitAt n l)) = n)) =
  match n, l with
  | 0, _ -> ()
  | _, [] -> ()
  | _, _ :: l' -> lemma_splitAt_fst_length (n - 1) l'

private let update_maintains_length_helper (#ty: Type) (s: list ty) (i: nat{i < length s}) (v: ty)
  : Lemma (length (seq_update_fn s i v) = length s) =
  let s1, _, s2 = split3 s i in
    lemma_splitAt_fst_length i s;
    lemma_splitAt_snd_length i s;
    append_length [v] s2;
    append_length s1 (append [v] s2)

private let update_maintains_length_lemma () : Lemma (update_maintains_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty).
    seq_length (seq_update s i v) = seq_length s
  with (
    reveal_seq_length ty;
    reveal_seq_update ty;
    update_maintains_length_helper s i v
  )

/// We represent the following Dafny axiom with `update_then_index_fact`:
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
///   0 <= n && n < Seq#Length(s) ==>
///     (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v) &&
///     (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));

private let update_then_index_fact =
  forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty) (n: nat{n < seq_length (seq_update s i v)})
      .{:pattern seq_index (seq_update s i v) n}
      n < seq_length s ==>
          (i = n ==> seq_index (seq_update s i v) n == v)
        /\ (i <> n ==> seq_index (seq_update s i v) n == seq_index s n)

private let rec update_then_index_helper
  (#ty: Type)
  (s: list ty)
  (i: nat{i < length s})
  (v: ty)
  (n: nat{n < length (seq_update_fn s i v)})
  : Lemma (requires n < length s)
          (ensures  index (seq_update_fn s i v) n == (if i = n then v else index s n)) =
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
      reveal_seq_index ty;
      reveal_seq_update ty;
      reveal_seq_length ty;
      update_then_index_helper s i v n
    )

/// We represent the following Dafny axiom with `contains_iff_exists_index_fact`:
///
/// axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
///   Seq#Contains(s,x) <==>
///     (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));

private let contains_iff_exists_index_fact =
  forall (ty: Type) (s: seq ty) (x: ty).{:pattern seq_contains s x}
    seq_contains s x <==> (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x)

private let contains_iff_exists_index_lemma () : Lemma (contains_iff_exists_index_fact) =
  introduce 
    forall (ty: Type) (s: seq ty) (x: ty).
      seq_contains s x <==> (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x)
  with (
    reveal_seq_contains ty;
    reveal_seq_index ty;
    reveal_seq_length ty;
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

/// We represent the following Dafny axiom with `empty_doesnt_contain_fact`:
///
/// axiom (forall<T> x: T ::
///   { Seq#Contains(Seq#Empty(), x) }
///   !Seq#Contains(Seq#Empty(), x));

private let empty_doesnt_contain_anything_fact =
  forall (ty: Type) (x: ty).{:pattern seq_contains (seq_empty ty) x} ~(seq_contains (seq_empty ty) x)

private let empty_doesnt_contain_anything_lemma () : Lemma (empty_doesnt_contain_anything_fact) =
  introduce 
    forall (ty: Type) (x: ty). ~(seq_contains (seq_empty ty) x)
  with (
    reveal_seq_contains ty;
    reveal_seq_empty ty
  )

/// We represent the following Dafny axiom with `build_contains_equiv_fact`:
///
/// axiom (forall<T> s: Seq T, v: T, x: T ::  // needed to prove things like '4 in [2,3,4]', see method TestSequences0 in SmallTests.dfy
///   { Seq#Contains(Seq#Build(s, v), x) }
///     Seq#Contains(Seq#Build(s, v), x) <==> (v == x || Seq#Contains(s, x)));

private let build_contains_equiv_fact =
  forall (ty: Type) (s: seq ty) (v: ty) (x: ty).{:pattern seq_contains (seq_build s v) x}
    seq_contains (seq_build s v) x <==> (v == x \/ seq_contains s x)

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
    reveal_seq_contains ty;
    reveal_seq_build ty;
    build_contains_equiv_helper ty s v x
  )

/// We represent the following Dafny axiom with `take_contains_equiv_exists_fact`:
///
/// axiom (forall<T> s: Seq T, n: int, x: T ::
///   { Seq#Contains(Seq#Take(s, n), x) }
///   Seq#Contains(Seq#Take(s, n), x) <==>
///     (exists i: int :: { Seq#Index(s, i) }
///       0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));

private let take_contains_equiv_exists_fact =
  forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).{:pattern seq_contains (seq_take s n) x}
    seq_contains (seq_take s n) x <==>
    (exists (i: nat).{:pattern seq_index s i} i < n /\ i < seq_length s /\ seq_index s i == x)

private let rec take_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires memP x (seq_take_fn s n))
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
          (ensures  memP x (seq_take_fn s n)) =
  match s with
  | hd :: tl ->
     eliminate x == hd \/ ~(x == hd)
     returns memP x (seq_take_fn s n)
     with case_x_eq_hd. ()
     and case_x_ne_hd. take_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1)

private let take_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (memP x (seq_take_fn s n) <==>
           (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)) =
  introduce memP x (seq_take_fn s n) ==>
              (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x)
  with given_antecedent. (take_contains_equiv_exists_helper1 ty s n x);
  introduce (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x) ==>
              memP x (seq_take_fn s n)
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
    reveal_seq_contains ty;
    reveal_seq_take ty;
    reveal_seq_length ty;
    reveal_seq_index ty;
    take_contains_equiv_exists_helper3 ty s n x
  )

/// We represent the following Dafny axiom with `drop_contains_equiv_exists_fact`:
///
/// axiom (forall<T> s: Seq T, n: int, x: T ::
///   { Seq#Contains(Seq#Drop(s, n), x) }
///   Seq#Contains(Seq#Drop(s, n), x) <==>
///     (exists i: int :: { Seq#Index(s, i) }
///       0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));

private let drop_contains_equiv_exists_fact =
  forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).{:pattern seq_contains (seq_drop s n) x}
    seq_contains (seq_drop s n) x <==>
    (exists (i: nat).{:pattern seq_index s i} n <= i && i < seq_length s /\ seq_index s i == x)

private let rec drop_contains_equiv_exists_helper1 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (requires memP x (seq_drop_fn s n))
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
          (ensures  memP x (seq_drop_fn s n)) =
  match s with
  | hd :: tl ->
     eliminate n == 0 \/ n <> 0
     returns memP x (seq_drop_fn s n)
     with _. lemma_index_memP s i
     and _. (
       drop_contains_equiv_exists_helper2 ty tl (n - 1) x (i - 1);
       eliminate exists (i_tl: nat). n - 1 <= i_tl /\ i_tl < length tl /\ index tl i_tl == x
       returns _
       with _.
         introduce exists i. n <= i /\ i < length s /\ index s i == x with (i_tl + 1) and ())

private let drop_contains_equiv_exists_helper3 (ty: Type) (s: list ty) (n: nat{n <= length s}) (x: ty)
  : Lemma (memP x (seq_drop_fn s n) <==>
           (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)) =
  introduce memP x (seq_drop_fn s n) ==>
              (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x)
  with given_antecedent. (
    drop_contains_equiv_exists_helper1 ty s n x);
    introduce (exists (i: nat).{:pattern index s i} n <= i /\ i < length s /\ index s i == x) ==>
                memP x (seq_drop_fn s n)
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
    reveal_seq_contains ty;
    reveal_seq_drop ty;
    reveal_seq_length ty;
    reveal_seq_index ty;
    drop_contains_equiv_exists_helper3 ty s n x;
    assert (memP x (seq_drop_fn s n) <==>
            (exists (i: nat). n <= i /\ i < length s /\ seq_index s i == x))
  )

/// We represent the following Dafny axiom with `seq_equal_def_fact`:
///
/// axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
///   Seq#Equal(s0,s1) <==>
///     Seq#Length(s0) == Seq#Length(s1) &&
///     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
///         0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

private let seq_equal_def_fact =
  forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_equal s0 s1}
    seq_equal s0 s1 <==>
    seq_length s0 == seq_length s1 /\
      (forall j.{:pattern seq_index s0 j \/ seq_index s1 j}
       0 <= j && j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

private let seq_equal_def_lemma () : Lemma (seq_equal_def_fact) =
  introduce
    forall (ty: Type) (s0: seq ty) (s1: seq ty).
      seq_equal s0 s1 <==>
      seq_length s0 == seq_length s1 /\
        (forall j.{:pattern seq_index s0 j \/ seq_index s1 j}
         0 <= j && j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)
  with
    reveal_seq_equal ty

/// We represent the following Dafny axiom with `seq_extensionality_fact`:
///
/// axiom (forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
///   Seq#Equal(a,b) ==> a == b);

private let seq_extensionality_fact =
  forall (ty: Type) (a: seq ty) (b: seq ty).{:pattern seq_equal a b}
    seq_equal a b ==> a == b

private let seq_extensionality_lemma () : Lemma (seq_extensionality_fact) =
  introduce forall (ty: Type) (a: seq ty) (b: seq ty). seq_equal a b ==> a == b
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_index ty;
      seq_equal_def_lemma ();
      introduce forall (i: nat) . i < length a ==> index a i == index b i
      with
        introduce _ ==> _
        with given_antecedent. (
          assert (seq_index a i == seq_index b i) // needed to trigger
        );
      FStar.List.Tot.Properties.index_extensionality a b
    )

/// We represent an analog of the following Dafny axiom with
/// `seq_is_prefix_def_fact`.  Our analog uses `seq_is_prefix` instead
/// of `Seq#SameUntil`.
///
/// axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
///   Seq#SameUntil(s0,s1,n) <==>
///     (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
///         0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));

private let seq_is_prefix_def_fact =
  forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_is_prefix s0 s1}
    seq_is_prefix s0 s1 <==>
      seq_length s0 <= seq_length s1
    /\ (forall (j: nat).{:pattern seq_index s0 j \/ seq_index s1 j}
         j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)

private let seq_is_prefix_def_lemma () : Lemma (seq_is_prefix_def_fact) =
  introduce
    forall (ty: Type) (s0: seq ty) (s1: seq ty).
      seq_is_prefix s0 s1 <==>
        seq_length s0 <= seq_length s1
      /\ (forall (j: nat).{:pattern seq_index s0 j \/ seq_index s1 j}
           j < seq_length s0 ==> seq_index s0 j == seq_index s1 j)
  with
    reveal_seq_is_prefix ty

/// We represent the following Dafny axiom with `take_length_fact`:
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
///   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n);

private let take_length_fact =
  forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_length (seq_take s n)}
    n <= seq_length s ==> seq_length (seq_take s n) = n

private let take_length_lemma () : Lemma (take_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
    n <= seq_length s ==> seq_length (seq_take s n) = n
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_take ty;
      lemma_splitAt_fst_length n s
    )

/// We represent the following Dafny axiom with `index_into_take_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, j: int ::
///   {:weight 25}
///   { Seq#Index(Seq#Take(s,n), j) }
///   { Seq#Index(s, j), Seq#Take(s,n) }
///   0 <= j && j < n && j < Seq#Length(s) ==>
///     Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));

private let index_into_take_fact (_ : squash take_length_fact) =
  forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
    {:pattern seq_index (seq_take s n) j \/ seq_index s j ; seq_take s n}
    j < n && n <= seq_length s ==> seq_index (seq_take s n) j == seq_index s j

private let rec index_into_take_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < n && n <= length s /\ length (seq_take_fn s n) = n)
          (ensures  index (seq_take_fn s n) j == index s j) =
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
      reveal_seq_length ty;
      reveal_seq_index ty;
      reveal_seq_take ty;
      assert (length (seq_take s n) == n); // triggers take_length_fact
      index_into_take_helper s n j
    )

/// We represent the following Dafny axiom with `drop_length_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
///   0 <= n && n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n);

private let drop_length_fact =
  forall (ty: Type) (s: seq ty) (n: nat).
    {:pattern seq_length (seq_drop s n)}
    n <= seq_length s ==> seq_length (seq_drop s n) = seq_length s - n

private let drop_length_lemma () : Lemma (drop_length_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat).
              n <= seq_length s ==> seq_length (seq_drop s n) = seq_length s - n
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_drop ty;
      lemma_splitAt_snd_length n s
    )

/// We represent the following Dafny axiom with `index_into_drop_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, j: int ::
///   {:weight 25}
///   { Seq#Index(Seq#Drop(s,n), j) }
///   0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
///     Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));

private let index_into_drop_fact (_ : squash drop_length_fact) =
  forall (ty: Type) (s: seq ty) (n: nat) (j: nat).
    {:pattern seq_index (seq_drop s n) j}
    j < seq_length s - n ==> seq_index (seq_drop s n) j == seq_index s (j + n)

private let rec index_into_drop_helper (#ty: Type) (s: list ty) (n: nat) (j: nat)
  : Lemma (requires j < length s - n /\ length (seq_drop_fn s n) = length s - n)
          (ensures  index (seq_drop_fn s n) j == index s (j + n)) =
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
      reveal_seq_length ty;
      reveal_seq_index ty;
      reveal_seq_drop ty;
      assert (seq_length (seq_drop s n) = seq_length s - n); // triggers drop_length_fact
      index_into_drop_helper s n j
    )

/// We represent the following Dafny axiom with `drop_index_offset_fact`.
///
/// axiom (forall<T> s: Seq T, n: int, k: int ::
///   {:weight 25}
///   { Seq#Index(s, k), Seq#Drop(s,n) }
///   0 <= n && n <= k && k < Seq#Length(s) ==>
///     Seq#Index(Seq#Drop(s,n), k-n) == Seq#Index(s, k));

private let drop_index_offset_fact (_ : squash drop_length_fact) =
  forall (ty: Type) (s: seq ty) (n: nat) (k: nat).
    {:pattern seq_index s k; seq_drop s n}
    n <= k && k < seq_length s ==> seq_index (seq_drop s n) (k - n) == seq_index s k

private let drop_index_offset_lemma ()
  : Lemma (requires drop_length_fact) (ensures drop_index_offset_fact ()) =
  introduce 
    forall (ty: Type) (s: seq ty) (n: nat) (k: nat).
      n <= k && k < seq_length s ==> seq_index (seq_drop s n) (k - n) == seq_index s k
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_index ty;
      reveal_seq_drop ty;
      assert (seq_length (seq_drop s n) = seq_length s - n); // triggers drop_length_fact
      index_into_drop_helper s n (k - n)
    )

/// We represent the following Dafny axiom with `append_then_take_or_drop_fact`.
///
/// axiom (forall<T> s, t: Seq T, n: int ::
///   { Seq#Take(Seq#Append(s, t), n) }
///   { Seq#Drop(Seq#Append(s, t), n) }
///   n == Seq#Length(s)
///   ==>
///   Seq#Take(Seq#Append(s, t), n) == s &&
///   Seq#Drop(Seq#Append(s, t), n) == t);

private let append_then_take_or_drop_fact (_ : squash append_sums_lengths_fact) =
  forall (ty: Type) (s: seq ty) (t: seq ty) (n: nat).
    {:pattern seq_take (seq_append s t) n \/ seq_drop (seq_append s t) n}
    n = seq_length s ==> seq_take (seq_append s t) n == s /\ seq_drop (seq_append s t) n == t

private let rec append_then_take_or_drop_helper (#ty: Type) (s: list ty) (t: list ty) (n: nat)
  : Lemma (requires n = length s /\ length (append s t) = length s + length t)
          (ensures  seq_take_fn (append s t) n == s /\ seq_drop_fn (append s t) n == t) =
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
      reveal_seq_length ty;
      reveal_seq_append ty;
      reveal_seq_drop ty;
      reveal_seq_take ty;
      append_then_take_or_drop_helper s t n
    )

/// We represent the following Dafny axiom with `take_commutes_with_in_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Take(Seq#Update(s, i, v), n) }
///         0 <= i && i < n && n <= Seq#Length(s) ==>
///         Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v) );

private let take_commutes_with_in_range_update_fact
  (_ : squash (update_maintains_length_fact /\ take_length_fact)) =
  forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern seq_take (seq_update s i v) n}
    i < n && n <= seq_length s ==>
    seq_take (seq_update s i v) n == seq_update (seq_take s n) i v

private let rec take_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (seq_update_fn s i v) = length s
                    /\ length (seq_take_fn s n) = n)
          (ensures  seq_take_fn (seq_update_fn s i v) n == seq_update_fn (seq_take_fn s n) i v) =
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
      reveal_seq_length ty;
      reveal_seq_update ty;
      reveal_seq_take ty;
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      assert (seq_length (seq_take s n) = n);                // triggers take_length_fact
      take_commutes_with_in_range_update_helper s i v n
    )

/// We represent the following Dafny axiom with `take_ignores_out_of_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Take(Seq#Update(s, i, v), n) }
///         n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));

private let take_ignores_out_of_range_update_fact (_ : squash update_maintains_length_fact) =
  forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern seq_take (seq_update s i v) n}
    n <= i && i < seq_length s ==>
    seq_take (seq_update s i v) n == seq_take s n

private let rec take_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (seq_update_fn s i v) = length s)
          (ensures  seq_take_fn (seq_update_fn s i v) n == seq_take_fn s n) =
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
      reveal_seq_length ty;
      reveal_seq_update ty;
      reveal_seq_take ty;
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      take_ignores_out_of_range_update_helper s i v n
    )

/// We represent the following Dafny axiom with `drop_commutes_with_in_range_update_fact`.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Drop(Seq#Update(s, i, v), n) }
///         0 <= n && n <= i && i < Seq#Length(s) ==>
///         Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );

private let drop_commutes_with_in_range_update_fact
  (_ : squash (update_maintains_length_fact /\ drop_length_fact)) =
  forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern seq_drop (seq_update s i v) n}
    n <= i && i < seq_length s ==>
    seq_drop (seq_update s i v) n == seq_update (seq_drop s n) (i - n) v

private let rec drop_commutes_with_in_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   n <= i
                    /\ i < length s
                    /\ length (seq_update_fn s i v) = length s
                    /\ length (seq_drop_fn s n) = length s - n)
          (ensures  seq_drop_fn (seq_update_fn s i v) n ==
                      seq_update_fn (seq_drop_fn s n) (i - n) v) =
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
      reveal_seq_length ty;
      reveal_seq_update ty;
      reveal_seq_drop ty;
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      assert (seq_length (seq_drop s n) = length s - n);     // triggers drop_length_fact
      drop_commutes_with_in_range_update_helper s i v n
    )

/// We represent the following Dafny axiom with `drop_ignores_out_of_range_update_fact`.
/// Jay noticed that it was unnecessarily weak, possibly due to a typo, so he reported this as
/// Dafny issue #1423 (https://github.com/dafny-lang/dafny/issues/1423) and updated it here.
///
/// axiom (forall<T> s: Seq T, i: int, v: T, n: int ::
///         { Seq#Drop(Seq#Update(s, i, v), n) }
///         0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));

private let drop_ignores_out_of_range_update_fact (_ : squash update_maintains_length_fact) =
  forall (ty: Type) (s: seq ty) (i: nat) (v: ty) (n: nat).{:pattern seq_drop (seq_update s i v) n}
    i < n && n <= seq_length s ==>
    seq_drop (seq_update s i v) n == seq_drop s n

private let rec drop_ignores_out_of_range_update_helper (#ty: Type) (s: list ty) (i: nat) (v: ty) (n: nat)
  : Lemma (requires   i < n
                    /\ n <= length s
                    /\ length (seq_update_fn s i v) = length s)
          (ensures  seq_drop_fn (seq_update_fn s i v) n == seq_drop_fn s n) =
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
      reveal_seq_length ty;
      reveal_seq_update ty;
      reveal_seq_drop ty;
      assert (seq_length (seq_update s i v) = seq_length s); // triggers update_maintains_length_fact
      drop_ignores_out_of_range_update_helper s i v n
    )

/// We represent the following Dafny axiom with `drop_commutes_with_build_fact`.
///
/// axiom (forall<T> s: Seq T, v: T, n: int ::
///         { Seq#Drop(Seq#Build(s, v), n) }
///         0 <= n && n <= Seq#Length(s) ==>
///         Seq#Drop(Seq#Build(s, v), n) == Seq#Build(Seq#Drop(s, n), v) );

private let drop_commutes_with_build_fact (_ : squash build_increments_length_fact) =
  forall (ty: Type) (s: seq ty) (v: ty) (n: nat).{:pattern seq_drop (seq_build s v) n}
    n <= seq_length s ==> seq_drop (seq_build s v) n == seq_build (seq_drop s n) v

private let rec drop_commutes_with_build_helper (#ty: Type) (s: list ty) (v: ty) (n: nat)
  : Lemma (requires n <= length s /\ length (append s [v]) = 1 + length s)
          (ensures  seq_drop_fn (append s [v]) n == append (seq_drop_fn s n) [v]) =
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
      reveal_seq_length ty;
      reveal_seq_build ty;
      reveal_seq_drop ty;
      assert (seq_length (seq_build s v) = 1 + seq_length s); // triggers build_increments_length_fact
      drop_commutes_with_build_helper s v n
    )

/// We prove, and make ambient, the definition of `seq_rank`.

private let seq_rank_def_fact =
  forall (ty: Type) (v: ty).{:pattern seq_rank v} seq_rank v == v

private let seq_rank_def_lemma () : Lemma (seq_rank_def_fact) =
  introduce forall (ty: Type) (v: ty). seq_rank v == v
  with reveal_seq_rank ty

/// We represent the following Dafny axiom with `element_ranks_less_fact`.
///
/// axiom (forall s: Seq Box, i: int ::
///         { DtRank($Unbox(Seq#Index(s, i)): DatatypeType) }
///         0 <= i && i < Seq#Length(s) ==> DtRank($Unbox(Seq#Index(s, i)): DatatypeType) < Seq#Rank(s) );

private let element_ranks_less_fact =
  forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_rank (seq_index s i)}
    i < seq_length s ==> seq_rank (seq_index s i) << seq_rank s

private let element_ranks_less_lemma () : Lemma (element_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat). i < seq_length s ==> seq_rank (seq_index s i) << seq_rank s
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_rank ty;
      reveal_seq_rank (seq ty);
      reveal_seq_index ty;
      reveal_seq_contains ty;
      contains_iff_exists_index_lemma ();
      assert (seq_contains s (seq_index s i));
      memP_precedes (seq_index s i) s
    )

/// We represent the following Dafny axiom with `drop_ranks_less_fact`.
///
/// axiom (forall<T> s: Seq T, i: int ::
///         { Seq#Rank(Seq#Drop(s, i)) }
///         0 < i && i <= Seq#Length(s) ==> Seq#Rank(Seq#Drop(s, i)) < Seq#Rank(s) );

private let drop_ranks_less_fact =
  forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_rank (seq_drop s i)}
    0 < i && i <= seq_length s ==> seq_rank (seq_drop s i) << seq_rank s

private let rec drop_ranks_less_helper (ty: Type) (s: list ty) (i: nat)
  : Lemma (requires 0 < i && i <= length s)
          (ensures  seq_drop_fn s i << s) =
  match s with
  | [] -> ()
  | hd :: tl -> if i = 1 then () else drop_ranks_less_helper ty tl (i - 1)

private let drop_ranks_less_lemma () : Lemma (drop_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat).
              0 < i && i <= seq_length s ==> seq_rank (seq_drop s i) << seq_rank s
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_drop ty;
      reveal_seq_rank (seq ty);
      reveal_seq_length ty;
      drop_ranks_less_helper ty s i
    )

/// We represent the following Dafny axiom with
/// `take_ranks_less_fact`.  However, since it isn't true in F* (which
/// has strong requirements for <<), we instead substitute seq_length,
/// requiring decreases clauses to use seq_length in this case.
///
/// axiom (forall<T> s: Seq T, i: int ::
///         { Seq#Rank(Seq#Take(s, i)) }
///         0 <= i && i < Seq#Length(s) ==> Seq#Rank(Seq#Take(s, i)) < Seq#Rank(s) );

private let take_ranks_less_fact =
  forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_length (seq_take s i)}
    i < seq_length s ==> seq_length (seq_take s i) << seq_length s

private let take_ranks_less_lemma () : Lemma (take_ranks_less_fact) =
  introduce forall (ty: Type) (s: seq ty) (i: nat).
              i < seq_length s ==> seq_length (seq_take s i) << seq_length s
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_take ty;
      reveal_seq_length ty;
      take_length_lemma ()
    )

/// We represent the following Dafny axiom with
/// `append_take_drop_ranks_less_fact`.  However, since it isn't true
/// in F* (which has strong requirements for <<), we instead
/// substitute seq_length, requiring decreases clauses to use
/// seq_length in this case.
///
/// axiom (forall<T> s: Seq T, i: int, j: int ::
///         { Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) }
///         0 <= i && i < j && j <= Seq#Length(s) ==>
///         Seq#Rank(Seq#Append(Seq#Take(s, i), Seq#Drop(s, j))) < Seq#Rank(s) );

private let append_take_drop_ranks_less_fact =
  forall (ty: Type) (s: seq ty) (i: nat) (j: nat).{:pattern seq_length (seq_append (seq_take s i) (seq_drop s j))}
    i < j && j <= seq_length s ==> seq_length (seq_append (seq_take s i) (seq_drop s j)) << seq_length s

private let append_take_drop_ranks_less_lemma () : Lemma (append_take_drop_ranks_less_fact) =
  introduce
    forall (ty: Type) (s: seq ty) (i: nat) (j: nat).
      i < j && j <= seq_length s ==> seq_length (seq_append (seq_take s i) (seq_drop s j)) << seq_length s
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_length ty;
      reveal_seq_take ty;
      reveal_seq_drop ty;
      reveal_seq_length ty;
      take_length_lemma ();
      drop_length_lemma ();
      append_sums_lengths_lemma ()
    )

/// We represent the following Dafny axiom with `drop_zero_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Drop(s, n) }
///         n == 0 ==> Seq#Drop(s, n) == s);

private let drop_zero_fact =
  forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_drop s n}
    n = 0 ==> seq_drop s n == s

private let drop_zero_lemma () : Lemma (drop_zero_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat). n = 0 ==> seq_drop s n == s
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_drop ty
    )

/// We represent the following Dafny axiom with `take_zero_fact`.
///
/// axiom (forall<T> s: Seq T, n: int :: { Seq#Take(s, n) }
///         n == 0 ==> Seq#Take(s, n) == Seq#Empty());

private let take_zero_fact =
  forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_take s n}
    n = 0 ==> seq_take s n == seq_empty ty

private let take_zero_lemma () : Lemma (take_zero_fact) =
  introduce forall (ty: Type) (s: seq ty) (n: nat). n = 0 ==> seq_take s n == seq_empty ty
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_take ty;
      reveal_seq_empty ty
    )

/// We represent the following Dafny axiom with `drop_then_drop_fact`.
///
/// axiom (forall<T> s: Seq T, m, n: int :: { Seq#Drop(Seq#Drop(s, m), n) }
///         0 <= m && 0 <= n && m+n <= Seq#Length(s) ==>
///         Seq#Drop(Seq#Drop(s, m), n) == Seq#Drop(s, m+n));

private let drop_then_drop_fact (_: squash drop_length_fact) =
  forall (ty: Type) (s: seq ty) (m: nat) (n: nat).{:pattern seq_drop (seq_drop s m) n}
    m + n <= seq_length s ==> seq_drop (seq_drop s m) n == seq_drop s (m + n)

private let rec drop_then_drop_helper (#ty: Type) (s: seq ty) (m: nat) (n: nat)
  : Lemma (requires m + n <= length s /\ length (seq_drop_fn s m) = length s - m)
          (ensures  seq_drop_fn (seq_drop_fn s m) n == seq_drop_fn s (m + n)) =
  match s with
  | [] -> ()
  | hd :: tl -> if m = 0 then () else drop_then_drop_helper tl (m - 1) n

private let drop_then_drop_lemma () : Lemma (requires drop_length_fact) (ensures drop_then_drop_fact ()) =
  introduce forall (ty: Type) (s: seq ty) (m: nat) (n: nat).
              m + n <= seq_length s ==> seq_drop (seq_drop s m) n == seq_drop s (m + n)
  with
    introduce _ ==> _
    with given_antecedent. (
      reveal_seq_drop ty;
      reveal_seq_length ty;
      assert (seq_length (seq_drop s m) = seq_length s - m); // triggers drop_length_fact
      drop_then_drop_helper s m n
    )

/// The predicate `all_dafny_seq_facts` collects all the Dafny sequence axioms.
/// You can bring them into scope by invoking `all_dafny_seq_facts_lemma`.

private let all_dafny_seq_facts =
    length_of_empty_is_zero_fact
  /\ length_zero_implies_empty_fact
  /\ singleton_length_one_fact
  /\ build_increments_length_fact
  /\ index_into_build_fact ()
  /\ append_sums_lengths_fact
  /\ index_into_singleton_fact ()
  /\ index_after_append_fact ()
  /\ update_maintains_length_fact
  /\ update_then_index_fact
  /\ contains_iff_exists_index_fact
  /\ empty_doesnt_contain_anything_fact
  /\ build_contains_equiv_fact
  /\ take_contains_equiv_exists_fact
  /\ drop_contains_equiv_exists_fact
  /\ seq_equal_def_fact
  /\ seq_extensionality_fact
  /\ seq_is_prefix_def_fact
  /\ take_length_fact
  /\ index_into_take_fact ()
  /\ drop_length_fact
  /\ index_into_drop_fact ()
  /\ drop_index_offset_fact ()
  /\ append_then_take_or_drop_fact ()
  /\ take_commutes_with_in_range_update_fact ()
  /\ take_ignores_out_of_range_update_fact ()
  /\ drop_commutes_with_in_range_update_fact ()
  /\ drop_ignores_out_of_range_update_fact ()
  /\ drop_commutes_with_build_fact ()
  /\ seq_rank_def_fact
  /\ element_ranks_less_fact
  /\ drop_ranks_less_fact
  /\ take_ranks_less_fact
  /\ append_take_drop_ranks_less_fact
  /\ drop_zero_fact
  /\ take_zero_fact
  /\ drop_then_drop_fact ()

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
