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
This module includes tests of sequence proprties.

@summary Tests sequence properties
*)
module Tests

open FStar.Sequence

(** test1 asserts various statements that trivially follow from the ambient sequence facts **)
private let test1 () : Lemma (True) =
  assert (seq_length (seq_empty #int) == 0);
  assert (forall (s: seq bool). seq_length s == 0 ==> s == seq_empty);
  assert (forall (v: list int). seq_length (seq_singleton v) == 1);
  assert (forall (s: seq int) (v: int). seq_length (seq_build s v) == 1 + seq_length s);
  assert (forall (v: nat). seq_index (seq_singleton v) 0 == v);
  assert (~(seq_contains seq_empty 42));
  assert (forall (s: seq int). seq_take s 0 == seq_empty);
  assert (forall (s: seq int). seq_drop s 0 == s);
  ()

(** test2 builds a sequence [1; 2; 3; 4; 5] and asserts various properties about it **)
private let test2 () : Lemma (True) =
  let s1 = nil $:: 1 in
  let s2 = s1 $:: 2 in
  let s3 = s2 $:: 3 in
  let s4 = s3 $:: 4 in
  let s5 = s4 $:: 5 in
  assert (seq_length s2 = 1 + seq_length s1);
  assert (seq_length s2 = 2);
  assert (seq_length s5 = 5);
  assert (s5 $@ 1 == 2);
  assert (forall (s: seq int) (n: nat). n < 2 ==> (s2 $+ s) $@ n = s2 $@ n);
  assert (seq_drop (seq_drop s5 1) 2 == seq_drop s5 3);
  assert (forall (v: int). seq_length (s5 $:: v) = 6);
  assert (s3 $<= s5);
  assert (seq_length (seq_update s5 3 7) == 5);
  assert ((seq_update s5 3 7) $@ 2 == 3);
  assert ((seq_update s5 3 7) $@ 3 == 7);
  assert (seq_length (seq_slice s5 1 3) == 2)

(** test3 establishes that appending a take and a drop with the same index produces the same sequence **)
private let test3 (s: seq int) (n: nat{n <= seq_length s})
  : Lemma (s $== ((seq_take s n) $+ (seq_drop s n))) =
  ()

(** test4 tests the use of seq_rank to establish a decreases clause **)
private let rec test4 (s: seq int) : Tot int (decreases seq_rank s) =
  if seq_length s = 0 then
    0
  else
    1 + test4 (seq_drop s 1)

(** test5 tests the use of seq_length to establish a decreases clause in a case where seq_rank won't work **)
private let rec test5 (s: seq int) : Tot int (decreases seq_length s) =
  if seq_length s = 0 then
    0
  else
    1 + test5 (seq_take s (seq_length s - 1))

(** test6 simply asserts all the ambient sequence facts **)
private let test6 () : Lemma (True) =
  assert (forall (ty: Type).{:pattern seq_empty #ty} seq_length (seq_empty #ty) = 0);
  assert (forall (ty: Type) (s: seq ty).{:pattern seq_length s} seq_length s = 0 ==> s == seq_empty);
  assert (forall (ty: Type) (v: ty).{:pattern seq_length (seq_singleton v)} seq_length (seq_singleton v) = 1);
  assert (forall (ty: Type) (s: seq ty) (v: ty).{:pattern seq_build s v} seq_length (seq_build s v) = 1 + seq_length s);
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_length (seq_append s0 s1)}
           seq_length (seq_append s0 s1) = seq_length s0 + seq_length s1);
  assert (forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty).{:pattern seq_length (seq_update s i v)}
           seq_length (seq_update s i v) = seq_length s);
  assert (forall (ty: Type) (s: seq ty) (i: nat{i < seq_length s}) (v: ty) (n: nat{n < seq_length (seq_update s i v)})
            .{:pattern seq_index (seq_update s i v) n}
            n < seq_length s ==>
              (i = n ==> seq_index (seq_update s i v) n == v)
            /\ (i <> n ==> seq_index (seq_update s i v) n == seq_index s n));
  assert (forall (ty: Type) (s: seq ty) (x: ty).{:pattern seq_contains s x}
           seq_contains s x <==> (exists (i: nat).{:pattern seq_index s i} i < seq_length s /\ seq_index s i == x));
  assert (forall (ty: Type) (x: ty).{:pattern seq_contains seq_empty x} ~(seq_contains seq_empty x));
  assert (forall (ty: Type) (s: seq ty) (v: ty) (x: ty).{:pattern seq_contains (seq_build s v) x}
            seq_contains (seq_build s v) x <==> (v == x \/ seq_contains s x));
  assert (forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).{:pattern seq_contains (seq_take s n) x}
            seq_contains (seq_take s n) x <==>
            (exists (i: nat).{:pattern seq_index s i} i < n /\ i < seq_length s /\ seq_index s i == x));
  assert (forall (ty: Type) (s: seq ty) (n: nat{n <= seq_length s}) (x: ty).{:pattern seq_contains (seq_drop s n) x}
            seq_contains (seq_drop s n) x <==>
            (exists (i: nat).{:pattern seq_index s i} n <= i && i < seq_length s /\ seq_index s i == x));
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_equal s0 s1}
           seq_equal s0 s1 <==>
           seq_length s0 == seq_length s1 /\
             (forall j.{:pattern seq_index s0 j \/ seq_index s1 j}
                0 <= j && j < seq_length s0 ==> seq_index s0 j == seq_index s1 j));
  assert (forall (ty: Type) (a: seq ty) (b: seq ty).{:pattern seq_equal a b} seq_equal a b ==> a == b);
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern seq_is_prefix s0 s1}
            seq_is_prefix s0 s1 <==>
              seq_length s0 <= seq_length s1
            /\ (forall (j: nat).{:pattern seq_index s0 j \/ seq_index s1 j}
                 j < seq_length s0 ==> seq_index s0 j == seq_index s1 j));
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_length (seq_take s n)}
            n <= seq_length s ==> seq_length (seq_take s n) = n);
  assert (forall (ty: Type) (s: seq ty) (n: nat). {:pattern seq_length (seq_drop s n)}
            n <= seq_length s ==> seq_length (seq_drop s n) = seq_length s - n);
  assert (forall (ty: Type) (v: ty).{:pattern seq_rank v} seq_rank v == v);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_rank (seq_index s i)}
            i < seq_length s ==> seq_rank (seq_index s i) << seq_rank s);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_rank (seq_drop s i)}
            0 < i && i <= seq_length s ==> seq_rank (seq_drop s i) << seq_rank s);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern seq_length (seq_take s i)}
            i < seq_length s ==> seq_length (seq_take s i) << seq_length s);
  assert (forall (ty: Type) (s: seq ty) (i: nat) (j: nat).{:pattern seq_length (seq_append (seq_take s i) (seq_drop s j))}
            i < j && j <= seq_length s ==> seq_length (seq_append (seq_take s i) (seq_drop s j)) << seq_length s);
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_drop s n} n = 0 ==> seq_drop s n == s);
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern seq_take s n} n = 0 ==> seq_take s n == seq_empty);
  assert (forall (ty: Type) (s: seq ty) (m: nat) (n: nat).{:pattern seq_drop (seq_drop s m) n}
            m + n <= seq_length s ==> seq_drop (seq_drop s m) n == seq_drop s (m + n))
