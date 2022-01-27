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
This module includes tests of sequence properties.

@summary Tests sequence properties
*)
module Tests

open FStar.Sequence
open FStar.Sequence.Util

(** test1 asserts various statements that trivially follow from the ambient sequence facts **)
private let test1 () : Lemma (True) =
  assert (length (empty #int) == 0);
  assert (forall (s: seq bool). length s == 0 ==> s == empty);
  assert (forall (v: list int). length (singleton v) == 1);
  assert (forall (s: seq int) (v: int). length (build s v) == 1 + length s);
  assert (forall (v: nat). index (singleton v) 0 == v);
  assert (~(contains empty 42));
  assert (forall (s: seq int). take s 0 == empty);
  assert (forall (s: seq int). drop s 0 == s);
  ()

(** test2 builds a sequence [1; 2; 3; 4; 5] and asserts various properties about it **)
private let test2 () : Lemma (True) =
  let s1 = empty $:: 1 in
  let s2 = s1 $:: 2 in
  let s3 = s2 $:: 3 in
  let s4 = s3 $:: 4 in
  let s5 = s4 $:: 5 in
  assert (length s2 = 1 + length s1);
  assert (length s2 = 2);
  assert (length s5 = 5);
  assert (s5 $@ 1 == 2);
  assert (forall (s: seq int) (n: nat). n < 2 ==> (s2 $+ s) $@ n = s2 $@ n);
  assert (drop (drop s5 1) 2 == drop s5 3);
  assert (forall (v: int). length (s5 $:: v) = 6);
  assert (s3 $<= s5);
  assert (length (update s5 3 7) == 5);
  assert ((update s5 3 7) $@ 2 == 3);
  assert ((update s5 3 7) $@ 3 == 7);
  assert (length (slice s5 1 3) == 2)

(** test3 establishes that appending a take and a drop with the same index produces the same sequence **)
private let test3 (s: seq int) (n: nat{n <= length s})
  : Lemma (s $== ((take s n) $+ (drop s n))) =
  ()

(** test4 tests the use of rank to establish a decreases clause **)
private let rec test4 (s: seq int) : Tot int (decreases rank s) =
  if length s = 0 then
    0
  else
    1 + test4 (drop s 1)

(** test5 tests the use of length to establish a decreases clause in a case where rank won't work **)
private let rec test5 (s: seq int) : Tot int (decreases length s) =
  if length s = 0 then
    0
  else
    1 + test5 (take s (length s - 1))

(** test6 simply asserts all the ambient sequence facts **)
private let test6 () : Lemma (True) =
  assert (forall (ty: Type).{:pattern empty #ty} length (empty #ty) = 0);
  assert (forall (ty: Type) (s: seq ty).{:pattern length s} length s = 0 ==> s == empty);
  assert (forall (ty: Type) (v: ty).{:pattern length (singleton v)} length (singleton v) = 1);
  assert (forall (ty: Type) (s: seq ty) (v: ty).{:pattern build s v} length (build s v) = 1 + length s);
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern length (append s0 s1)}
           length (append s0 s1) = length s0 + length s1);
  assert (forall (ty: Type) (s: seq ty) (i: nat{i < length s}) (v: ty).{:pattern length (update s i v)}
           length (update s i v) = length s);
  assert (forall (ty: Type) (s: seq ty) (i: nat{i < length s}) (v: ty) (n: nat{n < length (update s i v)})
            .{:pattern index (update s i v) n}
            n < length s ==>
              (i = n ==> index (update s i v) n == v)
            /\ (i <> n ==> index (update s i v) n == index s n));
  assert (forall (ty: Type) (s: seq ty) (x: ty).{:pattern contains s x}
           contains s x <==> (exists (i: nat).{:pattern index s i} i < length s /\ index s i == x));
  assert (forall (ty: Type) (x: ty).{:pattern contains empty x} ~(contains empty x));
  assert (forall (ty: Type) (s: seq ty) (v: ty) (x: ty).{:pattern contains (build s v) x}
            contains (build s v) x <==> (v == x \/ contains s x));
  assert (forall (ty: Type) (s: seq ty) (n: nat{n <= length s}) (x: ty).{:pattern contains (take s n) x}
            contains (take s n) x <==>
            (exists (i: nat).{:pattern index s i} i < n /\ i < length s /\ index s i == x));
  assert (forall (ty: Type) (s: seq ty) (n: nat{n <= length s}) (x: ty).{:pattern contains (drop s n) x}
            contains (drop s n) x <==>
            (exists (i: nat).{:pattern index s i} n <= i && i < length s /\ index s i == x));
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern equal s0 s1}
           equal s0 s1 <==>
           length s0 == length s1 /\
             (forall j.{:pattern index s0 j \/ index s1 j}
                0 <= j && j < length s0 ==> index s0 j == index s1 j));
  assert (forall (ty: Type) (a: seq ty) (b: seq ty).{:pattern equal a b} equal a b ==> a == b);
  assert (forall (ty: Type) (s0: seq ty) (s1: seq ty).{:pattern is_prefix s0 s1}
            is_prefix s0 s1 <==>
              length s0 <= length s1
            /\ (forall (j: nat).{:pattern index s0 j \/ index s1 j}
                 j < length s0 ==> index s0 j == index s1 j));
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern length (take s n)}
            n <= length s ==> length (take s n) = n);
  assert (forall (ty: Type) (s: seq ty) (n: nat). {:pattern length (drop s n)}
            n <= length s ==> length (drop s n) = length s - n);
  assert (forall (ty: Type) (v: ty).{:pattern rank v} rank v == v);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern rank (index s i)}
            i < length s ==> rank (index s i) << rank s);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern rank (drop s i)}
            0 < i && i <= length s ==> rank (drop s i) << rank s);
  assert (forall (ty: Type) (s: seq ty) (i: nat).{:pattern length (take s i)}
            i < length s ==> length (take s i) << length s);
  assert (forall (ty: Type) (s: seq ty) (i: nat) (j: nat).{:pattern length (append (take s i) (drop s j))}
            i < j && j <= length s ==> length (append (take s i) (drop s j)) << length s);
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern drop s n} n = 0 ==> drop s n == s);
  assert (forall (ty: Type) (s: seq ty) (n: nat).{:pattern take s n} n = 0 ==> take s n == empty);
  assert (forall (ty: Type) (s: seq ty) (m: nat) (n: nat).{:pattern drop (drop s m) n}
            m + n <= length s ==> drop (drop s m) n == drop s (m + n))
