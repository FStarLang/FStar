(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: N. Swamy
*)
module FStar.Sequence.Permutation
open FStar.Sequence
open FStar.Sequence.Util
module S = FStar.Sequence
(* This module defines a permutation on sequences as a bijection among
   the sequence indices relating equal elements.

   It defines a few utilities to work with such permutations.

   Notably:

   1. Given two sequence with equal element counts, it constructs a
      permutation.

   2. Folding the multiplication of a commutative monoid over a
      sequence and its permutation produces the same result
*)

(* A bounded natural number *)
let nat_at_most (n:nat) = m:nat { m < n }

(* A function from the indices of `s` to itself *)
let index_fun #a (s:seq a) = nat_at_most (S.length s) -> nat_at_most (S.length s)

(* An abstract predicate defining when an index_fun is a permutation *)
val is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) : prop

(* Revealing the interpretation of is_permutation *)
val reveal_is_permutation (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>
           (* lengths of the sequences are the same *)
           S.length s0 == S.length s1 /\
           (* f is injective *)
           (forall x y. {:pattern f x; f y}
             x <> y ==> f x <> f y) /\
           (* and f relates equal items in s0 and s1 *)
           (forall (i:nat{i < S.length s0}).{:pattern (S.index s1 (f i))}
              S.index s0 i == S.index s1 (f i)))

(* A seqperm is an index_fun that is also a permutation *)
let seqperm (#a:Type) (s0:seq a) (s1:seq a) =
  f:index_fun s0 { is_permutation s0 s1 f }

(* We can construct a permutation from
//    sequences whose element counts are the same *)
val permutation_from_equal_counts
      (#a:eqtype)
      (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)

(** Now, some utilities related to commutative monoids and permutations *)

module CM = FStar.Algebra.CommMonoid

(* folding a m.mult over a sequence *)
let foldm_back (#a:Type) (m:CM.cm a) (s:seq a) = fold_back m.mult s m.unit

(* folding m over the concatenation of s1 and s2
   can be decomposed into a fold over s1 and a fold over s2 *)
val foldm_back_append (#a:Type) (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == m.mult (foldm_back m s1) (foldm_back m s2))

(* folds over concatenated lists can is symmetric *)
val foldm_back_sym (#a:Type) (m:CM.cm a) (s1 s2: seq a)
  : Lemma
    (ensures foldm_back m (append s1 s2) == foldm_back m (append s2 s1))

(* And, finally, if s0 and s1 are permutations,
   then folding m over them is identical *)
val foldm_back_perm (#a:_)
               (m:CM.cm a)
               (s0:seq a)
               (s1:seq a)
               (p:seqperm s0 s1)
  : Lemma
    (ensures foldm_back m s0  == foldm_back m s1)
