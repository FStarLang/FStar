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
module FStar.Seq.Permutation
open FStar.Seq

(* This module defines a permutation on sequences as a bijection among
   the sequence indices relating equal elements.

   It defines a few utilities to work with such permutations.

   Notably:

   1. Given two sequence with equal element counts, it constructs a
      permutation.

   2. Folding the multiplication of a commutative monoid over a
      sequence and its permutation produces the equivalent results
*)

(* A bounded natural number *)
let nat_at_most (n:nat) = m:nat { m < n }

(* A function from the indices of `s` to itself *)
let index_fun #a (s:seq a) = nat_at_most (Seq.length s) -> nat_at_most (Seq.length s)

(* An abstract predicate defining when an index_fun is a permutation *)
val is_permutation (#a:Type) (s0:seq a) (s1:seq a) (f:index_fun s0) : prop

(* Revealing the interpretation of is_permutation *)
val reveal_is_permutation (#a:Type) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation s0 s1 f <==>
           (* lengths of the sequences are the same *)
           Seq.length s0 == Seq.length s1 /\
           (* f is injective *)
           (forall x y. {:pattern f x; f y}
             x <> y ==> f x <> f y) /\
           (* and f relates equal items in s0 and s1 *)
           (forall (i:nat{i < Seq.length s0}).{:pattern (Seq.index s1 (f i))}
              Seq.index s0 i == Seq.index s1 (f i)))

(* A seqperm is an index_fun that is also a permutation *)
let seqperm (#a:Type) (s0:seq a) (s1:seq a) =
  f:index_fun s0 { is_permutation s0 s1 f }

(* We can construct a permutation from 
   sequences whose element counts are the same *)
val permutation_from_equal_counts 
      (#a:eqtype)
      (s0:seq a) (s1:seq a{(forall x. count x s0 == count x s1)})
  : Tot (seqperm s0 s1)

(** Now, some utilities related to commutative monoids and permutations *)

module CE = FStar.Algebra.CommMonoid.Equiv

(* folding a m.mult over a sequence *)
let foldm_snoc (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s:seq a) =
  foldr_snoc m.mult s m.unit

(* folding over a sequence of units is unit *)
val foldm_snoc_unit_seq (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s:Seq.seq a)
  : Lemma (requires Seq.equal s (Seq.create (Seq.length s) m.unit))
          (ensures eq.eq (foldm_snoc m s) m.unit)

(* folding over a singleton sequence is the sequence element *)
val foldm_snoc_singleton (#a:_) (#eq:_) (m:CE.cm a eq) (x:a)
  : Lemma (eq.eq (foldm_snoc m (Seq.create 1 x)) x)

(* folding m over the concatenation of s1 and s2
   can be decomposed into a fold over s1 and a fold over s2 *)
val foldm_snoc_append (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2))
                   (m.mult (foldm_snoc m s1) (foldm_snoc m s2)))

(* folds over concatenated lists can is symmetric *)
val foldm_snoc_sym (#a:Type) (#eq:CE.equiv a) (m:CE.cm a eq) (s1 s2: seq a)
  : Lemma
    (ensures eq.eq (foldm_snoc m (append s1 s2))
                   (foldm_snoc m (append s2 s1)))

(* And, finally, if s0 and s1 are permutations, 
   then folding m over them is identical *)
val foldm_snoc_perm (#a:_) (#eq:_)
               (m:CE.cm a eq)
               (s0:seq a)
               (s1:seq a)
               (p:seqperm s0 s1)
  : Lemma
    (ensures eq.eq (foldm_snoc m s0) (foldm_snoc m s1))
