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

(** This module provides some utilities on top of FStar.Sequence *)
module FStar.Sequence.Util
open FStar.Sequence.Base


/// For convenience, we define `slice` to represent Dafny sequence slices.
let slice (#ty: Type) (s: seq ty) (i: nat) (j: nat{j >= i && j <= length s})
  : seq ty
  = all_seq_facts_lemma();
    drop (take s j) i

let cons #a (x:a) (s:seq a) = singleton x `append` s

let head #a (s:seq a{length s > 0}) = s $@ 0

let tail #a (s:seq a{length s > 0}) = drop s 1

/// Split a sequences into a prefix and the last element
/// This is the inverse of the Sequence.build
let un_build (#a:_) (s:seq a{length s > 0})
  : seq a & a
  = take s (length s - 1),
    s $@ (length s - 1)

let split #a (s:seq a) (i:nat{ i <= length s})
  : seq a & seq a
  = take s i,
    drop s i

/// Counts the number of elements of `s` that
/// satisfy the predicate [f]
let rec count_matches (#a:Type) (f:a -> bool) (s:seq a)
  : Tot nat (decreases (length s))
  = all_seq_facts_lemma();
    if length s = 0 then 0
    else if f (head s) then 1 + count_matches f (tail s)
    else count_matches f (tail s)

/// count_matches on an empty sequence is always zero
let count_matches_empty (a:Type) (f:a -> bool) (s:seq a{length s = 0})
  : Lemma (count_matches f s = 0)
  = ()

/// count is a specialization of count_matches
/// to count the number of occurrences of a given element `x` in `s`.
///
/// It is opaque to give control over its unrollings in specific proofs
[@@"opaque_to_smt"]
let count (#a:eqtype) (x:a) (s:seq a) = count_matches (fun y -> x = y) s

/// A specializtion of count_matches_empty
let count_empty (#a:eqtype) (s:seq a{length s = 0})
  : Lemma (forall x. count x s = 0)
  = reveal_opaque (`%count) (count #a)

/// The head element always occurs in a non-empty list
let count_head (#a:eqtype) (s:seq a{length s > 0})
  : Lemma (count (head s) s > 0)
  = reveal_opaque (`%count) (count #a)

/// count sums over append
let rec lemma_append_count_aux (#a:eqtype) (x:a) (lo hi:seq a)
  : Lemma
    (ensures (count x (append lo hi) = (count x lo + count x hi)))
    (decreases (length lo))
  = all_seq_facts_lemma();
    reveal_opaque (`%count) (count #a);
    if length lo = 0
    then assert (append lo hi `equal` hi)
    else (
      lemma_append_count_aux x (tail lo) hi;
      assert (append (tail lo) hi `equal` tail (append lo hi))
    )


/// Folding a function over a sequence, starting from its
/// last element, hence fold_back
let rec fold_back (#a #b:Type) (f:b -> a -> Tot a) (s:seq b) (init:a)
  : Tot a (decreases (length s))
  = all_seq_facts_lemma();
    if length s = 0 then init
    else let last  = s $@ (length s - 1) in
         let s = take s (length s - 1) in
         f last (fold_back f s init)
