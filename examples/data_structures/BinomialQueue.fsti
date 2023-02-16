(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi
*)

module BinomialQueue

/// This module provides an implementation for mergable priority queues
///   using binomial queues.
///
/// See https://www.cs.princeton.edu/~appel/BQ.pdf
///   for background on binomial queues.
///
/// The module provides functional correctness specifications for
///   the priority queue operations using a multiset as the logical
///   representation.
///
/// See the following for a Coq outline for the same:
///   https://softwarefoundations.cis.upenn.edu/vfa-current/Binom.html

module S = FStar.Set


/// Fixing the key type to nat,
///   should be possible to parameterize over it and a comparison function

type key_t = nat

/// The priority queue interface

val priq       : Type0
val empty      : priq
val insert     : key_t -> priq -> priq
val delete_max : priq -> option (key_t & priq)
val merge      : priq -> priq -> priq


/// The multiset type and associated functioms

noeq
type ms = {
  ms_count : key_t -> nat;
  ms_elems : S.set key_t;
}

let ms_empty : ms = {
  ms_count = (fun _ -> 0);
  ms_elems = S.empty;
}

let ms_singleton (x:key_t) : ms = {
  ms_count = (fun x' -> if x' = x then 1 else 0);
  ms_elems = S.singleton x;
}

let ms_append (ms1 ms2:ms) : ms = {
  ms_count = (fun x -> ms1.ms_count x + ms2.ms_count x);
  ms_elems = S.union ms1.ms_elems ms2.ms_elems;
}

let ms_cons (x:key_t) (ms:ms) =
  ms_append (ms_singleton x) ms

/// ms1 and ms2 are in the permutation relation if:
///   - their element sets are equal
///   - their count functions are pointwise equal

let permutation (ms1 ms2:ms) =
  S.equal ms1.ms_elems ms2.ms_elems /\
  (forall (x:key_t).{:pattern ms1.ms_count x \/ ms2.ms_count x}
               ms1.ms_count x == ms2.ms_count x)

/// The representation logical predicate

val repr (q:priq) (s:ms) : prop

/// Functional correctness spec for priority queue operations

val empty_repr (_:unit) : Lemma (empty `repr` ms_empty)

val insert_repr (x:key_t) (q:priq) (s:ms)
  : Lemma (requires q `repr` s)
          (ensures insert x q `repr` (ms_cons x s))

val merge_repr (p q:priq) (sp sq:ms)
  : Lemma (requires p `repr` sp /\ q `repr` sq)
          (ensures merge p q `repr` ms_append sp sq)

val delete_max_none_repr (p:priq)
  : Lemma (delete_max p == None <==> p `repr` ms_empty)

val delete_max_some_repr (p:priq) (sp:ms)
  (k:key_t) (q:priq) (sq:ms)
  : Lemma (requires
             p `repr` sp /\
             delete_max p == Some (k, q) /\
             q `repr` sq)
          (ensures
             permutation sp (ms_cons k sq) /\
             (forall (x:key_t). S.mem x sq.ms_elems ==> x <= k))
