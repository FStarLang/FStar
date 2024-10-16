(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStar.BitVector

/// This module defines a bit vector as a sequence of booleans of a
/// given length, and provides various utilities.
///
/// NOTE: THE TYPE [bv_t] DEFINED IS UNRELATED TO THE SMT SOLVER'S
/// THEORY OF BIT VECTORS. SEE [FStar.BV] FOR THAT.
///
/// TODO: We might rename this module to FStar.Seq.Boolean?

open FStar.Mul
open FStar.Seq

(** [logand] defined in terms of its indexing behavior *)
let rec logand_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logand_vec #n a b) i = (index a i && index b i))
      [SMTPat (index (logand_vec #n a b) i)] =
  if i = 0 then () else logand_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

(** [logxor] defined in terms of its indexing behavior *)
let rec logxor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logxor_vec #n a b) i = (index a i <> index b i))
      [SMTPat (index (logxor_vec #n a b) i)] =
  if i = 0 then () else logxor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)


(** [logor] defined in terms of its indexing behavior *)
let rec logor_vec_definition (#n: pos) (a b: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (logor_vec #n a b) i = (index a i || index b i))
      [SMTPat (index (logor_vec #n a b) i)] =
  if i = 0 then () else logor_vec_definition #(n - 1) (slice a 1 n) (slice b 1 n) (i - 1)

(** [lognot] defined in terms of its indexing behavior *)
let rec lognot_vec_definition (#n: pos) (a: bv_t n) (i: nat{i < n})
    : Lemma (ensures index (lognot_vec #n a) i = not (index a i))
      [SMTPat (index (lognot_vec #n a) i)] =
  if i = 0 then () else lognot_vec_definition #(n - 1) (slice a 1 n) (i - 1)

(* Bitwise lemmas *)

(** If both [x] and [y] are false at a given index [i], then so is they logical xor at [i] *)
let lemma_xor_bounded (m: pos) (n: nat) (x y: bv_t m)
    : Lemma
      (requires
        (forall (i: nat).
            (i < m /\ i >= n) ==>
            (Seq.index x (m - 1 - i) = false /\ Seq.index y (m - 1 - i) = false)))
      (ensures
        (forall (i: nat). (i < m /\ i >= n) ==> (Seq.index (logxor_vec x y) (m - 1 - i) = false))) =
  ()

(** Proves that the subset property is conserved in subslices. *)
let lemma_slice_subset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_subset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_subset_vec #(j - i) (slice a i j) (slice b i j))) = ()

(** Proves that the superset property is conserved in subslices. *)
let lemma_slice_superset_vec (#n: pos) (a b: bv_t n) (i: nat) (j: nat{i < j && j <= n})
    : Lemma (requires is_superset_vec a b)
      (ensures
        (match n with
          | 1 -> True
          | _ -> is_superset_vec #(j - i) (slice a i j) (slice b i j))) = ()

(**** Shift operators *)

(** The fill bits of a shift left are zero *)
let shift_left_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = false)
      [SMTPat (index (shift_left_vec #n a s) i)] = ()

(** Relating the indexes of the shifted vector to the original *)
let shift_left_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < n - s})
    : Lemma (ensures index (shift_left_vec #n a s) i = index a (i + s))
      [SMTPat (index (shift_left_vec #n a s) i)] = ()

(** The fill bits of a shift right are zero *)
let shift_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_right_vec #n a s) i = false)
      [SMTPat (index (shift_right_vec #n a s) i)] = ()

(** Relating the indexes of the shifted vector to the original *)
let shift_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_right_vec #n a s) i)] = ()

(** Arithmetic shift right of [a], interpreting position [0] as the
    most-significant bit, and using its value to fill *)
(** The fill bits of arithmetic shift right is the value of its
    most-significant bit (position zero) *)
let shift_arithmetic_right_vec_lemma_1 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i < s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a 0)
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)] = ()

(** Relating the indexes of the shifted vector to the original *)
let shift_arithmetic_right_vec_lemma_2 (#n: pos) (a: bv_t n) (s: nat) (i: nat{i < n && i >= s})
    : Lemma (ensures index (shift_arithmetic_right_vec #n a s) i = index a (i - s))
      [SMTPat (index (shift_arithmetic_right_vec #n a s) i)] = ()

