(*
   Copyright 2008-2019 Microsoft Research

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
module Steel.SizeT

(**** THIS MODULE IS GENETATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

val n: (n:nat{n % 8 = 0 /\ n >= 8})

/// For FStar.UIntN.fstp: anything that you fix/update here should be
/// reflected in [FStar.IntN.fstp], which is mostly a copy-paste of
/// this module.
///
/// Except, as compared to [FStar.IntN.fstp], here:
///  - every occurrence of [int_t] has been replaced with [uint_t]
///  - every occurrence of [@%] has been replaced with [%].
///  - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers

/// This module provides an abstract type for machine integers of a
/// given signedness and width. The interface is designed to be safe
/// with respect to arithmetic underflow and overflow.

/// Note, we have attempted several times to re-design this module to
/// make it more amenable to normalization and to impose less overhead
/// on the SMT solver when reasoning about machine integer
/// arithmetic. The following github issue reports on the current
/// status of that work.
///
/// https://github.com/FStarLang/FStar/issues/1757

open FStar.UInt
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

(** Abstract type of machine integers, with an underlying
    representation using a bounded mathematical integer *)
new val t : eqtype

(** A coercion that projects a bounded mathematical integer from a
    machine integer *)
val v (x:t) : Tot (uint_t n)


(** A coercion that injects a bounded mathematical integers into a
    machine integer *)
val uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x))

(** Injection/projection inverse *)
val uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)]

(** Projection/injection inverse *)
val vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)]

(** An alternate form of the injectivity of the [v] projection *)
val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))

(**** Addition primitives *)

(** Bounds-respecting addition

    The precondition enforces that the sum does not overflow,
    expressing the bound as an addition on mathematical integers *)
val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))

(** Addition modulo [2^n]

    Machine integers can always be added, but the postcondition is now
    in terms of addition modulo [2^n] on mathematical integers *)
val add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))

(**** SizeT specific injections *)

val max_size_t: t

val max_size_lemma (x: t) : Lemma (v x <= v max_size_t)

val at_least_16 : (b:bool{b ==> n >= 16})

val at_least_32 : (b:bool{b ==> n >= 32})

val at_least_64 : (b:bool{b ==> n >= 64})

val of_uint16 (x: FStar.UInt16.t{at_least_16}) : Tot (y:t{v y = FStar.UInt16.v x})

val of_uint32 (x: FStar.UInt32.t{at_least_32}) : Tot (y:t{v y = FStar.UInt32.v x})

val of_uint64 (x: FStar.UInt64.t{at_least_64}) : Tot (y:t{v y = FStar.UInt64.v x})

let rec incr
  (x: t)
  (a: Seq.seq t{fits (Seq.length a) n})
    : Tot unit (decreases (Seq.length a - v x))
  =
  Math.Lemmas.pow2_le_compat n 8;
  if v x >= Seq.length a then ()
  else incr (x `add` (uint_to_t 1)) a
