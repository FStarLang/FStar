(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Rational

/// The ordered field of rational numbers, developed without any axiom.
///
/// Rationals are represented canonically (as a fraction in lowest terms with a
/// positive denominator), so F*'s propositional equality [==] on [rat] *is*
/// equality of rationals. That is what makes [rat] usable as the index type of
/// a Dedekind cut; see [FStar.Real.Dedekind].
///
/// The representation is abstract: clients reason through [num]/[den] and the
/// [mk_*] congruences, or, more usually, through the field and order laws.

module L = FStar.Math.Lemmas

/// [pmul] is multiplication of positive integers, packaged so that its
/// positivity is available without a lemma call.
val pmul (a b:pos) : c:pos{c == a * b}

val rat : eqtype

(**** Representation *)

val num : rat -> int
val den : rat -> pos

/// [mk n d] is the rational [n/d].
val mk (n:int) (d:pos) : rat

val mk_num_den (q:rat) : Lemma (mk (num q) (den q) == q) [SMTPat (mk (num q) (den q))]

val num_den_reduced (q:rat) : Lemma (num q == 0 ==> den q == 1)

/// Two rationals are equal exactly when they cross-multiply equally.
val eq_cross (p q:rat)
  : Lemma (p == q <==> num p * den q == num q * den p)

/// [mk n d] really does denote [n/d].
val mk_cross (n:int) (d:pos)
  : Lemma (num (mk n d) * d == n * den (mk n d))

val mk_eq (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mk n1 d1 == mk n2 d2 <==> n1 * d2 == n2 * d1)

(**** Embedding of the integers *)

val of_int (n:int) : rat

val of_int_num_den (n:int) : Lemma (num (of_int n) == n /\ den (of_int n) == 1)

val of_int_mk (n:int) : Lemma (of_int n == mk n 1)

let zero : rat = of_int 0
let one  : rat = of_int 1
let two  : rat = of_int 2

(**** Field operations *)

val add : rat -> rat -> rat
val neg : rat -> rat
val mul : rat -> rat -> rat

/// Total inverse; [inv zero] is [zero].
val inv : rat -> rat

let sub (p q:rat) : rat = add p (neg q)
let div (p q:rat) : rat = mul p (inv q)

(**** Order *)

val lt : rat -> rat -> bool

let le (p q:rat) : bool = lt p q || p = q
let gt (p q:rat) : bool = lt q p
let ge (p q:rat) : bool = le q p

(**** The [mk] congruences: every operation acts on representatives *)

val mk_add (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (add (mk n1 d1) (mk n2 d2) == mk (n1 * d2 + n2 * d1) (pmul d1 d2))

val mk_neg (n:int) (d:pos)
  : Lemma (neg (mk n d) == mk (-n) d)

val mk_mul (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (mul (mk n1 d1) (mk n2 d2) == mk (n1 * n2) (pmul d1 d2))

val mk_lt (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (lt (mk n1 d1) (mk n2 d2) <==> n1 * d2 < n2 * d1)

val inv_num_den (q:rat)
  : Lemma (requires q =!= zero)
          (ensures  mul q (inv q) == one)

(**** Field laws *)

val add_comm (p q:rat)     : Lemma (add p q == add q p)
val add_assoc (p q r:rat)  : Lemma (add (add p q) r == add p (add q r))
val add_zero (p:rat)       : Lemma (add p zero == p)
val add_neg (p:rat)        : Lemma (add p (neg p) == zero)
val neg_neg (p:rat)        : Lemma (neg (neg p) == p)

val mul_comm (p q:rat)     : Lemma (mul p q == mul q p)
val mul_assoc (p q r:rat)  : Lemma (mul (mul p q) r == mul p (mul q r))
val mul_one (p:rat)        : Lemma (mul p one == p)
val mul_zero (p:rat)       : Lemma (mul p zero == zero)
val mul_neg (p q:rat)      : Lemma (mul (neg p) q == neg (mul p q))

val distrib (p q r:rat)
  : Lemma (mul p (add q r) == add (mul p q) (mul p r))

val mul_eq_zero (p q:rat)
  : Lemma (mul p q == zero <==> (p == zero \/ q == zero))

(**** Order laws *)

val lt_irrefl (p:rat)     : Lemma (~(lt p p))
val lt_trans (p q r:rat)  : Lemma (requires lt p q /\ lt q r) (ensures lt p r)
val lt_total (p q:rat)    : Lemma (lt p q \/ p == q \/ lt q p)
val lt_asym (p q:rat)     : Lemma (requires lt p q) (ensures ~(lt q p))

val lt_add_r (p q r:rat)  : Lemma (lt (add p r) (add q r) <==> lt p q)
val lt_neg (p q:rat)      : Lemma (lt (neg q) (neg p) <==> lt p q)

val lt_mul_pos (p q r:rat)
  : Lemma (requires lt zero r) (ensures lt (mul p r) (mul q r) <==> lt p q)

val mul_pos (p q:rat)
  : Lemma (requires lt zero p /\ lt zero q) (ensures lt zero (mul p q))

val inv_pos (p:rat)
  : Lemma (requires lt zero p) (ensures lt zero (inv p))

(**** Integers, floor, Archimedes, density *)

val of_int_add (m n:int) : Lemma (of_int (m + n) == add (of_int m) (of_int n))
val of_int_mul (m n:int) : Lemma (of_int (m * n) == mul (of_int m) (of_int n))
val of_int_lt  (m n:int) : Lemma (lt (of_int m) (of_int n) <==> m < n)
val of_int_inj (m n:int) : Lemma (of_int m == of_int n <==> m == n)

/// The greatest integer below [q].
val floor (q:rat) : int

val floor_spec (q:rat)
  : Lemma (le (of_int (floor q)) q /\ lt q (of_int (floor q + 1)))

/// Archimedes' property, in the form used to prove completeness.
val archimedean (q:rat) : Lemma (exists (n:nat). lt q (of_int n))

/// [1/n] can be made smaller than any positive rational.
val small_inv (eps:rat)
  : Lemma (requires lt zero eps)
          (ensures  exists (n:pos). lt (mk 1 n) eps)

/// Midpoint, witnessing the density of the order.
val mid (p q:rat) : rat

val mid_spec (p q:rat)
  : Lemma (requires lt p q) (ensures lt p (mid p q) /\ lt (mid p q) q)

/// A rational strictly below [q] (used to show cuts are nonempty).
val below (q:rat) : r:rat{lt r q}

/// A rational strictly above [q].
val above (q:rat) : r:rat{lt q r}
