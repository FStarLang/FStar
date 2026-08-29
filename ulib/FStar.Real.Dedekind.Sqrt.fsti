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
module FStar.Real.Dedekind.Sqrt

/// Square roots on the Dedekind reals of [FStar.Real.Dedekind].
///
/// Nothing is assumed here. [sqrt x] is *constructed* as
///
///     sqrt x  =  lub { y | 0 <= y  /\  y * y <= x }
///
/// and [sqrt x * sqrt x == x] is *proved*, by ruling out both [<] and [>]
/// using the least-upper-bound property of the reals. This is the payoff of
/// building the reals as Dedekind cuts: completeness is a theorem of the
/// construction, so the square root is a theorem too.
///
/// [FStar.Real.Sqrt] transfers all of this to the SMT-mapped reals of
/// [FStar.Real], which is what discharges the square-root axiom that
/// [FStar.Math.Sqrt] used to need.

module R = FStar.Real.Dedekind
module O = FStar.Real.Ordered
module Q = FStar.Rational

open FStar.Real.Dedekind

(**** The set whose supremum is the square root *)

/// [sqrt_set x] is the set of nonnegative reals whose square is at most [x].
/// For [x >= 0] it is nonempty (it contains [0]) and bounded above (by
/// [1 + x]), so it has a least upper bound.
val sqrt_set (x:real) : rset

val sqrt_set_mem (x y:real)
  : Lemma (sqrt_set x y <==> (le zero y /\ le (mul y y) x))

val sqrt_set_nonempty (x:real)
  : Lemma (requires le zero x) (ensures nonempty (sqrt_set x))

val sqrt_set_bounded (x:real)
  : Lemma (requires le zero x) (ensures bounded_above (sqrt_set x))

(**** The square root *)

/// Total, with [sqrt x == zero] for negative [x].
val sqrt (x:real) : real

/// [sqrt x] is the least upper bound of [sqrt_set x].
val sqrt_is_lub (x:real)
  : Lemma (requires le zero x) (ensures is_lub (sqrt_set x) (sqrt x))

val sqrt_neg (x:real) : Lemma (requires lt x zero) (ensures sqrt x == zero)

val sqrt_nonneg (x:real) : Lemma (le zero (sqrt x))

/// **The defining property, proved rather than assumed.**
val sqrt_square (x:real)
  : Lemma (requires le zero x) (ensures mul (sqrt x) (sqrt x) == x)

/// ... and it is the only nonnegative number with that property.
val sqrt_unique (x y:real)
  : Lemma (requires le zero y /\ mul y y == x) (ensures y == sqrt x)

val sqrt_zero () : Lemma (sqrt zero == zero)
val sqrt_one  () : Lemma (sqrt one == one)

val sqrt_sq (x:real)
  : Lemma (requires le zero x) (ensures sqrt (mul x x) == x)

val sqrt_positive (x:real)
  : Lemma (requires lt zero x) (ensures lt zero (sqrt x))

val sqrt_mono (x y:real)
  : Lemma (requires le zero x /\ lt x y) (ensures lt (sqrt x) (sqrt y))

val sqrt_mul (x y:real)
  : Lemma (requires le zero x /\ le zero y)
          (ensures sqrt (mul x y) == mul (sqrt x) (sqrt y))

val sqrt_div (x y:real)
  : Lemma (requires le zero x /\ lt zero y)
          (ensures sqrt (div x y) == div (sqrt x) (sqrt y))

/// The classical example: a real number whose square is exactly [2] exists.
val sqrt_two_sq () : Lemma (mul (sqrt two) (sqrt two) == two)
