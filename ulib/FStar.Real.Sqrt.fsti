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
module FStar.Real.Sqrt

/// Square roots on [FStar.Real.real], with **no axioms**.
///
/// Z3's theory of reals is a theory of *ordered fields*: it proves nothing
/// that needs completeness, and in particular it gives no square roots. So
/// [sqrt] cannot be obtained from the SMT solver, and historically F* simply
/// assumed it (see [FStar.Math.Sqrt]'s old [assume val sqrt0]).
///
/// Here it is instead *defined*, by transferring
/// [FStar.Real.Dedekind.Sqrt.sqrt] --- which is built as a least upper bound
/// in the Dedekind-cut construction --- across the bridge exposed by
/// [FStar.Real] ([to_dedekind] / [of_dedekind]). Every lemma below is a
/// theorem of that construction.
///
/// [sqrt] is total: on a negative argument it returns [0.0R].

open FStar.Real

val sqrt (x:real) : real

val sqrt_neg (x:real)
  : Lemma (requires x <. 0.0R) (ensures sqrt x == 0.0R)

val sqrt_nonneg (x:real)
  : Lemma (sqrt x >=. 0.0R)
          [SMTPat (sqrt x)]

/// **The defining property, proved rather than assumed.**
val sqrt_square (x:real)
  : Lemma (requires x >=. 0.0R)
          (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]

/// ... and it is the only nonnegative number with that property.
val sqrt_unique (x y:real)
  : Lemma (requires y >=. 0.0R /\ y *. y == x)
          (ensures sqrt x == y)

val sqrt_zero () : Lemma (sqrt 0.0R == 0.0R)
val sqrt_one  () : Lemma (sqrt 1.0R == 1.0R)

val sqrt_sq (x:real)
  : Lemma (requires x >=. 0.0R) (ensures sqrt (x *. x) == x)

val sqrt_positive (x:real)
  : Lemma (requires x >. 0.0R) (ensures sqrt x >. 0.0R)

val sqrt_mono (x y:real)
  : Lemma (requires x >=. 0.0R /\ x <. y) (ensures sqrt x <. sqrt y)

val sqrt_mul (x y:real)
  : Lemma (requires x >=. 0.0R /\ y >=. 0.0R)
          (ensures sqrt (x *. y) == sqrt x *. sqrt y)

val sqrt_div (x y:real)
  : Lemma (requires x >=. 0.0R /\ y >. 0.0R)
          (ensures y =!= 0.0R /\ sqrt y =!= 0.0R /\
                   sqrt (x /. y) == sqrt x /. sqrt y)

/// The classical example, now a theorem of [FStar.Real] itself: there is a
/// real number whose square is exactly [2].
val sqrt_two () : Lemma (sqrt two *. sqrt two == two /\ sqrt two >=. 0.0R)

/// Inverse square root.
let rsqrt (x:real{x >. 0.0R}) : real =
  sqrt_positive x;
  1.0R /. sqrt x
