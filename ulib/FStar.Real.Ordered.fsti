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
module FStar.Real.Ordered

/// Elementary consequences of the ordered-field axioms of
/// [FStar.Real.Dedekind]. Nothing here is assumed: this module derives the
/// everyday algebra of the reals from the small set of laws exported by the
/// construction, so that analytic developments (such as [FStar.Real.Dedekind.Sqrt])
/// can be written at a comfortable level of abstraction.

open FStar.Real.Dedekind

module Q = FStar.Rational

(**** Order *)

val lt_asym (x y:real)     : Lemma (requires lt x y) (ensures ~(lt y x))
val not_lt (x y:real)      : Lemma (~(lt x y) <==> le y x)
val le_refl (x:real)       : Lemma (le x x)
val le_trans (x y z:real)  : Lemma (requires le x y /\ le y z) (ensures le x z)
val lt_le_trans (x y z:real) : Lemma (requires lt x y /\ le y z) (ensures lt x z)
val le_lt_trans (x y z:real) : Lemma (requires le x y /\ lt y z) (ensures lt x z)
val le_antisym (x y:real)  : Lemma (requires le x y /\ le y x) (ensures x == y)

(**** Additive group *)

val add_zero_l (x:real)    : Lemma (add zero x == x)
val add_opp_l (x:real)     : Lemma (add (opp x) x == zero)
val add_cancel (x y z:real): Lemma (add x z == add y z <==> x == y)
val opp_opp (x:real)       : Lemma (opp (opp x) == x)
val opp_zero ()            : Lemma (opp zero == zero)
val opp_add (x y:real)     : Lemma (opp (add x y) == add (opp x) (opp y))
val sub_self (x:real)      : Lemma (sub x x == zero)
val sub_add (x y:real)     : Lemma (add (sub x y) y == x)
val add_sub (x y:real)     : Lemma (sub (add x y) y == x)

val lt_add_l (x y z:real)  : Lemma (lt (add z x) (add z y) <==> lt x y)
val le_add_r (x y z:real)  : Lemma (le (add x z) (add y z) <==> le x y)
val lt_sub (x y:real)      : Lemma (lt x y <==> lt zero (sub y x))
val le_sub (x y:real)      : Lemma (le x y <==> le zero (sub y x))
val lt_opp (x y:real)      : Lemma (lt (opp y) (opp x) <==> lt x y)
val lt_add_compat (a b c d:real)
  : Lemma (requires lt a b /\ le c d) (ensures lt (add a c) (add b d))

(**** Multiplication *)

val mul_zero_l (x:real)     : Lemma (mul zero x == zero)
val mul_one_l (x:real)      : Lemma (mul one x == x)
val distrib_r (x y z:real)  : Lemma (mul (add x y) z == add (mul x z) (mul y z))
val mul_opp (x y:real)      : Lemma (mul (opp x) y == opp (mul x y))
val mul_opp_r (x y:real)    : Lemma (mul x (opp y) == opp (mul x y))
val mul_sub (x y z:real)    : Lemma (mul x (sub y z) == sub (mul x y) (mul x z))
val mul_sub_r (x y z:real)  : Lemma (mul (sub x y) z == sub (mul x z) (mul y z))

val mul_pos (x y:real)
  : Lemma (requires lt zero x /\ lt zero y) (ensures lt zero (mul x y))
val mul_nonneg (x y:real)
  : Lemma (requires le zero x /\ le zero y) (ensures le zero (mul x y))
val le_mul_pos (x y z:real)
  : Lemma (requires lt zero z) (ensures le (mul x z) (mul y z) <==> le x y)
val mul_lt_compat (a b c d:real)
  : Lemma (requires le zero a /\ lt a b /\ le zero c /\ lt c d)
          (ensures  lt (mul a c) (mul b d))
val mul_le_compat (a b c d:real)
  : Lemma (requires le zero a /\ le a b /\ le zero c /\ le c d)
          (ensures  le (mul a c) (mul b d))

(**** Squares *)

val sq_nonneg (x:real)
  : Lemma (requires le zero x) (ensures le zero (mul x x))
val sq_mono (x y:real)
  : Lemma (requires le zero x /\ lt x y) (ensures lt (mul x x) (mul y y))
val sq_mono_rev (x y:real)
  : Lemma (requires le zero x /\ le zero y /\ lt (mul x x) (mul y y))
          (ensures  lt x y)
val sq_inj (x y:real)
  : Lemma (requires le zero x /\ le zero y /\ mul x x == mul y y)
          (ensures  x == y)

/// [(x+y)^2 = x^2 + 2xy + y^2]
val square_add (x y:real)
  : Lemma (mul (add x y) (add x y) == add (add (mul x x) (mul two (mul x y))) (mul y y))
/// [(x-y)^2 = x^2 - 2xy + y^2]
val square_sub (x y:real)
  : Lemma (mul (sub x y) (sub x y) == add (sub (mul x x) (mul two (mul x y))) (mul y y))

(**** Constants and inverses *)

val zero_lt_one ()  : Lemma (lt zero one)
val zero_lt_two ()  : Lemma (lt zero two)
val two_eq ()       : Lemma (two == add one one)
val one_ne_zero ()  : Lemma (one =!= zero)

val inv_pos (x:real)
  : Lemma (requires lt zero x) (ensures lt zero (inv x))
val inv_antitone (x y:real)
  : Lemma (requires lt zero x /\ lt x y) (ensures lt (inv y) (inv x))
val div_pos (x y:real)
  : Lemma (requires lt zero x /\ lt zero y) (ensures lt zero (div x y))
val mul_div (x y:real)
  : Lemma (requires y =!= zero) (ensures mul (div x y) y == x)
val div_lt_iff (x y z:real)
  : Lemma (requires lt zero z) (ensures lt (div x z) y <==> lt x (mul y z))

val of_rat_inv (q:Q.rat)
  : Lemma (requires q =!= Q.zero) (ensures inv (of_rat q) == of_rat (Q.inv q))

(**** Density of the rationals; smallness *)

/// Some rational strictly between [0] and [u].
val small_rat (u:real)
  : Ghost Q.rat (requires lt zero u)
                (ensures fun q -> Q.lt Q.zero q /\ lt zero (of_rat q) /\ lt (of_rat q) u)

/// Some real strictly between [0] and [u].
val small_pos (u:real)
  : Ghost real (requires lt zero u) (ensures fun e -> lt zero e /\ lt e u)

/// A positive real below both [u] and [v].
val small_pos2 (u v:real)
  : Ghost real (requires lt zero u /\ lt zero v)
               (ensures fun e -> lt zero e /\ lt e u /\ lt e v)
