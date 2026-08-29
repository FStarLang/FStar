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

module O = FStar.Real.Ordered
module Q = FStar.Rational
module ID = FStar.IndefiniteDescription

open FStar.Real.Dedekind

#set-options "--fuel 0 --ifuel 0 --z3rlimit 30"

(**** Generic algebra used below *)

/// [(ab)^2 = a^2 b^2].
let mul4 (a b:real)
  : Lemma (mul (mul a b) (mul a b) == mul (mul a a) (mul b b))
  = mul_assoc a b (mul a b);
    mul_comm b (mul a b);
    mul_assoc a b b;
    mul_comm b (mul b b);
    mul_assoc a (mul b b) a;
    mul_comm (mul b b) a;
    mul_assoc a a (mul b b)

let mul_cancel_l (a b c:real)
  : Lemma (requires c =!= zero /\ mul c a == mul c b) (ensures a == b)
  = mul_inv c;
    mul_assoc (inv c) c a;
    mul_assoc (inv c) c b;
    mul_comm (inv c) c;
    O.mul_one_l a;
    O.mul_one_l b

(**** The set whose supremum is the square root *)

let sqrt_setp (x y:real) : prop = le zero y /\ le (mul y y) x

let sqrt_set (x:real) : rset = sqrt_setp x

let sqrt_set_mem (x y:real)
  : Lemma (sqrt_set x y <==> (le zero y /\ le (mul y y) x))
  = ()

let sqrt_set_nonempty (x:real)
  : Lemma (requires le zero x) (ensures is_nonempty (sqrt_set x))
  = O.le_refl zero;
    mul_zero zero;
    introduce exists (y:real). sqrt_set x y with zero and ()

/// Anything in [sqrt_set x] is at most [1 + x]: if [y] exceeded [1 + x] it
/// would exceed [1], so [y * y > y > x].
let sqrt_bound_aux (x y:real)
  : Lemma (requires le zero x /\ sqrt_set x y) (ensures le y (add one x))
  = O.not_lt (add one x) y;
    introduce lt (add one x) y ==> False
    with begin
      O.zero_lt_one ();
      O.le_add_r zero one x;
      O.add_zero_l x;
      O.le_add_r zero x one;
      add_comm x one; add_comm zero one;
      O.add_zero_l one;
      O.le_lt_trans one (add one x) y;
      lt_trans zero one y;
      lt_mul_pos one y y;
      O.mul_one_l y;
      lt_trans (add one x) y (mul y y);
      O.le_lt_trans x (add one x) (mul y y);
      O.not_lt x (mul y y)
    end

let sqrt_set_bounded (x:real)
  : Lemma (requires le zero x) (ensures is_bounded_above (sqrt_set x))
  = introduce forall (y:real). sqrt_set x y ==> le y (add one x)
    with introduce _ ==> _ with sqrt_bound_aux x y;
    introduce exists (b:real). is_upper_bound (sqrt_set x) b
    with (add one x) and ()

(**** The square root *)

#push-options "--ifuel 1"
let sqrt (x:real) : real =
  if ID.strong_excluded_middle (le zero x)
  then begin
    sqrt_set_nonempty x;
    sqrt_set_bounded x;
    lub (sqrt_set x)
  end
  else zero

let sqrt_is_lub (x:real)
  : Lemma (requires le zero x) (ensures is_lub (sqrt_set x) (sqrt x))
  = sqrt_set_nonempty x; sqrt_set_bounded x

let sqrt_neg (x:real) : Lemma (requires lt x zero) (ensures sqrt x == zero)
  = lt_irrefl x; O.lt_asym x zero
#pop-options

let sqrt_nonneg (x:real) : Lemma (le zero (sqrt x))
  = O.le_refl zero;
    introduce le zero x ==> le zero (sqrt x)
    with begin
      sqrt_is_lub x;
      sqrt_set_nonempty x;
      mul_zero zero
    end;
    O.not_lt zero x;
    introduce lt x zero ==> le zero (sqrt x)
    with sqrt_neg x

(**** Small algebraic steps

   Each of these is a separate top-level lemma on purpose: proving them inline
   inside the two main arguments below made those arguments take minutes
   instead of milliseconds. *)

/// [2s + 1 > 0] when [s >= 0].
let w_pos (s:real)
  : Lemma (requires le zero s) (ensures lt zero (add (mul two s) one))
  = O.zero_lt_two ();
    O.mul_nonneg two s;
    O.zero_lt_one ();
    O.lt_add_compat zero one zero (mul two s);
    O.add_zero_l zero;
    add_comm one (mul two s)

/// [e(2s+1) == 2se + e]
let ew_eq (s e:real)
  : Lemma (mul e (add (mul two s) one) == add (mul two (mul s e)) e)
  = distrib e (mul two s) one;
    mul_one e;
    mul_comm e (mul two s);
    mul_assoc two s e

/// [e * 2s == 2se]
let ew_eq2 (s e:real) : Lemma (mul e (mul two s) == mul two (mul s e))
  = mul_comm e (mul two s); mul_assoc two s e

/// [e^2 <= e] for [0 < e <= 1].
let sq_le (e:real)
  : Lemma (requires lt zero e /\ le e one) (ensures le (mul e e) e)
  = O.le_mul_pos e one e; O.mul_one_l e

/// [(s+e)^2 <= s^2 + e(2s+1)] for [0 < e <= 1].
let expand_le (s e:real)
  : Lemma (requires lt zero e /\ le e one)
          (ensures le (mul (add s e) (add s e))
                      (add (mul s s) (mul e (add (mul two s) one))))
  = O.square_add s e;
    sq_le e;
    O.le_add_r (mul e e) e (add (mul s s) (mul two (mul s e)));
    add_comm (add (mul s s) (mul two (mul s e))) (mul e e);
    add_comm (add (mul s s) (mul two (mul s e))) e;
    add_assoc (mul s s) (mul two (mul s e)) e;
    ew_eq s e

/// [(s-e)^2 >= s^2 - 2se].
let expand_ge (s e:real)
  : Lemma (requires le zero e)
          (ensures le (sub (mul s s) (mul two (mul s e)))
                      (mul (sub s e) (sub s e)))
  = O.square_sub s e;
    O.sq_nonneg e;
    O.le_add_r zero (mul e e) (sub (mul s s) (mul two (mul s e)));
    O.add_zero_l (sub (mul s s) (mul two (mul s e)));
    add_comm (mul e e) (sub (mul s s) (mul two (mul s e)))

/// From [e < d/w] and [w > 0], conclude [ew < d].
let small_mul (e d w:real)
  : Lemma (requires lt zero w /\ lt e (div d w)) (ensures lt (mul e w) d)
  = lt_mul_pos e (div d w) w; lt_irrefl zero; O.mul_div d w

let sum_lt (a u d x:real)
  : Lemma (requires lt u d /\ x == add a d) (ensures lt (add a u) x)
  = O.lt_add_l u d a

let sub_lt (x a u:real)
  : Lemma (requires lt u (sub a x)) (ensures lt x (sub a u))
  = O.sub_add a x;
    lt_add_r u (sub a x) x;
    add_comm u x;
    O.sub_add a u;
    lt_add_r x (sub a u) u

let shift_pos (s e:real)
  : Lemma (requires lt zero e) (ensures lt s (add s e))
  = O.lt_add_l zero e s; add_zero s

let shrink (s e:real)
  : Lemma (requires lt zero e) (ensures lt (sub s e) s)
  = O.sub_add s e; O.lt_add_l zero e (sub s e); add_zero (sub s e)

(**** The two analytic steps

   Both are stated without mentioning [sqrt] or [lub]: keeping the
   least-upper-bound hypothesis out of the SMT context here is worth three
   orders of magnitude in verification time. *)

/// If [s^2 < x] then some [y > s] is still in [sqrt_set x]: take [y = s + e]
/// with [e] positive, at most [1], and below [(x - s^2)/(2s+1)]; then
/// [y^2 <= s^2 + e(2s+1) < x].
let sqrt_step_lt (x s:real)
  : Lemma (requires le zero x /\ le zero s /\ lt (mul s s) x)
          (ensures exists (y:real). le zero y /\ le (mul y y) x /\ lt s y)
  = let d = sub x (mul s s) in
    O.lt_sub (mul s s) x;
    w_pos s;
    let w = add (mul two s) one in
    O.div_pos d w;
    O.zero_lt_one ();
    let e = O.small_pos2 one (div d w) in
    expand_le s e;
    small_mul e d w;
    O.sub_add x (mul s s);
    add_comm (sub x (mul s s)) (mul s s);
    sum_lt (mul s s) (mul e w) d x;
    O.le_lt_trans (mul (add s e) (add s e)) (add (mul s s) (mul e w)) x;
    shift_pos s e;
    O.le_trans zero s (add s e);
    introduce exists (y:real). le zero y /\ le (mul y y) x /\ lt s y
    with (add s e) and ()

/// If [s^2 > x] then some [b < s] is still an upper bound of [sqrt_set x]:
/// take [b = s - e] with [e] positive, below [s], and below [(s^2 - x)/(2s)];
/// then [b^2 >= s^2 - 2se > x], so every member of the set is below [b].
let sqrt_step_gt (x s:real)
  : Lemma (requires le zero x /\ le zero s /\ lt x (mul s s))
          (ensures exists (b:real).
                     lt b s /\
                     (forall (y:real). (le zero y /\ le (mul y y) x) ==> le y b))
  = mul_zero zero;
    O.not_lt x zero;
    let d = sub (mul s s) x in
    O.lt_sub x (mul s s);
    O.zero_lt_two ();
    let w = mul two s in
    O.mul_pos two s;
    O.div_pos d w;
    let e = O.small_pos2 s (div d w) in
    small_mul e d w;
    ew_eq2 s e;
    sub_lt x (mul s s) (mul e w);
    expand_ge s e;
    O.lt_le_trans x (sub (mul s s) (mul e w)) (mul (sub s e) (sub s e));
    O.lt_sub e s;
    introduce forall (y:real). (le zero y /\ le (mul y y) x) ==> le y (sub s e)
    with introduce _ ==> _ with begin
      O.le_lt_trans (mul y y) x (mul (sub s e) (sub s e));
      O.sq_mono_rev y (sub s e)
    end;
    shrink s e;
    introduce exists (b:real).
                lt b s /\
                (forall (y:real). (le zero y /\ le (mul y y) x) ==> le y b)
    with (sub s e) and ()

(**** [sqrt x] is neither too small nor too big *)

let sqrt_not_lt (x:real)
  : Lemma (requires le zero x)
          (ensures ~(lt (mul (sqrt x) (sqrt x)) x))
  = sqrt_nonneg x;
    sqrt_is_lub x;
    introduce lt (mul (sqrt x) (sqrt x)) x ==> False
    with begin
      sqrt_step_lt x (sqrt x);
      eliminate exists (y:real). le zero y /\ le (mul y y) x /\ lt (sqrt x) y
      with begin
        sqrt_set_mem x y;
        O.le_lt_trans y (sqrt x) y;
        lt_irrefl y
      end
    end

let sqrt_not_gt (x:real)
  : Lemma (requires le zero x)
          (ensures ~(lt x (mul (sqrt x) (sqrt x))))
  = sqrt_nonneg x;
    sqrt_is_lub x;
    introduce lt x (mul (sqrt x) (sqrt x)) ==> False
    with begin
      sqrt_step_gt x (sqrt x);
      eliminate exists (b:real).
                  lt b (sqrt x) /\
                  (forall (y:real). (le zero y /\ le (mul y y) x) ==> le y b)
      with begin
        introduce forall (y:real). sqrt_set x y ==> le y b
        with introduce _ ==> _ with sqrt_set_mem x y;
        O.le_lt_trans (sqrt x) b (sqrt x);
        lt_irrefl (sqrt x)
      end
    end

(**** The defining property *)

let sqrt_square (x:real)
  : Lemma (requires le zero x) (ensures mul (sqrt x) (sqrt x) == x)
  = sqrt_not_lt x;
    sqrt_not_gt x;
    lt_total (mul (sqrt x) (sqrt x)) x

let sqrt_unique (x y:real)
  : Lemma (requires le zero y /\ mul y y == x) (ensures y == sqrt x)
  = O.sq_nonneg y;
    sqrt_square x;
    sqrt_nonneg x;
    O.sq_inj y (sqrt x)

(**** Consequences *)

let sqrt_zero () : Lemma (sqrt zero == zero)
  = O.le_refl zero; mul_zero zero; sqrt_unique zero zero

let sqrt_one () : Lemma (sqrt one == one)
  = O.zero_lt_one (); mul_one one; sqrt_unique one one

let sqrt_sq (x:real)
  : Lemma (requires le zero x) (ensures sqrt (mul x x) == x)
  = sqrt_unique (mul x x) x

let sqrt_positive (x:real)
  : Lemma (requires lt zero x) (ensures lt zero (sqrt x))
  = sqrt_nonneg x;
    O.le_refl zero;
    sqrt_square x;
    mul_zero zero;
    lt_irrefl zero

let sqrt_mono (x y:real)
  : Lemma (requires le zero x /\ lt x y) (ensures lt (sqrt x) (sqrt y))
  = O.le_lt_trans zero x y;
    sqrt_square x; sqrt_square y;
    sqrt_nonneg x; sqrt_nonneg y;
    O.sq_mono_rev (sqrt x) (sqrt y)

let sqrt_mul (x y:real)
  : Lemma (requires le zero x /\ le zero y)
          (ensures sqrt (mul x y) == mul (sqrt x) (sqrt y))
  = sqrt_nonneg x; sqrt_nonneg y;
    sqrt_square x; sqrt_square y;
    O.mul_nonneg (sqrt x) (sqrt y);
    mul4 (sqrt x) (sqrt y);
    sqrt_unique (mul x y) (mul (sqrt x) (sqrt y))

/// [(1/t)^2 == 1/(t*t)]
let inv_sq (t:real)
  : Lemma (requires lt zero t)
          (ensures mul (inv t) (inv t) == inv (mul t t))
  = lt_irrefl zero;
    O.mul_pos t t;
    mul4 t (inv t);
    mul_inv t;
    mul_one one;
    mul_inv (mul t t);
    mul_cancel_l (mul (inv t) (inv t)) (inv (mul t t)) (mul t t)

let sqrt_div (x y:real)
  : Lemma (requires le zero x /\ lt zero y)
          (ensures sqrt (div x y) == div (sqrt x) (sqrt y))
  = sqrt_positive y;
    sqrt_square x; sqrt_square y;
    sqrt_nonneg x;
    O.inv_pos (sqrt y);
    O.mul_nonneg (sqrt x) (inv (sqrt y));
    mul4 (sqrt x) (inv (sqrt y));
    inv_sq (sqrt y);
    sqrt_unique (div x y) (div (sqrt x) (sqrt y))

let sqrt_two_sq () : Lemma (mul (sqrt two) (sqrt two) == two)
  = O.zero_lt_two (); sqrt_square two
