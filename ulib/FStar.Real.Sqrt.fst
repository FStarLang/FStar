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

/// [sqrt x] is constructed as
///
///     sqrt x  =  lub { y | 0 <= y  /\  y * y <= x }
///
/// using nothing but the completeness of [FStar.Real] ([FStar.Real.lub]).
/// The ordered-field algebra below is discharged by Z3's theory of reals; the
/// least-upper-bound property is the part Z3 cannot do, and it comes from the
/// Dedekind-cut construction that implements [FStar.Real].

open FStar.Real
module ID = FStar.IndefiniteDescription

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** The set whose supremum is the square root *)

let sqrt_setp (x y:real) : prop = y >=. 0.0R /\ y *. y <=. x

let sqrt_set (x:real) : rset = sqrt_setp x

let sqrt_set_nonempty (x:real)
  : Lemma (requires x >=. 0.0R) (ensures nonempty (sqrt_set x))
  = introduce exists (y:real). sqrt_set x y with 0.0R and ()

/// Anything in [sqrt_set x] is at most [1 + x]: if [y] exceeded [1 + x] it
/// would exceed [1], so [y * y > y > x].
let sqrt_bound_aux (x y:real)
  : Lemma (requires x >=. 0.0R /\ sqrt_set x y) (ensures y <=. 1.0R +. x)
  = introduce 1.0R +. x <. y ==> False
    with begin
      assert (1.0R <. y);
      assert (y *. y >. y *. 1.0R)
    end

let sqrt_set_bounded (x:real)
  : Lemma (requires x >=. 0.0R) (ensures bounded_above (sqrt_set x))
  = introduce forall (y:real). sqrt_set x y ==> y <=. 1.0R +. x
    with introduce _ ==> _ with sqrt_bound_aux x y;
    introduce exists (b:real). upper_bound (sqrt_set x) b with (1.0R +. x) and ()

(**** The square root *)

#push-options "--ifuel 1"
let sqrt (x:real) : real =
  if ID.strong_excluded_middle (x >=. 0.0R)
  then begin
    sqrt_set_nonempty x;
    sqrt_set_bounded x;
    lub (sqrt_set x)
  end
  else 0.0R

let sqrt_is_lub (x:real)
  : Lemma (requires x >=. 0.0R) (ensures is_lub (sqrt_set x) (sqrt x))
  = sqrt_set_nonempty x; sqrt_set_bounded x

let sqrt_neg (x:real)
  : Lemma (requires x <. 0.0R) (ensures sqrt x == 0.0R)
  = ()
#pop-options

let sqrt_nonneg (x:real)
  : Lemma (sqrt x >=. 0.0R)
          [SMTPat (sqrt x)]
  = introduce x >=. 0.0R ==> sqrt x >=. 0.0R
    with begin
      sqrt_is_lub x;
      sqrt_set_nonempty x;
      assert (sqrt_set x 0.0R)
    end;
    introduce x <. 0.0R ==> sqrt x >=. 0.0R with sqrt_neg x

(**** The two analytic steps

   Both are stated without mentioning [sqrt] or [lub]: keeping the
   least-upper-bound hypothesis out of the SMT context is worth orders of
   magnitude in verification time. *)

/// Some [e] with [0 < e <= a] and [e < b].
let small_pos2 (a b:real)
  : Ghost real (requires a >. 0.0R /\ b >. 0.0R)
               (ensures fun e -> e >. 0.0R /\ e <=. a /\ e <. b)
  = if a <. b then a else b /. two

/// From [e < d/w] and [w > 0], conclude [e * w < d].
let small_mul (e d w:real)
  : Lemma (requires w >. 0.0R /\ e <. d /. w) (ensures e *. w <. d)
  = assert (e *. w <. (d /. w) *. w);
    assert ((d /. w) *. w == d)

/// If [s^2 < x] then some [y > s] is still in [sqrt_set x]: take [y = s + e]
/// with [e] positive, at most [1], and below [(x - s^2)/(2s+1)]; then
/// [y^2 <= s^2 + e(2s+1) < x].
let sqrt_step_lt (x s:real)
  : Lemma (requires x >=. 0.0R /\ s >=. 0.0R /\ s *. s <. x)
          (ensures exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ s <. y)
  = let d = x -. s *. s in
    let w = two *. s +. 1.0R in
    assert (w >. 0.0R);
    assert (d /. w >. 0.0R);
    let e = small_pos2 1.0R (d /. w) in
    small_mul e d w;
    let y = s +. e in
    assert (e *. e <=. e *. 1.0R);
    assert (y *. y == s *. s +. (two *. s *. e +. e *. e));
    assert (e *. w == two *. s *. e +. e);
    assert (y *. y <=. s *. s +. e *. w);
    introduce exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ s <. y
    with y and ()

/// If [s^2 > x] then some [b < s] is still an upper bound of [sqrt_set x]:
/// take [b = s - e] with [e] positive, below [s], and below [(s^2 - x)/(2s)];
/// then [b^2 >= s^2 - 2se > x], so every member of the set is below [b].
let sqrt_step_gt (x s:real)
  : Lemma (requires x >=. 0.0R /\ s >=. 0.0R /\ x <. s *. s)
          (ensures exists (b:real).
                     b <. s /\
                     (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b))
  = assert (s >. 0.0R);
    let d = s *. s -. x in
    let w = two *. s in
    assert (w >. 0.0R);
    assert (d /. w >. 0.0R);
    let e = small_pos2 s (d /. w) in
    small_mul e d w;
    let b = s -. e in
    assert (b >=. 0.0R);
    assert (e *. w == two *. s *. e);
    assert (b *. b == s *. s -. two *. s *. e +. e *. e);
    assert (b *. b >. x);
    introduce forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b
    with introduce (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b with begin
      introduce b <. y ==> False
      with assert (y *. y >. b *. b)
    end;
    introduce exists (b:real).
                b <. s /\
                (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b)
    with b and ()

(**** [sqrt x] is neither too small nor too big *)

let sqrt_not_lt (x:real)
  : Lemma (requires x >=. 0.0R) (ensures ~(sqrt x *. sqrt x <. x))
  = sqrt_nonneg x;
    sqrt_is_lub x;
    introduce sqrt x *. sqrt x <. x ==> False
    with begin
      sqrt_step_lt x (sqrt x);
      eliminate exists (y:real). y >=. 0.0R /\ y *. y <=. x /\ sqrt x <. y
      with assert (sqrt_set x y)
    end

let sqrt_not_gt (x:real)
  : Lemma (requires x >=. 0.0R) (ensures ~(x <. sqrt x *. sqrt x))
  = sqrt_nonneg x;
    sqrt_is_lub x;
    introduce x <. sqrt x *. sqrt x ==> False
    with begin
      sqrt_step_gt x (sqrt x);
      eliminate exists (b:real).
                  b <. sqrt x /\
                  (forall (y:real). (y >=. 0.0R /\ y *. y <=. x) ==> y <=. b)
      with begin
        introduce forall (y:real). sqrt_set x y ==> y <=. b
        with introduce sqrt_set x y ==> y <=. b with assert (sqrt_setp x y);
        assert (upper_bound (sqrt_set x) b)
      end
    end

(**** The defining property *)

let sqrt_square (x:real)
  : Lemma (requires x >=. 0.0R)
          (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]
  = sqrt_not_lt x; sqrt_not_gt x

/// Squaring is strictly monotone on the nonnegatives. Stated separately: in
/// the middle of the arguments below the SMT context is large enough that
/// this nonlinear step times out.
let sq_lt (a b:real)
  : Lemma (requires a >=. 0.0R /\ a <. b) (ensures a *. a <. b *. b)
  = assert (a *. a <=. a *. b)

let sq_le (a b:real)
  : Lemma (requires a >=. 0.0R /\ a <=. b) (ensures a *. a <=. b *. b)
  = assert (a *. a <=. a *. b)

let sqrt_unique (x y:real)
  : Lemma (requires y >=. 0.0R /\ y *. y == x)
          (ensures sqrt x == y)
  = sqrt_square x;
    sqrt_nonneg x;
    introduce y <. sqrt x ==> False with sq_lt y (sqrt x);
    introduce sqrt x <. y ==> False with sq_lt (sqrt x) y

(**** Consequences *)

let sqrt_zero () : Lemma (sqrt 0.0R == 0.0R) = sqrt_unique 0.0R 0.0R
let sqrt_one  () : Lemma (sqrt 1.0R == 1.0R) = sqrt_unique 1.0R 1.0R

let sqrt_sq (x:real)
  : Lemma (requires x >=. 0.0R) (ensures sqrt (x *. x) == x)
  = sqrt_unique (x *. x) x

let sqrt_positive (x:real)
  : Lemma (requires x >. 0.0R) (ensures sqrt x >. 0.0R)
  = sqrt_nonneg x; sqrt_square x

let sqrt_mono (x y:real)
  : Lemma (requires x >=. 0.0R /\ x <. y) (ensures sqrt x <. sqrt y)
  = sqrt_nonneg x; sqrt_nonneg y;
    sqrt_square x; sqrt_square y;
    introduce sqrt y <=. sqrt x ==> False with sq_le (sqrt y) (sqrt x)

let mul_nonneg (a b:real)
  : Lemma (requires a >=. 0.0R /\ b >=. 0.0R) (ensures a *. b >=. 0.0R)
  = ()

let div_nonneg (a b:real)
  : Lemma (requires a >=. 0.0R /\ b >. 0.0R) (ensures b =!= 0.0R /\ a /. b >=. 0.0R)
  = ()

/// [(ab)^2 == a^2 b^2] and [(a/b)^2 == a^2/b^2], hoisted for the same reason.
let mul4 (a b:real) : Lemma ((a *. b) *. (a *. b) == (a *. a) *. (b *. b)) = ()

let div4 (a b:real)
  : Lemma (requires b =!= 0.0R)
          (ensures b *. b =!= 0.0R /\
                   (a /. b) *. (a /. b) == (a *. a) /. (b *. b))
  = assert (b *. b =!= 0.0R);
    assert ((a /. b) *. (a /. b) *. (b *. b) == a *. a)

let sqrt_mul (x y:real)
  : Lemma (requires x >=. 0.0R /\ y >=. 0.0R)
          (ensures sqrt (x *. y) == sqrt x *. sqrt y)
  = sqrt_nonneg x; sqrt_nonneg y;
    sqrt_square x; sqrt_square y;
    mul_nonneg (sqrt x) (sqrt y);
    mul4 (sqrt x) (sqrt y);
    sqrt_unique (x *. y) (sqrt x *. sqrt y)

let sqrt_div (x y:real)
  : Lemma (requires x >=. 0.0R /\ y >. 0.0R)
          (ensures y =!= 0.0R /\ sqrt y =!= 0.0R /\
                   sqrt (x /. y) == sqrt x /. sqrt y)
  = sqrt_positive y;
    sqrt_nonneg x;
    sqrt_square x; sqrt_square y;
    div_nonneg (sqrt x) (sqrt y);
    div4 (sqrt x) (sqrt y);
    sqrt_unique (x /. y) (sqrt x /. sqrt y)

let sqrt_two () : Lemma (sqrt two *. sqrt two == two /\ sqrt two >=. 0.0R)
  = sqrt_nonneg two; sqrt_square two
