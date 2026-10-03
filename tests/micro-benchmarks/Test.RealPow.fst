module Test.RealPow

open FStar.Real
open FStar.Math.Pow
module S = FStar.Math.Sqrt

#set-options "--fuel 0 --ifuel 0 --z3rlimit 10"

let integer_small (a:rpos)
  : Lemma (pow a 1.0R == a /\
           pow a 2.0R == a *. a /\
           pow a 3.0R == a *. a *. a)
  = pow_one a;
    pow_succ a 1;
    pow_succ a 2

let identities (a:rpos) (x:real)
  : Lemma (pow a 0.0R == 1.0R /\ pow a 1.0R == a /\ pow 1.0R x == 1.0R)
  = pow_zero a; pow_one a; pow_one_base x

let integers ()
  : Lemma (exp2 3.0R == 8.0R /\ exp2 (0.0R -. 3.0R) == 0.125R)
  = integer_small 2.0R;
    pow_neg 2.0R 3.0R

let small_base ()
  : Lemma (pow 0.5R 3.0R == 0.125R /\ pow 0.5R (0.0R -. 3.0R) == 8.0R)
  = integer_small 0.5R;
    pow_neg 0.5R 3.0R

let negative_integer_steps (a:rpos)
  : Lemma (pow a (0.0R -. 1.0R) == 1.0R /. a /\
           pow a (0.0R -. 2.0R) == 1.0R /. (a *. a))
  = pow_zero a;
    pow_succ a (-1);
    pow_succ a (-2)

let cube_root () : Lemma (pow 8.0R (1.0R /. 3.0R) == 2.0R)
  = integer_small 8.0R; integer_small 2.0R;
    pow_rational_unique 8.0R 1 3 2.0R

let two_thirds () : Lemma (pow 27.0R (2.0R /. 3.0R) == 9.0R)
  = integer_small 27.0R; integer_small 9.0R;
    pow_rational_unique 27.0R 2 3 9.0R

let small_cube_root () : Lemma (pow 0.125R (1.0R /. 3.0R) == 0.5R)
  = integer_small 0.125R; integer_small 0.5R;
    pow_rational_unique 0.125R 1 3 0.5R

let square_root (a:rpos)
  : Lemma (pow a 0.5R == S.sqrt a /\ pow a 0.5R *. pow a 0.5R == a)
  = pow_half a; S.sqrt_square a

let inverse_square_root ()
  : Lemma (exp2 (0.0R -. 0.5R) *. exp2 (0.0R -. 0.5R) == 0.5R)
  = square_root 2.0R; pow_neg 2.0R 0.5R

/// Exercise the real extension at an irrational exponent, across both signs.
let irrational_exponent ()
  : Lemma (2.0R <=. exp2 (S.sqrt 2.0R) /\ exp2 (S.sqrt 2.0R) <=. 4.0R /\
           exp2 (0.0R -. S.sqrt 2.0R) == 1.0R /. exp2 (S.sqrt 2.0R))
  = S.sqrt_one (); S.sqrt_mono 1.0R 2.0R;
    S.sqrt_sq 2.0R; S.sqrt_mono 2.0R 4.0R;
    pow_mono 2.0R 1.0R (S.sqrt 2.0R);
    pow_mono 2.0R (S.sqrt 2.0R) 2.0R;
    pow_one 2.0R;
    integer_small 2.0R;
    pow_neg 2.0R (S.sqrt 2.0R)

let all_real_exponents (x:real)
  : Lemma (exp2 x >. 0.0R /\ pow 0.5R x == 1.0R /. exp2 x)
  = pow_inverse_base 2.0R x

let decreasing_base (x y:real{x <=. y})
  : Lemma (pow 0.5R y <=. pow 0.5R x)
  = pow_antitone 0.5R x y

let three_halves (a:rpos)
  : Lemma (pow a 1.5R *. pow a 1.5R == a *. a *. a)
  = pow_rational a 3 2;
    integer_small a;
    integer_small (pow a 1.5R)

/// pow requires a strictly positive base.
[@@expect_failure [19]] let zero_base () = pow 0.0R 0.0R
[@@expect_failure [19]] let negative_base () = pow (0.0R -. 2.0R) 0.5R

/// Reject the false equations 2^0 = 0 and 8^(1/3) = 3.
[@@expect_failure [19]] let wrong_zero () : Lemma (exp2 0.0R == 0.0R) = pow_zero 2.0R
[@@expect_failure [19]] let wrong_root () : Lemma (pow 8.0R (1.0R /. 3.0R) == 3.0R) = cube_root ()
