module FStar.Math.Sqrt

open FStar.Real

type rnonneg = x:real{x >=. 0.0R}
type rpos = x:real{x >. 0.0R}

(* The nonnegative square root. *)
val sqrt (x : rnonneg) : rnonneg

val sqrt_square (x : rnonneg)
  : Lemma (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]

val sqrt_unique (x : rnonneg) (y : rnonneg)
  : Lemma (requires y *. y == x)
          (ensures sqrt x == y)

val sqrt_zero ()
  : Lemma (sqrt 0.0R == 0.0R)

val sqrt_one ()
  : Lemma (sqrt 1.0R == 1.0R)

val sqrt_sq (x : rnonneg)
  : Lemma (ensures sqrt (x *. x) == x)

val sqrt_positive (x : rpos)
  : Lemma (ensures sqrt x >. 0.0R)
          [SMTPat (sqrt x)]

val sqrt_mul (x y : rnonneg)
  : Lemma (ensures sqrt (x *. y) == sqrt x *. sqrt y)

val sqrt_div (x : rnonneg) (y : rpos)
  : Lemma (ensures sqrt (x /. y) == sqrt x /. sqrt y)

(* Inverse square root. *)
let rsqrt (x : rpos) : rpos =
  1.0R /. sqrt x
