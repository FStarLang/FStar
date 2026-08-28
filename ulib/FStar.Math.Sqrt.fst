module FStar.Math.Sqrt

open FStar.Real

(* This is the sole mathematical axiom: every nonnegative real has a
   nonnegative square root.  The refinement records both defining properties,
   so the remaining laws in this module can be proved from real arithmetic. *)
assume val sqrt0 (x : rnonneg)
  : y:rnonneg{y *. y == x}

let sqrt = sqrt0

(* All of the proofs below work via SMT only. The lemma calls
   are just in case. *)

let sqrt_square (x : rnonneg)
  : Lemma (ensures sqrt x *. sqrt x == x)
          [SMTPat (sqrt x *. sqrt x)]
  = ()

let sqrt_unique (x : rnonneg) (y : rnonneg)
  : Lemma (requires y *. y == x)
          (ensures sqrt x == y)
  = ()

let sqrt_zero ()
  : Lemma (sqrt 0.0R == 0.0R)
  = sqrt_unique 0.0R 0.0R

let sqrt_one ()
  : Lemma (sqrt 1.0R == 1.0R)
  = sqrt_unique 1.0R 1.0R

let sqrt_sq (x : rnonneg)
  : Lemma (ensures sqrt (x *. x) == x)
  = sqrt_unique (x *. x) x

let sqrt_positive (x : rpos)
  : Lemma (ensures sqrt x >. 0.0R)
          [SMTPat (sqrt x)]
  = sqrt_square x

let sqrt_mul (x y : rnonneg)
  : Lemma (ensures sqrt (x *. y) == sqrt x *. sqrt y)
  = sqrt_square x;
    sqrt_square y;
    sqrt_unique (x *. y) (sqrt x *. sqrt y)

let sqrt_div (x : rnonneg) (y : rpos)
  : Lemma (ensures sqrt (x /. y) == sqrt x /. sqrt y)
  = sqrt_square x;
    sqrt_square y;
    sqrt_positive y;
    sqrt_unique (x /. y) (sqrt x /. sqrt y)
