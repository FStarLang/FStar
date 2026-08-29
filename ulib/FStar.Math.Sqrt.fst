module FStar.Math.Sqrt

open FStar.Real

module RS = FStar.Real.Sqrt

(* This used to be the sole mathematical axiom of the module:

     assume val sqrt0 (x : rnonneg) : y:rnonneg{y *. y == x}

   It is now a definition. [FStar.Real] is implemented by the Dedekind-cut
   construction of [FStar.Real.Dedekind], and [FStar.Real.Sqrt] uses the
   completeness of that construction to *prove* the existence of square
   roots -- something Z3's theory of reals, which is a theory of ordered
   fields only, cannot do.

   This module is kept for backwards compatibility; new code should use
   [FStar.Real.Sqrt] directly, whose [sqrt] is total (it returns [0.0R] on
   negative inputs) and which offers a few more lemmas. *)
let sqrt0 (x : rnonneg) : y:rnonneg{y *. y == x} =
  RS.sqrt_nonneg x;
  RS.sqrt_square x;
  RS.sqrt x

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
