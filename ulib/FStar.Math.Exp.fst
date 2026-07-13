module FStar.Math.Exp

open FStar.Real
open FStar.Functions

type rpos = x:real{x >. 0.0R}

(* A proxy, see https://github.com/FStarLang/FStar/issues/4244 *)
assume val exp0 : real -> rpos

(* This module was somewhat painful to write. See also
https://github.com/FStarLang/FStar/issues/4245. *)

let exp = exp0

let exp0_injective (x y : real)
  : Lemma (ensures exp0 x == exp0 y ==> x == y)
  = admit() (* basic property, assumed *)

let exp0_surjective (x : rpos)
  : Lemma (ensures exists (y:real). exp0 y == x)
  = admit() (* basic property, assumed *)

let log0 : f : ((x:rpos) -> real) {is_bij f /\ f `is_inverse_of` exp0 /\ exp0 `is_inverse_of` f} =
  Classical.forall_intro_2 exp0_injective;
  Classical.forall_intro exp0_surjective;
  FStar.Functions.inverse_of_bij #real #rpos exp0

let log = log0

let exp_positive (x : real)
  : Lemma (ensures exp x >. 0.0R)
          [SMTPat (exp x)]
  = ()

let exp_base () : Lemma (exp 0.0R == 1.0R)
  = admit() (* basic property, assumed *)

let exp_add (x y : real)
  : Lemma (ensures exp (x +. y) == exp x *. exp y)
          [SMTPat (exp (x +. y))]
  = admit() (* basic property, assumed *)

let log_exp (x : real)
  : Lemma (ensures log (exp x) == x)
          [SMTPat (log (exp x))]
  = assert (log0 `is_inverse_of` exp0)

let exp_log (x : real{x >. 0.0R})
  : Lemma (ensures exp (log x) == x)
          [SMTPat (exp (log x))]
  = assert (log0 `is_inverse_of` exp0)

let exp_sub (x y : real)
  : Lemma (ensures exp (x -. y) == exp x /. exp y)
          [SMTPat (exp (x -. y))]
  = exp_add x (0.0R -. y);
    exp_add (0.0R -. y) y;
    exp_base ();
    ()

let log_mul (x y : real{x >. 0.0R /\ y >. 0.0R})
  : Lemma (ensures log (x *. y) == log x +. log y)
          [SMTPat (log (x *. y))]
  = assert (exp (log x +. log y) == exp (log x) *. exp (log y));
    ()

let log_div (x y : real{x >. 0.0R /\ y >. 0.0R})
  : Lemma (ensures log (x /. y) == log x -. log y)
          [SMTPat (log (x /. y))]
  = log_mul x (1.0R /. y);
    assert (exp (log x -. log y) == exp (log x) /. exp (log y));
    ()
