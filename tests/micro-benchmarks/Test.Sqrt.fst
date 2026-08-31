module Test.Sqrt

open FStar.Real
open FStar.Math.Sqrt

let sqrt_2 : r:rnonneg{r *. r == 2.0R} = sqrt_square 2.0R; sqrt 2.0R

let test_sqrt_2_mul = assert (sqrt_2 *. sqrt_2 == 2.0R)

let test_sqrt_2_add = assert (sqrt_2 >. 1.0R)

let test_sqrt_2_add_explicit =
  (* A bit of SMT wrestling can prove it *)
  let mlem (x y : (r:real{r >=. 0.0R})) : Lemma (requires x*.x >. y*.y) (ensures x >. y) =
    ()
  in
  mlem sqrt_2 1.0R;
  assert (sqrt_2 >. 1.0R)

#push-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
let test_sqrt_2_scale = assert (1.0R /. sqrt_2 == sqrt_2 /. 2.0R)
#pop-options

let test_zero = sqrt_zero ()
let test_one = sqrt_one ()
let test_sq (x:rnonneg) = sqrt_sq x
let test_mono = sqrt_mono 1.0R 2.0R; assert (sqrt 1.0R <. sqrt_2)
let test_mul (x y:rnonneg) = sqrt_mul x y
let test_div (x:rnonneg) (y:rpos) = sqrt_div x y
let test_rsqrt (x:rpos) = assert (rsqrt x >. 0.0R)
