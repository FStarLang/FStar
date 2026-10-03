module FStar.Math.Pow

open FStar.Real

type rpos = a:real{a >. 0.0R}

/// Real exponentiation for a strictly positive base and any real exponent.
///
/// [pow a x] is strictly positive. This is an erased operation on
/// [FStar.Real.real] for use in specifications and proofs.
///
/// Zero and negative bases are excluded because their powers are not defined
/// for every real exponent.
val pow (a:rpos) (x:real) : rpos

val pow_positive (a:rpos) (x:real) : Lemma (pow a x >. 0.0R)
val pow_zero (a:rpos) : Lemma (pow a 0.0R == 1.0R)
val pow_one (a:rpos) : Lemma (pow a 1.0R == a)
val pow_one_base (x:real) : Lemma (pow 1.0R x == 1.0R)

val pow_neg (a:rpos) (x:real)
  : Lemma (pow a (0.0R -. x) == 1.0R /. pow a x)
val pow_inverse_base (a:rpos) (x:real)
  : Lemma (pow (1.0R /. a) x == 1.0R /. pow a x)

/// Integer powers obey the usual recurrence, including negative exponents.
val pow_succ (a:rpos) (n:int)
  : Lemma (pow a (of_int (n+1)) == a *. pow a (of_int n))

/// For a nonnegative rational exponent m/n, (a^(m/n))^n = a^m.
val pow_rational (a:rpos) (m:nat) (n:pos)
  : Lemma (pow (pow a (of_int m /. of_int n)) (of_int n) == pow a (of_int m))

/// The positive nth root of a^m is unique.
val pow_rational_unique (a:rpos) (m:nat) (n:pos) (r:rpos)
  : Lemma (requires pow r (of_int n) == pow a (of_int m))
          (ensures pow a (of_int m /. of_int n) == r)

/// Exponentiation by one half agrees with the nonnegative square root.
val pow_half (a:rpos) : Lemma (pow a 0.5R == FStar.Math.Sqrt.sqrt a)

/// Exponentiation is nondecreasing in the exponent when the base is at least 1.
val pow_mono (a:real{a >=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a x <=. pow a y)

/// Exponentiation is nonincreasing in the exponent when the base is at most 1.
val pow_antitone (a:real{0.0R <. a /\ a <=. 1.0R}) (x y:real{x <=. y})
  : Lemma (pow a y <=. pow a x)

/// Raising a power to another exponent multiplies the exponents.
val pow_pow (a:rpos) (x y:real)
  : Lemma (pow (pow a x) y == pow a (x *. y))

let exp2 (x:real) : rpos = pow 2.0R x
