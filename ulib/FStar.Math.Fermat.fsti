module FStar.Math.Fermat

open FStar.Mul
open FStar.Math.Euclid

/// Fermat's Little Theorem (and Binomial Theorem)
///
/// Proven by induction from the Freshman's dream identity
///
///   pow (a + b) p % p = (pow a p + pow b p) % p
///
/// which follows from the Binomial Theorem
///
///   pow (a + b) n = sum_{i=0}^n (binomial n k * pow a (n - i) * pow b i)
///
/// which in turn can be proved by induction from Pascal's identity
///
///   binomial n k + binomial n (k - 1) = binomial (n + 1) k
///
/// See
///  https://github.com/coqtail/coqtail/blob/master/src/Hierarchy/Commutative_ring_binomial.v
///  https://github.com/coq-contribs/rsa/blob/master/Binomials.v
///

#set-options "--fuel 0 --ifuel 0"

let rec pow (a:int) (k:nat) : int =
  if k = 0 then 1
  else a * pow a (k - 1)

val fermat (p:int{is_prime p}) (a:int) : Lemma (pow a p % p == a % p)

val mod_mult_congr (p:int{is_prime p}) (a b c:int) : Lemma
  (requires (a * c) % p = (b * c) % p /\ c % p <> 0)
  (ensures  a % p = b % p)

val fermat_alt (p:int{is_prime p}) (a:int{a % p <> 0}) : Lemma (pow a (p - 1) % p == 1)
