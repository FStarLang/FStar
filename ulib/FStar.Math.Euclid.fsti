module FStar.Math.Euclid

open FStar.Mul

///
/// Divides relation
///
/// It is reflexive, transitive, and antisymmetric up to sign.
/// When a <> 0, a `divides` b iff a % b = 0 (this is proved below)
///

let divides (a b:int) : prop = exists q. b = q * a

val divides_reflexive (a:int) : Lemma (a `divides` a) [SMTPat (a `divides` a)]

val divides_transitive (a b c:int) : Lemma
  (requires a `divides` b /\ b `divides` c)
  (ensures  a `divides` c)

val divide_antisym (a b:int) : Lemma
  (requires a `divides` b /\ b `divides` a)
  (ensures  a = b \/ a = -b)

val divides_0 (a:int) : Lemma (a `divides` 0)

val divides_1 (a:int) : Lemma (requires a `divides` 1) (ensures a = 1 \/ a = -1)

val divides_minus (a b:int) : Lemma
  (requires a `divides` b)
  (ensures  a `divides` (-b))

val divides_opp (a b:int) : Lemma
  (requires a `divides` b)
  (ensures (-a) `divides` b)

val divides_plus (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a + b))

val divides_sub (a b d:int) : Lemma
  (requires d `divides` a /\ d `divides` b)
  (ensures  d `divides` (a - b))

val divides_mult_right (a b d:int) : Lemma
  (requires d `divides` b)
  (ensures  d `divides` (a * b))

///
/// Greatest Common Divisor (GCD) relation
///
/// We deviate from the standard definition in that we allow the divisor to
/// be negative. Thus, the GCD of two integers is unique up to sign.
///

let is_gcd (a b d:int) : prop =
  d `divides` a /\
  d `divides` b /\
  (forall x. (x `divides` a /\ x `divides` b) ==> x `divides` d)

val mod_divides (a:int) (b:nonzero) : Lemma (requires a % b = 0) (ensures b `divides` a)

val divides_mod (a:int) (b:nonzero) : Lemma (requires b `divides` a) (ensures a % b = 0)

val is_gcd_unique (a b c d:int) : Lemma
  (requires is_gcd a b c /\ is_gcd a b d)
  (ensures  c = d \/ c = -d)

val is_gcd_reflexive (a:int) : Lemma (is_gcd a a a)

val is_gcd_symmetric (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a d)

val is_gcd_0 (a:int) : Lemma (is_gcd a 0 a)

val is_gcd_1 (a:int) : Lemma (is_gcd a 1 1)

val is_gcd_minus (a b d:int) : Lemma
  (requires is_gcd a (-b) d)
  (ensures  is_gcd b a d)

val is_gcd_opp (a b d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd b a (-d))

val is_gcd_plus (a b q d:int) : Lemma
  (requires is_gcd a b d)
  (ensures  is_gcd a (b + q * a) d)

///
/// Extended Euclidean algorithm
///
/// Computes the GCD of two integers (a, b) together with Bézout coefficients
/// (r, s) satisfying r a + s b = gcd(a, b)
///

val euclid_gcd (a b:int) : Pure (int & int & int)
  (requires True)
  (ensures  fun (r, s, d) -> r * a + s * b = d /\ is_gcd a b d)

///
/// A definition of primality based on the divides relation
///

let is_prime (p:int) =
  1 < p /\
  (forall (d:int).{:pattern (d `divides` p)}
     (d `divides` p ==> (d = 1 \/ d = -1 \/ d = p \/ d = -p)))

val bezout_prime (p:int) (a:pos{a < p}) : Pure (int & int)
  (requires is_prime p)
  (ensures  fun (r, s) -> r * p + s * a = 1)

///
/// Euclid's lemma and its generalization to arbitrary integers
///
/// - If a prime p divides a*b, then it must divide at least one of a or b
/// - If n divides a*b and a,n are coprime then n divides b
///

val euclid (n:pos) (a b r s:int) : Lemma
  (requires (a * b) % n = 0 /\ r * n + s * a = 1)
  (ensures  b % n = 0)

val euclid_prime (p:int{is_prime p}) (a b:int) : Lemma
  (requires (a * b) % p = 0)
  (ensures  a % p = 0 \/ b % p = 0)
