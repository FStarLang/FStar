(*
   Copyright 2008-2026 Microsoft Research

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
module FStar.Rational.Gcd

/// Euclid's algorithm as a *computable* function, together with the proof that
/// it agrees with the relational specification [FStar.Math.Euclid.is_gcd].
///
/// The point of this module is containment. [is_gcd] and [divides] are
/// quantified predicates, and letting them into an SMT context together with
/// nonlinear integer arithmetic reliably produces matching loops. Here we pay
/// that cost once and export a purely computational notion of "in lowest
/// terms" ([reduced]) that downstream modules can carry around for free.

open FStar.Math.Euclid

module L = FStar.Math.Lemmas
module C = FStar.Classical

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(**** Euclid's algorithm *)

let rec gcd_nat (a b:nat) : Tot nat (decreases b) =
  if b = 0 then a else gcd_nat b (a % b)

#push-options "--fuel 1"
let rec gcd_nat_pos (a b:nat)
  : Lemma (requires a > 0 \/ b > 0)
          (ensures  gcd_nat a b > 0)
          (decreases b)
  = if b = 0 then () else gcd_nat_pos b (a % b)

let rec gcd_nat_is_gcd (a b:nat)
  : Lemma (ensures is_gcd a b (gcd_nat a b)) (decreases b)
  = if b = 0 then is_gcd_0 a
    else begin
      gcd_nat_is_gcd b (a % b);
      let g = gcd_nat b (a % b) in
      L.lemma_div_mod a b;
      L.swap_mul b (a / b);
      assert (a % b + (a / b) * b == a);
      is_gcd_plus b (a % b) (a / b) g;
      is_gcd_symmetric b a g
    end
#pop-options

(**** The gcd of an integer and a positive integer *)

let iabs (n:int) : nat = if n < 0 then -n else n

let gcd (n:int) (d:pos) : pos =
  gcd_nat_pos (iabs n) d;
  gcd_nat (iabs n) d

let gcd_is_gcd (n:int) (d:pos)
  : Lemma (is_gcd n d (gcd n d))
  = gcd_nat_is_gcd (iabs n) d;
    let g = gcd n d in
    if n < 0 then begin
      assert (is_gcd (-n) d g);
      is_gcd_symmetric (-n) d g;
      is_gcd_minus d n g
    end

let gcd_divides (n:int) (d:pos)
  : Lemma (gcd n d `divides` n /\ gcd n d `divides` d)
  = gcd_is_gcd n d

(**** [reduced]: a quantifier-free notion of "in lowest terms" *)

let reduced (n:int) (d:pos) : bool = gcd n d = 1

let reduced_coprime (n:int) (d:pos)
  : Lemma (requires reduced n d) (ensures is_gcd n d 1)
  = gcd_is_gcd n d

let coprime_reduced (n:int) (d:pos)
  : Lemma (requires is_gcd n d 1) (ensures reduced n d)
  = gcd_is_gcd n d;
    is_gcd_unique n d 1 (gcd n d)

#push-options "--fuel 2"
let reduced_den_one (n:int) : Lemma (reduced n 1) = ()
#pop-options

(**** Bezout, and Gauss's lemma *)

/// Pure integer arithmetic, discharged away from any [divides] hypothesis.
let neg_bezout (r s a b:int)
  : Lemma (requires r * a + s * b == -1)
          (ensures  (-r) * a + (-s) * b == 1)
  = L.neg_mul_left r a;
    L.neg_mul_left s b

let bezout (a b:int)
  : Ghost (int & int)
      (requires is_gcd a b 1)
      (ensures  fun (r, s) -> r * a + s * b = 1)
  = let rsg = euclid_gcd a b in
    let (r, s, g) = rsg in
    assert (r * a + s * b == g);
    is_gcd_unique a b 1 g;
    assert (g == 1 \/ g == -1);
    if g = 1 then (r, s)
    else begin
      neg_bezout r s a b;
      (-r, -s)
    end

/// Gauss's lemma: a modulus coprime to one factor divides the other.
let coprime_divides_mul (m:pos) (a b:int)
  : Lemma (requires is_gcd m a 1 /\ m `divides` (a * b))
          (ensures  m `divides` b)
  = let (r, s) = bezout m a in
    divides_mod (a * b) m;
    euclid m a b r s;
    mod_divides b m

(**** Uniqueness of the reduced representative *)

let divides_cross (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (requires reduced n1 d1 /\ n1 * d2 == n2 * d1)
          (ensures  d1 `divides` d2)
  = reduced_coprime n1 d1;
    is_gcd_symmetric n1 d1 1;
    C.exists_intro (fun q -> n1 * d2 = q * d1) n2;
    assert (d1 `divides` (n1 * d2));
    coprime_divides_mul d1 n1 d2

let den_eq (n1:int) (d1:pos) (n2:int) (d2:pos)
  : Lemma (requires reduced n1 d1 /\ reduced n2 d2 /\ n1 * d2 == n2 * d1)
          (ensures  d1 == d2)
  = divides_cross n1 d1 n2 d2;
    divides_cross n2 d2 n1 d1;
    divide_antisym d1 d2

(**** Dividing out the gcd *)

let one_divides (a:int) : Lemma (1 `divides` a) =
  C.exists_intro (fun q -> a = q * 1) a

/// Pure nonlinear rearrangements, isolated from the [divides] context.
let mul_rearrange1 (g k x:int) : Lemma (g * (k * x) == k * (x * g)) = ()
let mul_rearrange2 (q x g:int) : Lemma (q * (x * g) == g * (q * x)) = ()

let mul_cancel_left (g:pos) (u v:int)
  : Lemma (requires g * u == g * v) (ensures u == v)
  = L.swap_mul g u;
    L.swap_mul g v;
    L.lemma_cancel_mul u v g

let quotient_coprime_aux (n:int) (d:pos) (g:pos) (a b x:int)
  : Lemma (requires is_gcd n d g /\ n == g * a /\ d == g * b /\
                    x `divides` a /\ x `divides` b)
          (ensures  x `divides` 1)
  = eliminate exists ka. a == ka * x
    with
    eliminate exists kb. b == kb * x
    with begin
      mul_rearrange1 g ka x;
      mul_rearrange1 g kb x;
      assert (n == ka * (x * g));
      assert (d == kb * (x * g));
      C.exists_intro (fun q -> n = q * (x * g)) ka;
      C.exists_intro (fun q -> d = q * (x * g)) kb;
      assert ((x * g) `divides` n /\ (x * g) `divides` d);
      assert ((x * g) `divides` g);
      eliminate exists q. g == q * (x * g)
      with begin
        mul_rearrange2 q x g;
        assert (g * 1 == g * (q * x));
        mul_cancel_left g 1 (q * x);
        assert (1 == q * x);
        C.exists_intro (fun k -> 1 = k * x) q
      end
    end

let quotient_coprime (n:int) (d:pos) (g:pos) (a b:int)
  : Lemma (requires is_gcd n d g /\ n == g * a /\ d == g * b)
          (ensures  is_gcd a b 1)
  = one_divides a;
    one_divides b;
    introduce forall (x:int). (x `divides` a /\ x `divides` b) ==> x `divides` 1
    with introduce _ ==> _
    with quotient_coprime_aux n d g a b x

let pos_factor (g:pos) (b:int)
  : Lemma (requires g * b > 0) (ensures b > 0) = ()

let exact_quotient (g:pos) (a:int)
  : Lemma (requires g `divides` a) (ensures a == g * (a / g))
  = divides_mod a g;
    L.lemma_div_mod a g

/// The central fact about normalization: dividing [n] and [d] by their gcd
/// gives a fraction in lowest terms with a positive denominator.
let reduce_ok (n:int) (d:pos)
  : Lemma (ensures (let g = gcd n d in
                    d / g > 0 /\ reduced (n / g) (d / g) /\
                    n == g * (n / g) /\ d == g * (d / g)))
  = let g = gcd n d in
    gcd_divides n d;
    gcd_is_gcd n d;
    exact_quotient g n;
    exact_quotient g d;
    let a = n / g in
    let b = d / g in
    assert (d == g * b /\ d > 0 /\ g > 0);
    pos_factor g b;
    quotient_coprime n d g a b;
    coprime_reduced a b

(**** The gcd of zero *)

#push-options "--fuel 2"
let gcd_zero (d:pos) : Lemma (gcd 0 d == d) = ()
#pop-options
