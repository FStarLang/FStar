module CanonCommSemiring.Test

open FStar.Algebra.CommMonoid
open CanonCommSemiring
open FStar.Tactics
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0 --z3rlimit 10 --tactics_info"

///
///  Ring of integers
///

#push-options "--no_smt --tactic_trace_d 0" // Look, no SMT!

[@tcdecltime]
let test1 (a:int) =
  assert (a + a + a == 3 * a) by (int_semiring ())

let test2 (a b:int) =
  assert (b + a + a + a + 4 + a + 3 * (a + b) + 7 ==
          a * 3 + 2 * b + b + a + b * 1 + 7 + (2 + 1) * a + 4)
  by (int_semiring ())

let test3 (a b c:int) =
  assert (a * b + c + b * b == (b + a) * b + c) by (int_semiring())

let horner (r a0 a1 a2 a3 a4 a5 a6 a7:int) =
  assert (
    (((((((((((((a0 + a1) * r) + a2) * r) + a3) * r) + a4) * r) + a5) * r) + a6) * r) + a7) * r
    ==
    a7 * r +
      a6 * r * r +
        a5 * r * r * r +
          a4 * r * r * r * r +
            a3 * r * r * r * r * r +
              a2 * r * r * r * r * r * r +
                a1 * r * r * r * r * r * r * r +
                  a0 * r * r * r * r * r * r * r )
   by (int_semiring ())

let product (x y z:int) =
  assert (
    (x * x + 1) * (x * y + 2) * (y *  z + 1) * (y *  z + 1) * (y *  z + 1)
     ==
     x * x * x * y * y * y * y * z * z * z + 3 * x * x * x * y * y * y * z * z +
     3 * x * x * x * y * y * z + x * x * x * y + 2 * x * x * y * y * y * z * z *
     z + 6 * x * x * y * y * z * z + 6 * x * x * y * z + 2 * x * x + x * y * y *
     y * y * z * z * z + 3 * x * y * y * y * z * z + 3 * x * y * y * z + x * y +
     2 * y * y * y * z * z * z + 6 * y * y * z * z + 6 * y * z + 2)
  by (int_semiring ())

#pop-options

(* Need SMT for chain-compatibility of calc *)
let test1_calc (a:int) =
  calc (==) {
    a + a + a;
    == { _ by (int_semiring ()) }
    3 * a;
  }

///
/// Ring of integers modulo 2^130 - 5 (the Poly1305 prime)
///

/// This must be fully normalized
let prime: pos =
  normalize_term_spec (pow2 130 - 5);
  1361129467683753853853498429727072845819

let ring : eqtype = a:nat{a < prime}

[@canon_attr]
let zero : ring = 0

[@canon_attr]
let one : ring = 1

// Can't mark this as strict because https://github.com/FStarLang/FStar/issues/1923
//[@(strict_on_arguments [0;1])]
let ( +% ) (a b:ring) : ring = (a + b) % prime

// Can't mark this as strict because https://github.com/FStarLang/FStar/issues/1923
//[@(strict_on_arguments [0;1])]
let ( *% ) (a b:ring) : ring = (a * b) % prime

// We want this only to be unfolded for constants
[@(strict_on_arguments [0])]
let ( ~% ) (a:ring) : ring = (-a) % prime

val add_identity (a:ring) : Lemma (zero +% a == a)
let add_identity a = ()

val mul_identity (a:ring) : Lemma (one *% a == a)
let mul_identity a = ()

val add_associativity (a b c:ring) : Lemma (a +% b +% c == a +% (b +% c))
let add_associativity a b c =
  calc (==) {
    a +% b +% c;
    == { }
    ((a + b) % prime + c) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_l (a + b) c prime }
    ((a + b) + c) % prime;
    == { }
    (a + (b + c)) % prime;
    == { Math.Lemmas.lemma_mod_plus_distr_r a (b + c) prime }
    a +% (b +% c);
  }

val add_commutativity (a b:ring) : Lemma (a +% b == b +% a)
let add_commutativity a b = ()

val mul_associativity (a b c:ring) : Lemma (a *% b *% c == a *% (b *% c))
let mul_associativity a b c =
  calc (==) {
    a *% b *% c;
    == { }
    (((a * b) % prime) * c) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_l (a * b) c prime }
    ((a * b) * c) % prime;
    == { Math.Lemmas.paren_mul_right a b c }
    (a * (b * c)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b * c) prime }
    (a * ((b * c) % prime)) % prime;
    == { }
    a *% (b *% c);
  }

val mul_commutativity (a b:ring) : Lemma (a *% b == b *% a)
let mul_commutativity a b = ()

[@canon_attr]
let ring_add_cm : cm ring =
  CM zero ( +% ) add_identity add_associativity add_commutativity

[@canon_attr]
let ring_mul_cm : cm ring =
  CM one ( *% ) mul_identity mul_associativity mul_commutativity

val mul_add_distr: distribute_left_lemma ring ring_add_cm ring_mul_cm
let mul_add_distr a b c =
  calc (==) {
    a *% (b +% c);
    == { }
    (a * (b +% c)) % prime;
    == { Math.Lemmas.lemma_mod_add_distr a (b + c) prime }
    (a * ((b + c) % prime)) % prime;
    == { Math.Lemmas.lemma_mod_mul_distr_r a (b + c) prime }
    (a * (b + c)) % prime;
    == { Math.Lemmas.distributivity_add_right a b c }
    (a * b + a * c) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a * b) (a * c) prime }
    (a * b + a *% c) % prime;
    == { }
    (a *% c + a * b) % prime;
    == { Math.Lemmas.lemma_mod_add_distr (a *% c) (a * b) prime }
    (a *% c + a *% b) % prime;
    == { }
    (a *% b + a *% c) % prime;
    == { }
    a *% b +% a *% c;
  }

val mul_zero_l: mult_zero_l_lemma ring ring_add_cm ring_mul_cm
let mul_zero_l a = assert_norm (0 % prime == 0)

val add_opp (a:ring) : Lemma (a +% ~%a == zero)
let add_opp a = ()

[@canon_attr]
let ring_cr : cr ring = CR ring_add_cm ring_mul_cm ( ~% ) add_opp mul_add_distr mul_zero_l

let poly_semiring () : Tac unit = canon_semiring ring_cr; trefl()

let test (x y:ring) =
  assert (4 *% x +% 2 *% x == 3 *% x +% 3 *% x) by (poly_semiring ())

let test_poly1 (a b:ring) =
  assert (a +% b == b +% a) by (poly_semiring ())

let test_poly2 (a b c:ring) =
  assert (c *% (a +% b) == (a +% b) *% c) by (poly_semiring ())

let test_poly2b (a b c d:ring) =
  assert ((a +% b) *% (c +% d) == a *% c +% b *% c +% a *% d +% b *% d) 
  by (poly_semiring ())

let test_poly3 (a b c:ring) =
  assert (2 *% (a +% b) *% c == 2 *% b *% c +% 2 *% a *% c) by (poly_semiring ())

let test_poly4 (a b:ring) =
  assert (~%(a +% a +% b) +% b == ~%a +% ~% a) by (poly_semiring ())

let test_poly5 (a:ring) =
  assert ((a +% 1) *% (a +% ~%1) == a *% a +% ~%1) by (poly_semiring ())

let poly_update_repeat_blocks_multi_lemma2_simplify (a b c w r d:ring) :
  Lemma
  ( (((a *% (r *% r)) +% c) *% (r *% r)) +% ((b *% (r *% r)) +% d) *% r ==
    (((((a *% (r *% r)) +% b *% r) +% c) *% r) +% d) *% r)
=
  assert (
    (((a *% (r *% r)) +% c) *% (r *% r)) +% ((b *% (r *% r)) +% d) *% r ==
    ((a *% (r *% r) +% b *% r +% c) *% r +% d) *% r)
  by (poly_semiring ())
