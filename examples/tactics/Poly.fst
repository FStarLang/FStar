module Poly

open CanonCommSemiring
open FStar.Tactics
open FStar.Mul

// These assumptions are proven in https://github.com/project-everest/vale/blob/fstar/src/lib/math/Math.Lemmas.Int_i.fsti
assume val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
assume val lemma_div_mod (a:int) (n:pos) : Lemma (a == (a / n) * n + a % n)

// Actually goes through with a higher limit
[@Pervasives.fail]
let lemma_poly_multiply_smt n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  let b = ((h2 * n + h1) * r1_4) in
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))

let lemma_poly_multiply_lemma n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  let b = ((h2 * n + h1) * r1_4) in
  modulo_addition_lemma hh_expand p b;
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))
  
let lemma_poly_multiply_canon n p r h r0 r1 h0 h1 h2 s1 d0 d1 d2 hh =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  let b = ((h2 * n + h1) * r1_4) in
  modulo_addition_lemma hh_expand p b;
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)))
      by (fun () -> canon_semiring int_cr)

val lemma_poly_reduce : n:int -> p:int -> h:int -> h2:int -> h10:int -> c:int -> hh:int -> Lemma
  (requires
    p > 0 /\
    4 * (n * n) == p + 5 /\
    h2 == h / (n * n) /\
    h10 == h % (n * n) /\
    c == (h2 / 4) + (h2 / 4) * 4 /\
    hh == h10 + c + (h2 % 4) * (n * n))
  (ensures h % p == hh % p)

let lemma_poly_reduce n p h h2 h10 c hh =
  let h2_4 = h2 / 4 in
  let h2_m = h2 % 4 in
  let h_expand = h10 + (h2_4 * 4 + h2_m) * (n * n) in
  let hh_expand = h10 + (h2_m) * (n * n) + h2_4 * 5 in
  lemma_div_mod h (n * n);
  modulo_addition_lemma hh_expand p h2_4;
  assert (h_expand == hh_expand + h2_4 * (n * n * 4 + (-5)))
      by (fun () -> canon_semiring int_cr)
