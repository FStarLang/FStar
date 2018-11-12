(*
   Copyright 2008-2018 Microsoft Research

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
module X64.Poly1305.Math_i

open FStar.Tactics
open FStar.Tactics.Canon
open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul
open Calc
open X64.Vale.State_i   // needed for mem
open X64.Poly1305.Bitvectors_i

(*
open FStar.Mul
open FStar.UInt
open Semantics
lemma_BitwiseAdd64()
lemma_BitwiseMul64()
*)


// private unfold let op_Star = op_Multiply

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 0 --smtencoding.elim_box true --eager_inference --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native"

(*
let heapletTo128_preserved (m:mem) (m':mem) (i:int) (len:nat) =
  admit()
*)
(*
let heapletTo128_preserved (m:mem) (ptr num_bytes i:int) (len:nat) (m':mem) :
  Lemma(memModified m m' ptr num_bytes /\
        disjoint ptr num_bytes i ((len + 15) / 16 * 16)
        ==> heapletTo128 m i len == heapletTo128 m' i len)
  =
  let open FStar.FunctionalExtensionality in
  assert (memModified m m' ptr num_bytes /\
          disjoint ptr num_bytes i ((len + 15) / 16 * 16)
          ==> feq (heapletTo128 m i len) (heapletTo128 m' i len));
  ()
*)
let heapletTo128_all_preserved (m:mem) (ptr num_bytes i:int) (len:nat) =
  let equality_test (m':mem) = heapletTo128 m i len == heapletTo128 m' i len in
  let heapletTo128_preserved (m':mem) :
  Lemma(memModified m m' ptr num_bytes /\
        disjoint ptr num_bytes i ((len + 15) / 16 * 16)
        ==> equality_test m')
        =
        let open FStar.FunctionalExtensionality in
        assert (memModified m m' ptr num_bytes /\
               disjoint ptr num_bytes i ((len + 15) / 16 * 16)
               ==> feq (heapletTo128 m i len) (heapletTo128 m' i len));
        () in
  FStar.Classical.forall_intro (heapletTo128_preserved);
  ()


(* Getting a weird error otherwise, will file an issue
   when this gets merged in fstar branch *)
let poly1305_heap_blocks (h:int) (pad:int) (r:int) (m:mem) (i:int) (k) : int
 = poly1305_heap_blocks' h pad r m i k

let reveal_poly1305_heap_blocks (h:int) (pad:int) (r:int) (m:mem) (i:int) (k) =
  ()

let lemma_heap_blocks_preserved (m:mem) (h:int) (pad:int) (r:int) (ptr num_bytes i:int) (k) = admit()

#reset-options "--smtencoding.elim_box true --z3cliopt smt.arith.nl=true --max_fuel 1 --max_ifuel 1 --smtencoding.nl_arith_repr native --z3rlimit 100 --using_facts_from Prims --using_facts_from FStar.Math.Lemmas"

val lemma_mul_div_comm: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0 /\ a % b = 0))
          (ensures (a/b)*c == a * (c/b))
let lemma_mul_div_comm a b c =
    ()

val lemma_exact_mul: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0))
          (ensures ((a*c) % b = 0))
let lemma_exact_mul a b c =
  (* a*c = c*a *)
  swap_mul a c;

  (* (c*a)%b = ((c%b)*a)%b *)
  lemma_mod_mul_distr_l c a b;
  ()

val lemma_mul_div_sep: a:nat -> b:pos -> c:nat ->
    Lemma (requires (c % b = 0) /\ (a*c) % b = 0)
          (ensures (a*c)/b == a * (c/b))
let lemma_mul_div_sep a b c = ()

val swap_add: a:int -> b:int -> c:int -> Lemma
      (a + b + c = a + c + b)
let swap_add a b c = ()


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"

let lemma_poly_multiply (n:int) (p:pos) (r:int) (h:int) (r0:int) (r1:nat) (h0:int) (h1:int)
                        (h2:int) (s1:int) (d0:int) (d1:int) (d2:int) (hh:int) = admit()
  (* let helper_lemma (x:nat) (y:int) : Lemma *)
  (*   (ensures ((h2*n + h1)*((p+5)*x) + y + (h1*r0 + h0*r1)*n + h0*r0 == *)
  (*             y + (h0*r1 + h1*r0 + h2*(5*x))* n + *)
  (*             (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p)) = *)
  (*    assert_by_tactic ((h2*n+h1)*((p+5)*x) == (h2*n+h1)*5*x + ((h2*n+h1)*x)*p) canon; *)
  (*   calc ( *)
  (*     (h2*n + h1)*((p+5)*x) + (y + (h1*r0 + h0*r1)*n + h0*r0) *)
  (*     &= (h2*n + h1)*5*x + ((h2*n + h1)*x)*p + (y + (h1*r0 + h0*r1)*n + h0*r0) &| using z3 *)
  (*     &= (h2*n + h1)*5*x + (y + (h1*r0 + h0*r1)*n + h0*r0) + ((h2*n + h1)*x)*p &| *)
  (*        using (swap_add ((h2*n + h1)*5*x) *)
  (*                        (((h2*n + h1)*x)*p) *)
  (*                        ((h2*r0)*(n*n) + (h1*r0 + h0*r1)*n + h0*r0)) *)
  (*     &= y + (h0*r1 + h1*r0 + h2*(5*x))*n + (h0*r0 + h1*(5*x)) + ((h2*n + h1)*x)*p &|| canon *)
  (*     ) *)
  (* in *)
  (*   calc( *)
  (*     h*r *)
  (*     &= (h2*(n*n) + h1*n + h0)*(r1*n + r0) &| using z3 *)
  (*     &= (h2*n+h1)*((n*n)*r1)+(h2*r0)*(n*n)+(h1*r0+h0*r1)*n+h0*r0 &|| canon *)
  (*     &= ((h2*n+h1)*((p+5)*(r1/4)))+(h2*r0)*(n*n)+ *)
  (*        (h1*r0+h0*r1)*n + h0*r0 &| using (slash_star_axiom (n*n) 4 (p+5); *)
  (*                                          lemma_mul_div_comm (p+5) 4 r1; *)
  (*                                          z3) *)
  (*     &= (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + *)
  (*        (h0*r0 + h1*(5*(r1/4))) + ((h2*n + h1)*(r1/4))*p  &| using (helper_lemma (r1/4) *)
  (*                                                                      ((h2*r0)*(n*n)); z3) *)
  (*    ); *)
  (*     calc( *)
  (*       r1 + (r1/4) *)
  (*       &= 5*(r1/4) &| using (comm_plus #r1 #(r1/4); *)
  (*                             division_addition_lemma r1 4 r1; *)
  (*                             lemma_mul_div_sep 5 4 r1) *)
  (*     ); *)
  (*   // assumptions due to library requiring nats, can we switch to nats? *)
  (*     assume ((h2*n + h1) >= 0); *)
  (*     assume ((h2*n+h1)*(r1/4) >= 0); *)
  (*     assume ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4))) >= 0); *)
  (*     assert (hh == (h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + *)
  (*                          h0*r0 + h1*(5*(r1/4))); *)
  (*   (\* proof that ((h2*n + h1)*(r1/4))*p % p = 0 *\) *)
  (*     multiple_modulo_lemma ((h2*n + h1)*(r1/4)) p; *)
  (*   (\* and (a+b*p)%p = a%p*\) *)
  (*     lemma_mod_plus ((h2*r0)*(n*n) + (h0*r1 + h1*r0 + h2*(5*(r1/4)))*n + (h0*r0 + h1*(5*(r1/4)))) *)
  (*       ((h2*n + h1)*(r1/4)) p; *)
  (*     assert ((h*r) % p == hh % p) *)

let lemma_poly_reduce (n:int) (p:pos) (h:nat) (h2:nat) (h10:int) (c:int) (hh:int) =
  lemma_div_mod h (n*n);
  assert (h == (n*n)*h2 + h10);
  calc(
    h
      &= (n*n)*h2 + h10 &| using (lemma_div_mod h (n*n))
      &= (n*n)*((h2 / 4) * 4 + h2 % 4) + h10 &| using z3
      &= h10 + (h2 % 4)*(n*n) + (h2 / 4) * (p+5) &|| tadmit
// NS: used to be this
//     But I can't see how that could have worked, since the lemma invocation of paren_mul_right doesn't help in this context
//     Might have been relying on some Z3 flakiness
// (paren_mul_right (h2/4) 4 (n*n); canon;; admit_goal ())
      &= h10 + (h2 % 4)*(n*n) + (h2/4)*5 + p*(h2/4) &|| canon
      &= h10 + (h2 % 4)*(n*n) + c + p*(h2/4) &| using z3
      &= hh + p*(h2/4) &| using z3);
  // proving hh >= 0, annoying
  lemma_mod_lt h2 4;
  lemma_mul_nat_pos_is_nat (h2 % 4) (n*n);
  lemma_mod_lt h (n*n);
  assert (hh >= 0);
  lemma_mod_plus hh (h2/4) p

(* Provable, when we merge the UInt branch and use the lemmas
   from Poly1305_Bitvectors *)
let lemma_poly_bits64 =
  admit()

let lemma_mul_strict_upper_bound (x:nat) (x_bound:int) (y:nat) (y_bound:int) =
  lemma_mult_lt_right y x x_bound;
  if x_bound = 0 || y_bound = 0 then ()
  else
    if y = 0 then
    begin
      assert_norm(x*0 = 0);
      pos_times_pos_is_pos x_bound y_bound
    end
    else
      lemma_mult_lt_left x_bound y y_bound

// Again provable from Poly1305_Bitvectors
let lemma_bytes_shift_power2 (y:nat64) =
  admit()

//Same
let lemma_bytes_and_mod (x:nat64) (y:nat64) =
  admit()

let lemma_mod_factors(x0:nat) (x1:nat) (y:nat) (z:pos) :
  Lemma ((x0 + (y * z) * x1) % z == (x0 % z)) =
  nat_times_nat_is_nat y x1;
  lemma_mod_plus x0 (y*x1) z;
  assert_by_tactic ((y*z)*x1 == (y*x1)*z) canon

#reset-options "--initial_fuel 0 --max_fuel 0 --smtencoding.elim_box true"
let lemma_mul_pos_pos_is_pos_inverse (x:pos) (y:int) :
  Lemma (requires y*x > 0)
        (ensures y > 0) =
  if y = 0 then assert_norm (0*x == 0)
  else if y < 0 then assume(False)
  else ()

#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 0 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 8"
let lemma_mod_factor_lo(x0:nat64) (x1:nat64) (y:int) (z:pos) :
  Lemma (requires z < 0x10000000000000000 /\
                  y * z == 0x10000000000000000)
        (ensures ((x0 % z) < nat64_max) /\
                 lowerUpper128 x0 x1 % z == lowerUpper128 (x0 % z) 0) =
  lemma_mul_pos_pos_is_pos_inverse z y;
  modulo_range_lemma x0 z;
  lemma_mod_factors x0 x1 y z;
  assert_norm(lowerUpper128 x0 x1 % z == lowerUpper128 (x0 % z) 0)

let lemma_mod_power2_lo (x0:nat64) (x1:nat64) (y:int) (z:int) =
    assert (z > 0);
    lemma_mod_factor_lo x0 x1 0x10000000000000000 0x1;
    lemma_mod_factor_lo x0 x1 0x100000000000000 0x100;
    lemma_mod_factor_lo x0 x1 0x1000000000000 0x10000;
    lemma_mod_factor_lo x0 x1 0x10000000000 0x1000000;
    lemma_mod_factor_lo x0 x1 0x100000000 0x100000000;
    lemma_mod_factor_lo x0 x1 0x1000000 0x10000000000;
    lemma_mod_factor_lo x0 x1 0x10000 0x1000000000000;
    lemma_mod_factor_lo x0 x1 0x100 0x100000000000000;
    lemma_bytes_power2 ();
    admit()

let lemma_power2_add64 (n:nat) =
  pow2_plus 64 n;
  FStar.UInt.pow2_values 64

//TODO: dafny proof seems tedious
let lemma_mod_breakdown (a:nat) (b:pos) (c:pos) :
  Lemma(0<b*c /\ a%(b*c) == b * ((a/b)%c) + a%b) =
  lemma_mul_pos_pos_is_pos b c;
  nat_over_pos_is_nat a b;
  admit ()


#reset-options "--smtencoding.elim_box true --z3rlimit 8 --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
// using calc it was not even proving the first equation, look into this later
let lemma_mod_hi (x0:nat64) (x1:nat64) (z:nat64) =
  let n = 0x10000000000000000 in
  assert(lowerUpper128 x0 x1 % lowerUpper128 0 z = (x1 * n + x0) % (z * n));
  lemma_mod_breakdown (x1 * n + x0) n z;
  assert ((x1 * n + x0) % (z * n) == n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n);
  lemma_mod_plus x0 x1 n;
  assert (n * (((x1 * n + x0) / n) % z) + (x1 * n + x0) % n == n * (((x1 * n + x0) / n) % z) + x0 % n);
  assert(n * (((x1 * n + x0) / n) % z) + x0 % n == n * (x1 % z) + x0);
  admit()

let lemma_poly_demod (p:pos) (h:int) (x:int) (r:int) =
  admit()


#reset-options "--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false --max_fuel 2 --max_ifuel 1 --smtencoding.elim_box true --smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --z3rlimit 50"
let lemma_reduce128  (h:int) (h2:nat64) (h1:nat64) (h0:nat64) (g:int) (g2:nat64) (g1:nat64) (g0:nat64) =
      admit()
      (*
      reveal_opaque mod2_128';
      assert_norm (mod2_128(g - 0x400000000000000000000000000000000) == mod2_128(g));
      if (g2<4) then
      begin
        assert(h < 0x3fffffffffffffffffffffffffffffffb);
        assert(h >= 0);
        calc(
             mod2_128(modp(h))
          &= mod2_128(h) &| using (assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb)));
          assert_norm (mod2_128(h) == lowerUpper128 h0 h1) // TODO: assert_norm for Calc
      end
      else
      begin
       assert (0 <= h);
       assert (h - 0x3fffffffffffffffffffffffffffffffb <
                 0x3fffffffffffffffffffffffffffffffb);
       calc(
            mod2_128(modp(h))
         &= mod2_128(h - 0x3fffffffffffffffffffffffffffffffb) &|
                          using (assert (modp(h) == h % 0x3fffffffffffffffffffffffffffffffb);
                                 assert (h - 0x3fffffffffffffffffffffffffffffffb == h %
                                                         0x3fffffffffffffffffffffffffffffffb))
         &= mod2_128(g - 0x400000000000000000000000000000000) &| using z3
         &= mod2_128(g) &| using z3);
       assert_norm (mod2_128(g) == lowerUpper128 g0 g1)
      end;
      *)

let lemma_add_key (old_h0:nat64) (old_h1:nat64) (h_in:int) (key_s0:nat64) (key_s1:nat64) (key_s:int) (h0:nat64) (h1:nat64) =
  admit()

let lemma_lowerUpper128_and (x:nat128) (x0:nat64) (x1:nat64) (y:nat128) (y0:nat64) (y1:nat64) (z:nat128) (z0:nat64) (z1:nat64) =
  admit()


// let rec lemma_poly1305_heap_hash_blocks' (h:int) (pad:int) (r:int) (m:mem) (i:int) (len:nat)
//   (k:int{i <= k /\ (k - i) % 16 == 0 /\ k <= i + len /\
//     (forall j . {:pattern (m `Map.contains` j)} i <= j /\ j < i + (len + 15) / 16 * 16 && (j - i) % 8 = 0 ==> m `Map.contains` j)}) :
//   Lemma (requires True)
//      (ensures (poly1305_heap_blocks h pad r m i k == poly1305_hash_blocks h pad r (heapletTo128 m i len) i k))
//   (decreases (k-i)) =
//     let heapb = poly1305_heap_blocks h pad r m i k in
//     let hashb = poly1305_hash_blocks h pad r (heapletTo128 m i len) i k in
//     if i = k then
//       assert(heapb == hashb)
//     else
//       let kk = k - 16 in
//       assert (i >= 0 ==> precedes (kk - i) (k-i));
//       assert (i < 0 ==> precedes (kk - i) (k-i));
//       lemma_poly1305_heap_hash_blocks' h pad r m i len kk


let lemma_poly1305_heap_hash_blocks (h:int) (pad:int) (r:int) (m:mem) (i:int) (k) (len:nat) =
  admit()
  // decreases k - i

let lemma_add_mod128 (x y :int) =
  reveal_opaque mod2_128'
