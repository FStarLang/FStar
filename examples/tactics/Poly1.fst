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
module Poly1

open FStar.Tactics.CanonCommSemiring
open FStar.Mul

assume val modulo_addition_lemma (a:int) (n:pos) (b:int) : Lemma ((a + b * n) % n = a % n)
assume val lemma_div_mod (a:int) (n:pos) : Lemma (a == (a / n) * n + a % n)

#set-options "--z3rlimit 150 --max_fuel 0 --max_ifuel 0 --using_facts_from '* -FStar.Tactics'"

// To print timing
#set-options "--query_stats"

[@@tcdecltime]
let lemma_poly_multiply (p:pos) (n r h r0 r1 h0 _h1 _h2 s1 d0 d1 d2 h1 h2 hh : int) : Lemma
  (requires r1 >= 0 /\ n > 0 /\ 4 * (n * n) == p + 5 /\ r == r1 * n + r0 /\
            h == h2 * (n * n) + h1 * n + h0 /\ s1 == r1 + (r1 / 4) /\ r1 % 4 == 0 /\
            d0 == h0 * r0 + h1 * s1 /\ d1 == h0 * r1 + h1 * r0 + h2 * s1 /\
            d2 == h2 * r0 /\ hh == d2 * (n * n) + d1 * n + d0)
  (ensures (h * r) % p == hh % p) =
  let r1_4 = r1 / 4 in
  let h_r_expand = (h2 * (n * n) + h1 * n + h0) * ((r1_4 * 4) * n + r0) in
  let hh_expand = (h2 * r0) * (n * n) + (h0 * (r1_4 * 4) + h1 * r0 + h2 * (5 * r1_4)) * n
    + (h0 * r0 + h1 * (5 * r1_4)) in
  let b = ((h2 * n + h1) * r1_4) in
  assert (h_r_expand == hh_expand + b * (n * n * 4 + (-5)));
  modulo_addition_lemma hh_expand p b
