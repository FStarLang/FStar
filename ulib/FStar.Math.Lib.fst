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
module FStar.Math.Lib

open FStar.Mul

(* Definition of the division operator *)
val lemma_div_def: a:nat -> b:pos -> Lemma (a = b * (a/b) + a % b)
let lemma_div_def a b = ()

private let mul_lemma (a:nat) (b:nat) (c:nat) : Lemma (requires (a <= b))
                                           (ensures  (c * a <= c * b))
  = ()

private let mul_lemma' (a:nat) (b:nat) (c:pos) : Lemma (requires (c * a <= c * b))
                                           (ensures (a <= b))
  = ()

private let mul_div_lemma (a:nat) (b:pos) : Lemma (b * (a / b) <= a) = ()

val slash_decr_axiom: a:nat -> b:pos -> Lemma (a / b <= a)
let slash_decr_axiom a b =
    mul_lemma 1 b a;
    mul_div_lemma a b;
    mul_lemma' (a / b) a b

private let lemma_mul_minus_distr_l (a:int) (b:int) (c:int) : Lemma (a * (b - c) = a * b - a * c)
  = ()

(* Axiom: definition of the "b divides c" relation *)
#reset-options "--z3rlimit 30"
val slash_star_axiom: a:nat -> b:pos -> c:nat -> Lemma
  (requires (a * b = c))
  (ensures  (a = c / b))
let slash_star_axiom a b c =
  lemma_div_def c b;
  lemma_mul_minus_distr_l b a (c/b)

#reset-options
val log_2: x:pos -> Tot nat
let rec log_2 x =
  if x >= 2 then 1 + log_2 (x / 2) else 0

(* Function: power of x *)
val powx : x:int -> n:nat -> Tot int
let rec powx x n =
  match n with
  | 0 -> 1
  | n -> x * powx x (n - 1)

(* Function: absolute value *)
val abs: x:int -> Tot (y:int{ (x >= 0 ==> y = x) /\ (x < 0 ==> y = -x) })
let abs x = if x >= 0 then x else -x

(* Function: maximum value *)
val max: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = x) /\ (x < y ==> z = y) })
let max x y = if x >= y then x else y

(* Function: minimum value *)
val min: x:int -> y:int -> Tot (z:int{ (x >= y ==> z = y) /\ (x < y ==> z = x) })
let min x y = if x >= y then y else x

(* Function: standard euclidean division, the rest is always positive *)
val div: a:int -> b:pos -> Tot (c:int{(a < 0 ==> c < 0) /\ (a >= 0 ==> c >= 0)})
let div a b =
  if a < 0 then
    begin
    slash_decr_axiom (-a) b;
    if a % b = 0 then - (-a / b)
    else - (-a / b) - 1
    end
  else a / b

(* Function: equivalent of the '/' operator in C, hence the rest can be negative *)
val div_non_eucl: a:int -> b:pos ->
  Tot (q:int{ ( a >= 0 ==> q = a / b ) /\ ( a < 0 ==> q = -((-a)/b) ) })
let div_non_eucl a b =
  if a < 0 then 0 - ((0 - a) / b)
  else a / b

(* The equivalent of the << C operator *)
val shift_left: v:int -> i:nat -> Tot (res:int{res = v * (pow2 i)})
let shift_left v i =
  v * (pow2 i)

(* asr OCaml operator *)
val arithmetic_shift_right: v:int -> i:nat -> Tot (res:int{ res = div v (pow2 i) })
let arithmetic_shift_right v i = 
  div v (pow2 i)

(* Case of C cast functions ? *)
(* Implemented by "mod" in OCaml *)
val signed_modulo: v:int -> p:pos -> Tot (res:int{ res = v - ((div_non_eucl v p) * p) })
let signed_modulo v p =
  if v >= 0 then v % p
  else 0 - ( (0-v) % p)

val op_Plus_Percent : a:int -> p:pos -> 
  Tot (res:int{ (a >= 0 ==> res = a % p) /\ (a < 0 ==> res = -((-a) % p)) }) 
let op_Plus_Percent a p = signed_modulo a p

(** Useful lemmas for future proofs **)

(* Lemmas of x^n *)
val powx_lemma1: a:int -> Lemma (powx a 1 = a)
let powx_lemma1 a = ()

val powx_lemma2: x:int -> n:nat -> m:nat -> Lemma
  (powx x n * powx x m = powx x (n + m))
let rec powx_lemma2 x n m =
  let ass (x y z : int) : Lemma ((x*y)*z == x*(y*z)) = () in
  match n with
  | 0 -> ()
  | _ -> powx_lemma2 x (n-1) m; ass x (powx x (n-1)) (powx x m)

(* Lemma: absolute value of product is the product of the absolute values *)
val abs_mul_lemma: a:int -> b:int -> Lemma (abs (a * b) = abs a * abs b)
let abs_mul_lemma a b = ()

(* Lemma: absolute value of a signed_module b is bounded by b *)
val signed_modulo_property: v:int -> p:pos -> Lemma (abs (signed_modulo v p ) < p)
let signed_modulo_property v p = ()

(* Lemma: non-Euclidean division has a smaller output compared to its input *)
val div_non_eucl_decr_lemma: a:int -> b:pos -> Lemma (abs (div_non_eucl a b) <= abs a)
let div_non_eucl_decr_lemma a b =
  slash_decr_axiom (abs a) b

(* Lemma: dividing by a bigger value leads to 0 in non-Euclidean division *)
val div_non_eucl_bigger_denom_lemma: a:int -> b:pos -> Lemma
  (requires (b > abs a))
  (ensures  (div_non_eucl a b = 0))
let div_non_eucl_bigger_denom_lemma a b = ()
