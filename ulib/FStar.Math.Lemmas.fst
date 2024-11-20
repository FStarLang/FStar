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
module FStar.Math.Lemmas

open FStar.Mul
open FStar.Math.Lib

#set-options "--fuel 0 --ifuel 0"

(* Lemma: definition of Euclidean division *)
let euclidean_div_axiom a b = ()

let lemma_eucl_div_bound a b q = ()

let lemma_mult_le_left a b c = ()

let lemma_mult_le_right a b c = ()

let lemma_mult_lt_left a b c = ()

let lemma_mult_lt_right a b c = ()

let lemma_mult_lt_sqr (n:nat) (m:nat) (k:nat{n < k && m < k})
  : Lemma (n * m < k * k) =
  calc (<=) {
    n * m;
  <= { lemma_mult_le_left n m (k - 1) }
    n * (k - 1);
  <= { lemma_mult_le_right (k - 1) n (k - 1) }
    (k - 1) * (k - 1);
  <= {}
    k*k - 1;
  }

(* Lemma: multiplication on integers is commutative *)
let swap_mul a b = ()

let lemma_cancel_mul a b n = ()

(* Lemma: multiplication is right distributive over addition *)
let distributivity_add_left a b c = ()

(* Lemma: multiplication is left distributive over addition *)
let distributivity_add_right a b c =
  calc (==) {
    a * (b + c);
  == {}
    (b + c) * a;
  == { distributivity_add_left b c a }
    b * a + c * a;
  == {}
    a * b + a * c;
  }

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
(* GM: This is really just an identity since the LHS is associated to the left *)
let paren_mul_left a b c = ()

(* Lemma: multiplication is associative, hence parenthesizing is meaningless *)
let paren_mul_right a b c = ()

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
let paren_add_left a b c = ()

(* Lemma: addition is associative, hence parenthesizing is meaningless *)
let paren_add_right a b c = ()

let addition_is_associative a b c = ()

let subtraction_is_distributive a b c = ()

let swap_add_plus_minus a b c = ()

(* Lemma: minus applies to the whole term *)
let neg_mul_left a b = ()

(* Lemma: minus applies to the whole term *)
let neg_mul_right a b = ()

let swap_neg_mul a b =
  neg_mul_left a b;
  neg_mul_right a b

(* Lemma: multiplication is left distributive over subtraction *)
let distributivity_sub_left a b c =
  calc (==) {
    (a - b) * c;
  == {}
    (a + (-b)) * c;
  == { distributivity_add_left a (-b) c }
    a * c + (-b) * c;
  == { neg_mul_left b c }
    a * c - b * c;
  }

(* Lemma: multiplication is right distributive over subtraction *)
let distributivity_sub_right a b c =
  calc (==) {
    a * (b - c);
  == {}
    a * (b + (-c));
  == { distributivity_add_right a b (-c) }
    a * b + a * (-c);
  == { neg_mul_right a c }
    a * b - a * c;
  }

(* Lemma: multiplication precedence on addition *)
let mul_binds_tighter a b c = ()

let lemma_abs_mul a b = ()

let lemma_abs_bound a b = ()

let mul_ineq1 a b c d =
  if a = 0 || c = 0 then ()
  else begin
    lemma_abs_bound a b;
    lemma_abs_bound c d;
    lemma_abs_mul a c;
    lemma_mult_lt_left (abs a) (abs c) d;
    lemma_mult_lt_right d (abs a) b;
    lemma_abs_bound (a * c) (b * d);
    ()
  end

(* Zero is neutral for addition *)
let add_zero_left_is_same (n : int) : Lemma(0 + n = n) = ()
let add_zero_right_is_same (n : int) : Lemma(n + 0 = n) = ()

(* One is neutral for multiplication *)
let mul_one_left_is_same (n : int) : Lemma(1 * n = n) = ()
let mul_one_right_is_same (n : int) : Lemma(n * 1 = n) = ()

(* Multiplying by zero gives zero *)
let mul_zero_left_is_zero (n : int) : Lemma(0 * n = 0) = ()
let mul_zero_right_is_zero (n : int) : Lemma(n * 0 = 0) = ()

let nat_times_nat_is_nat a b = ()

let pos_times_pos_is_pos a b = ()

let nat_over_pos_is_nat a b = ()

let nat_plus_nat_equal_zero_lemma a b = ()

let int_times_int_equal_zero_lemma a b = ()

#push-options "--fuel 1"
let pow2_double_sum n = ()

let pow2_double_mult n = pow2_double_sum n

let rec pow2_lt_compat n m =
  match m with
  | 0 -> ()
  | _ -> pow2_lt_compat (n-1) (m-1)
#pop-options

let pow2_le_compat n m =
  if m < n then pow2_lt_compat n m

#push-options "--fuel 1"
let rec pow2_plus n m =
  match n with
  | 0 -> ()
  | _ -> pow2_plus (n - 1) m
#pop-options

(* Lemma : definition of the exponential property of pow2 *)
let pow2_minus n m =
  pow2_plus (n - m) m;
  slash_star_axiom (pow2 (n - m)) (pow2 m) (pow2 n)

(* Lemma: loss of precision in euclidean division *)
let multiply_fractions a n = ()

(** Same as `small_mod` *)
let modulo_lemma a b = ()

(** Same as `lemma_div_def` in Math.Lib *)
let lemma_div_mod a p = ()

let lemma_mod_lt a p = ()

let lemma_div_lt_nat a n m =
  lemma_div_mod a (pow2 m);
  assert(a = pow2 m * (a / pow2 m) + a % pow2 m);
  pow2_plus m (n-m);
  assert(pow2 n = pow2 m * pow2 (n - m))

let lemma_div_lt a n m =
  if a >= 0 then lemma_div_lt_nat a n m

let bounded_multiple_is_zero (x:int) (n:pos) = ()

let small_div (a:nat) (n:pos) : Lemma (requires a < n) (ensures a / n == 0) = ()

let small_mod (a:nat) (n:pos) : Lemma (requires a < n) (ensures a % n == a) = ()

let lt_multiple_is_equal a b x n =
  assert (0 * n == 0);
  bounded_multiple_is_zero x n

let lemma_mod_plus (a:int) (k:int) (n:pos) =
  calc (==) {
    (a+k*n)%n - a%n;
    == { lemma_div_mod a n; lemma_div_mod (a+k*n) n }
    ((a + k*n) - n*((a + k*n)/n)) - (a - n*(a/n));
    == {}
    n*k + n*(a/n) - n*((a + k*n)/n);
    == { distributivity_add_right n k (a/n);
         distributivity_sub_right n (k + a/n) ((a + k*n)/n) }
    n * (k + a/n - (a+k*n)/n);
  };
  lt_multiple_is_equal ((a+k*n)%n) (a%n) (k + a/n - (a+k*n)/n) n;
  ()

let lemma_div_plus (a:int) (k:int) (n:pos) =
  calc (==) {
    n * ((a+k*n)/n - a/n);
    == { distributivity_sub_right n ((a+k*n)/n) (a/n) }
    n * ((a+k*n)/n) - n*(a/n);
    == { lemma_div_mod (a+k*n) n; lemma_div_mod a n }
    (a + k*n - (a+k*n)%n) - (a - a%n);
    == {}
    k*n - (a+k*n)%n + a%n;
    == { lemma_mod_plus a k n }
    k*n;
  };
  lemma_cancel_mul ((a+k*n)/n - a/n) k n

let lemma_div_mod_plus (a:int) (k:int) (n:pos) : Lemma ((a + k * n) / n = a / n + k /\
                                                        (a + k * n) % n = a % n) =
    lemma_div_plus a k n;
    lemma_mod_plus a k n

let add_div_mod_1 a n =
    lemma_mod_plus a 1 n;
    lemma_div_plus a 1 n

let sub_div_mod_1 a n =
    lemma_mod_plus a (-1) n;
    lemma_div_plus a (-1) n

#push-options "--smtencoding.elim_box true --smtencoding.nl_arith_repr native"

let cancel_mul_div (a:int) (n:nonzero) = ()

#pop-options

let cancel_mul_mod (a:int) (n:pos) =
  small_mod 0 n;
  lemma_mod_plus 0 a n

let lemma_mod_add_distr (a:int) (b:int) (n:pos) =
  calc (==) {
    (a + b%n) % n;
    == { lemma_mod_plus (a + (b % n)) (b / n) n }
    (a + b%n + n * (b/n)) % n;
    == { lemma_div_mod b n }
    (a + b) % n;
  }

let lemma_mod_sub_distr (a:int) (b:int) (n:pos) =
  calc (==) {
    (a - b%n) % n;
    == { lemma_mod_plus (a - (b % n)) (-(b / n)) n }
    (a - b%n + n * (-(b/n))) % n;
    == { neg_mul_right n (b/n) }
    (a - b%n - n * (b/n)) % n;
    == { lemma_div_mod b n }
    (a - b) % n;
  }

let lemma_mod_sub_0 a = ()

let lemma_mod_sub_1 a b =
  calc (==) {
    (-a) % b;
    == { lemma_mod_plus (-a) 1 b }
    ((-a) + 1*b) % b;
    == {}
    (b - a) % b;
    == { small_mod (b-a) b }
    b - a;
    == { small_mod a b }
    b - a%b;
  }

let lemma_mod_mul_distr_l a b n =
  calc (==) {
    (a * b)  % n;
    == { lemma_div_mod a n }
    ((n * (a/n) + a%n) * b)  % n;
    == { distributivity_add_left (n * (a/n)) (a%n) b }
    (n * (a/n) * b + (a%n) * b)  % n;
    == { paren_mul_right n (a/n) b; swap_mul ((a/n) * b) n }
    ((a%n) * b + ((a/n) * b) * n)  % n;
    == { lemma_mod_plus ((a%n) * b) ((a/n) * b) n }
    ((a%n) * b)  % n;
  }

let lemma_mod_mul_distr_r (a:int) (b:int) (n:pos) =
  calc (==) {
    (a * b) % n;
    == { swap_mul a b }
    (b * a) % n;
    == { lemma_mod_mul_distr_l b a n }
    (b%n * a) % n;
    == { swap_mul a (b%n) }
    (a * (b%n)) % n;
  }

let lemma_mod_injective p a b = ()

let lemma_mul_sub_distr a b c =
  distributivity_sub_right a b c

let lemma_div_exact a p = ()

let div_exact_r (a:int) (n:pos) = lemma_div_exact a n

let lemma_mod_spec a p =
  calc (==) {
    (a - a%p)/p;
    == { lemma_div_mod a p }
    (p*(a/p))/p;
    == { cancel_mul_div (a/p) p }
    a/p;
  }

let lemma_mod_spec2 a p =
  calc (==) {
    (a % p) + ((a - (a % p)) / p) * p;
    == { lemma_mod_spec a p }
    (a % p) + (a / p) * p;
    == { lemma_div_mod a p }
    a;
  }

let lemma_mod_plus_distr_l a b p =
  let q = (a - (a % p)) / p in
  lemma_mod_spec2 a p;
  lemma_mod_plus (a % p + b) q p

let lemma_mod_plus_distr_r a b p =
  lemma_mod_plus_distr_l b a p

let lemma_mod_mod a b p =
  lemma_mod_lt b p;
  modulo_lemma (b % p) p

(* * Lemmas about multiplication, division and modulo. **)
(* * This part focuses on the situation where          **)
(* * dividend: nat    divisor: pos                     **)
(* * TODO: add triggers for certain lemmas.            **)

(* Lemma: Definition of euclidean division *)
let euclidean_division_definition a b = ()

(* Lemma: Propriety about modulo *)
let modulo_range_lemma a b = ()

let small_modulo_lemma_1 a b = ()

let small_modulo_lemma_2 a b = ()

let small_division_lemma_1 a b = ()

let small_division_lemma_2 (a:int) (n:pos) = lemma_div_mod a n

(* Lemma: Multiplication by a positive integer preserves order *)
let multiplication_order_lemma a b p = ()

(* Lemma: Propriety about multiplication after division *)
let division_propriety a b = ()

(* Internal lemmas for proving the definition of division *)
let division_definition_lemma_1 a b m =
  if a / b - 1 < 0 then () else begin
    division_propriety a b;
    multiplication_order_lemma m (a / b - 1) b
  end

let division_definition_lemma_2 a b m =
  division_propriety a b;
  multiplication_order_lemma (a / b + 1) m b

(* Lemma: Definition of division *)
let division_definition a b m =
  division_definition_lemma_1 a b m;
  division_definition_lemma_2 a b m

(* Lemma: (a * b) / b = a; identical to `cancel_mul_div` above *)
let multiple_division_lemma (a:int) (n:nonzero) = cancel_mul_div a n

(* Lemma: (a * b) % b = 0 *)
let multiple_modulo_lemma (a:int) (n:pos) = cancel_mul_mod a n

(* Lemma: Division distributivity under special condition *)
let division_addition_lemma a b n = division_definition (a + n * b) b (a / b + n)

(* Lemma: Modulo distributivity *)
let modulo_distributivity a b c =
  calc (==) {
    (a + b) % c;
    == { lemma_mod_plus_distr_l a b c }
    ((a % c) + b) % c;
    == { lemma_mod_plus_distr_r (a % c) b c }
    ((a % c) + (b % c)) % c;
  }

let lemma_div_le a b d =
  calc (==>) {
    (a <= b) <: Type0;
    ==> { lemma_div_mod a d; lemma_div_mod b d }
    d * (a/d) + a%d <= d * (b/d) + b%d;
    ==> {}
    d * (a/d) - d * (b/d) <= b%d - a%d;
    ==> {}
    d * (a/d - b/d) <= b%d - a%d;
    ==> { (* a%d >= 0, and b%d < d*) }
    d * (a/d - b/d) < d;
    ==> {}
    a/d - b/d <= 0;
  }

(* Lemma: Division distributivity under special condition *)
let division_sub_lemma (a:int) (n:pos) (b:nat) =
  neg_mul_left b n;
  lemma_div_plus a (-b) n

let lemma_mod_plus_mul_distr a b c p =
  calc (==) {
    ((a + b) * c) % p;
    == { lemma_mod_mul_distr_l (a + b) c p }
    (((a + b) % p) * c) % p;
    == { lemma_mod_mul_distr_r ((a + b) % p) c p }
    (((a + b) % p) * (c % p)) % p;
    == { modulo_distributivity a b p }
    ((((a % p) + (b % p)) % p) * (c % p)) % p;
  }

(* Lemma: Modulo distributivity under special condition *)
let modulo_addition_lemma (a:int) (n:pos) (b:int) = lemma_mod_plus a b n

(* Lemma: Modulo distributivity under special condition *)
let lemma_mod_sub (a:int) (n:pos) (b:int) =
  neg_mul_left b n;
  lemma_mod_plus a (-b) n

let mod_mult_exact (a:int) (n:pos) (q:pos) =
  calc (==) {
    a % n;
    == { lemma_div_mod a (n * q) }
    ((n * q) * (a / (n * q)) + a % (n * q))  % n;
    == { (* hyp *) }
    ((n * q) * (a / (n * q)))  % n;
    == { paren_mul_right n q (a / (n * q));
         swap_mul n (q * (a / (n * q))) }
    ((q * (a / (n * q))) * n) % n;
    == { multiple_modulo_lemma (q * (a / (n*q))) n }
    0;
  }

let mod_mul_div_exact (a:int) (b:pos) (n:pos) =
  calc (==) {
    (a / b) % n;
    == { lemma_div_mod a (b * n) (* + hyp *) }
    (((b*n)*(a / (b*n))) / b) % n;
    == { paren_mul_right b n (a / (b*n)) }
    ((b*(n*(a / (b*n)))) / b) % n;
    == { cancel_mul_div (n * (a / (b * n))) b }
    (n*(a / (b*n))) % n;
    == { cancel_mul_mod (a / (b*n)) n }
    0;
  }

#push-options "--fuel 1"
let mod_pow2_div2 (a:int) (m:pos) : Lemma
  (requires a % pow2 m == 0)
  (ensures (a / 2) % pow2 (m - 1) == 0)
  =
  mod_mul_div_exact a 2 (pow2 (m - 1))
#pop-options

private val lemma_div_lt_cancel (a : int) (b : pos) (n : int) :
  Lemma (requires (a < b * n))
        (ensures (a / b < n))

private let lemma_div_lt_cancel a b n =
  (* by contradiction *)
  if a / b >= n then begin
    calc (>=) {
      a;
      >= { slash_decr_axiom a b }
      (a / b) * b;
      >= {}
      n * b;
    };
    assert False
  end

private val lemma_mod_mult_zero (a : int) (b : pos) (c : pos) : Lemma ((a % (b * c)) / b / c == 0)
private let lemma_mod_mult_zero a b c =
  (* < 1 *)
  lemma_mod_lt a (b * c);
  lemma_div_lt_cancel (a % (b * c)) b c;
  lemma_div_lt_cancel ((a % (b * c)) / b) c 1;

  (* >= 0 *)
  nat_over_pos_is_nat (a % (b * c)) b;
  nat_over_pos_is_nat ((a % (b * c)) / b) c;
  ()

(* Lemma: Divided by a product is equivalent to being divided one by one *)
let division_multiplication_lemma (a:int) (b:pos) (c:pos) =
  calc (==) {
    a / b / c;
    == { lemma_div_mod a (b * c) }
    ((b * c) * (a / (b * c)) + a % (b * c)) / b / c;
    == { paren_mul_right b c (a / (b * c)) }
    (b * (c * (a / (b * c))) + a % (b * c)) / b / c;
    == { lemma_div_plus (a % (b * c)) (c * (a / (b * c))) b }
    (c * (a / (b * c)) + ((a % (b * c)) / b)) / c;
    == { lemma_div_plus ((a % (b * c)) / b) (a / (b * c)) c }
    (a / (b * c)) + (a % (b * c)) / b / c;
    == { lemma_mod_mult_zero a b c }
    a / (b * c);
  }

private val cancel_fraction (a:int) (b:pos) (c:pos) : Lemma ((a * c) / (b * c) == a / b)
private let cancel_fraction a b c =
  calc (==) {
    (a * c) / (b * c);
    == { swap_mul b c }
    (a * c) / (c * b);
    == { division_multiplication_lemma (a * c) c b }
    ((a * c) / c) / b;
    == { cancel_mul_div a c }
    a / b;
  }

let modulo_scale_lemma a b c =
  calc (==) {
    (a * b) % (b * c);
    == { lemma_div_mod (a * b) (b * c) }
    a * b - (b * c) * ((a * b) / (b * c));
    == { cancel_fraction a c b }
    a * b - (b * c) * (a / c);
    == { paren_mul_right b c (a / c) }
    a * b - b * (c * (a / c));
    == { swap_mul b (c * (a / c)); distributivity_sub_left a (c * (a / c)) b }
    (a - c * (a / c)) * b;
    == { lemma_div_mod a c }
    (a % c) * b;
  }

let lemma_mul_pos_pos_is_pos (x:pos) (y:pos) : Lemma (x*y > 0) = ()
let lemma_mul_nat_pos_is_nat (x:nat) (y:pos) : Lemma (x*y >= 0) = ()

let modulo_division_lemma_0 (a:nat) (b:pos) (c:pos) : Lemma
  (a / (b*c) <= a /\ (a - (a / (b * c)) * (b * c)) / b = a / b - ((a / (b * c)) * c))
  = slash_decr_axiom a (b*c);
    calc (==) {
      (a / (b*c)) * (b * c);
      == { swap_mul b c }
      (a / (b*c)) * (c * b);
      == { paren_mul_right (a / (b*c)) c b }
      ((a / (b*c)) * c) * b;
    };
    cut ((a / (b*c)) * (b * c) = ((a / (b * c)) * c) * b);
    lemma_div_mod a (b*c);
    division_sub_lemma a b ((a / (b*c)) * c);
    ()

let modulo_division_lemma a b c =
  calc (==) {
    (a % (b * c)) / b;
    == { lemma_div_mod a (b * c) }
    (a - (b * c) * (a / (b * c))) / b;
    == { paren_mul_right b c ((a / (b * c))); neg_mul_right b (c * (a / (b * c))) }
    (a + b * (-(c * (a / (b * c))))) / b;
    == { lemma_div_plus a (-(c * (a / (b * c)))) b }
    (a / b) - c * (a / (b * c));
    == { division_multiplication_lemma a b c }
    (a / b) - c * ((a / b) / c);
    == { lemma_div_mod (a/b) c }
    (a / b) % c;
  }

let modulo_modulo_lemma (a:int) (b:pos) (c:pos) =
  pos_times_pos_is_pos b c;
  calc (==) {
    (a % (b * c)) % b;
    == { calc (==) {
             a % (b * c);
             == { lemma_div_mod a (b * c) }
             a - (b * c) * (a / (b * c));
             == { paren_mul_right b c (a / (b * c)) }
             a - b * (c * (a / (b * c)));
         }}
    (a - b * (c * (a / (b * c)))) % b;
    == { () }
    (a + (- (b * (c * (a / (b * c)))))) % b;
    == { neg_mul_right b (c * (a / (b * c))) }
    (a + (b * (-c * (a / (b * c))))) % b;
    == { () }
    (a + (-c * (a / (b * c))) * b) % b;
    == { lemma_mod_plus a (-c * (a / (b * c))) b}
    a % b;
  }

let pow2_multiplication_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_division_lemma (a * pow2 (c - b)) (pow2 b)

let pow2_multiplication_division_lemma_2 a b c =
  pow2_plus c (b - c);
  division_multiplication_lemma (a * pow2 c) (pow2 c) (pow2 (b - c));
  multiple_division_lemma a (pow2 c)

let pow2_multiplication_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  paren_mul_right a (pow2 (c - b)) (pow2 b);
  paren_mul_left a (pow2 (c - b)) (pow2 b);
  multiple_modulo_lemma (a * pow2 (c - b)) (pow2 b)

let pow2_multiplication_modulo_lemma_2 a b c =
  calc (==) {
    (a * pow2 c) % pow2 b;
    == {}
    (a * pow2 c) % pow2 (c + (b-c));
    == { pow2_plus c (b-c) }
    (a * pow2 c) % (pow2 c * pow2 (b-c));
    == { modulo_scale_lemma a (pow2 c) (pow2 (b-c)) }
    (a % pow2 (b - c)) * pow2 c;
  }

let pow2_modulo_division_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_division_lemma a (pow2 b) (pow2 (c - b))

let pow2_modulo_division_lemma_2 a b c =
  pow2_le_compat b c;
  small_division_lemma_1 (a % pow2 c) (pow2 b)

let pow2_modulo_modulo_lemma_1 a b c =
  pow2_plus (c - b) b;
  modulo_modulo_lemma a (pow2 b) (pow2 (c - b))

let pow2_modulo_modulo_lemma_2 a b c =
  pow2_le_compat b c;
  small_modulo_lemma_1 (a % pow2 c) (pow2 b)

let modulo_add p a b c =
  modulo_distributivity a b p;
  modulo_distributivity a c p

let lemma_mod_twice a p = lemma_mod_mod (a % p) a p

let modulo_sub p a b c =
  modulo_add p (-a) (a + b) (a + c)

let mod_add_both (a:int) (b:int) (x:int) (n:pos) =
  calc (==) {
    (a + x) % n;
    == { modulo_distributivity a x n }
    ((a % n) + (x % n)) % n;
    == { (* hyp *) }
    ((b % n) + (x % n)) % n;
    == { modulo_distributivity b x n }
    (b + x) % n;
  }

let lemma_mod_plus_injective (n:pos) (a:int) (b:nat) (c:nat) =
  small_mod b n;
  small_mod c n;
  mod_add_both (a + b) (a + c) (-a) n

(* Another characterization of the modulo *)
let modulo_sub_lemma a b c =
  calc (==) {
    b;
    == { modulo_lemma b c }
    b % c;
    == { lemma_mod_twice b c }
    (b%c) % c;
    == { (* hyp *) }
    (b%c  + (a-b)%c) % c;
    == { modulo_distributivity b (a-b) c }
    (b+(a-b)) % c;
    == {}
    a % c;
  }
