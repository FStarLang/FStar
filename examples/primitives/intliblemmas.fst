(*--build-config
  options:--verify_module IntLibLemmas;
  other-files:axioms.fst intlib.fst;
  --*)

module IntLibLemmas

open Axioms
open IntLib

val pow2_increases: n:nat -> m:nat -> Lemma 
  (requires (n > m)) (ensures (pow2 n > pow2 m)) (decreases (n-m))
let rec pow2_increases n m = match n - m with | 1 -> () | _ -> pow2_increases (n-1) m; pow2_increases n (n-1)

val pow2_exp: n:nat -> m:nat -> Lemma (pow2 n * pow2 m = pow2 (n+m))
let rec pow2_exp n m =  match n with | 0 -> () | _ -> pow2_exp (n-1) (m)

val pow2_doubles: n:nat -> Lemma (pow2 n + pow2 n = pow2 (n+1))
let pow2_doubles n = ()

assume val pow2_div: n:nat -> m:nat -> Lemma (div (pow2 n) (pow2 m) = pow2 (max (n-m) 0))
(* TODO 
let rec pow2_div n m = 
  match m with
  | 0 -> ()
  | _ -> if m < n then (pow2_div n (m-1); pow2_div (n-(m-1)) 1) else admit()
*)

assume val div_inequality: a:nat -> b:nat -> c:pos -> 
  Lemma ( (a < b ==> div a c <= div b c) /\ (a <= b ==> div a c <= div b c))
(* TODO
let div_inequality a b c = ()  
*)

assume val div_pow2_inequality: a:nat -> n:nat{a < pow2 n} -> Lemma (forall (m:nat). m <= n ==> div a (pow2 m) < pow2 (n-m))

assume val pow2_disjoint_ranges: x:nat -> y:nat -> n1:nat -> n2:nat ->
  Lemma (requires (x < pow2 n1 /\ y < pow2 n1 /\ x < pow2 n2 /\ y % pow2 n2 = 0))
	(ensures (x + y < pow2 n1))

val div_positive: a:nat -> b:pos -> Lemma (a / b >= 0)
let div_positive a b = ()

assume val modulo_lemma: a:nat -> b:pos -> Lemma ((a * b) % b = 0)
//let modulo_lemma a b = ()

(* TODO : sort all of this out *)
(*
(* Lemmas of x^n *)
val powx_lemma1:
  a:int -> Lemma (powx a 1 = a )
let powx_lemma1 a = ()

val powx_lemma2 :
    x:int -> n:nat -> m:nat ->
    Lemma (powx x n * powx x m = powx x (n+m))
let rec powx_lemma2 x n m =
  match m with
  | 0 -> ()
  | _ -> powx_lemma2 x n (m-1)

(* Lemma : pow2 is a stricly increasing function *) 
val pow2_increases_lemma: n:nat -> m:nat ->
  Lemma
    (requires (m < n))
    (ensures (pow2 m < pow2 n))
    (decreases (n-m))
let rec pow2_increases_lemma n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_increases_lemma (n-1) m; pow2_increases_lemma n (n-1)

(* Lemma : definition of the exponential property of pow2 *)
val pow2_exp_lemma: n:nat -> m:nat -> 
  Lemma (pow2 n * pow2 m = pow2 (n+m))
let rec pow2_exp_lemma n m =
  match n with
  | 0 -> ()
  | _ -> pow2_exp_lemma (n-1) (m)

(* Lemma : definition of the exponential property of pow2 *)
assume val pow2_div_lemma:
  n:nat -> m:nat{ n >= m } -> Lemma ((pow2 n) / (pow2 m) = pow2 (n-m))
(* let pow2_div_lemma n m =
  if n = m then ()
  else 
    (pow2_increases_lemma n m;
     pow2_exp_lemma (n-m) m;
     slash_star_axiom (pow2 (n-m)) (pow2 m) (pow2 n)) *)
     
(* Lemma : absolute value of product is the product of the absolute values *)
val abs_mul_lemma:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( abs ( a * b ) = abs a * abs b ))
let abs_mul_lemma a b = ()

(* Lemma : Non-euclidian division has a smaller output compared to its input *)
assume val div_non_eucl_decr_lemma:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures (abs (div a b) <= abs a))
(* let div_non_eucl_decr_lemma a b =
  (slash_decr_axiom (abs a) b) *)

(* Lemma : dividing by a bigger value leads to 0 if non euclidian division *)
val div_non_eucl_bigger_denom_lemma:
  a:int -> b:pos ->
  Lemma
    (requires ( b > abs a ))
    (ensures ( div a b = 0 ))
let div_non_eucl_bigger_denom_lemma a b = ()

(* Lemma : the absolute value of a signed_module b is bounded by b *)
val signed_modulo_property:
  v:int ->
  p:pos ->
  Lemma
    (requires (True))
    (ensures ( abs (mod v p ) < p ))
let signed_modulo_property v p = 
  if v >= 0 then euclidian_division_definition v p
  else euclidian_division_definition (-v) p

(* Lemma : loss of precision in euclidian division *)
val multiply_fractions_lemma:
  a:nat -> n:pos ->
  Lemma
    (requires (True))
    (ensures ( n * ( a / n ) <= a ))
let multiply_fractions_lemma a n =
  (euclidian_division_definition a n)

(* Lemma : multiplying by a strictly positive value preserves strict inequalities *)
val mul_pos_strict_incr_lemma: a:pos -> b:int -> c:pos -> Lemma (requires (b < c)) (ensures (a * b < a * c /\ b * a < c * a ))
let mul_pos_strict_incr_lemma a b c = ()

(* Lemma : multiplying by a positive value preserves inequalities *)
val mul_incr_lemma : a:nat -> b:nat -> c:nat -> 
		     Lemma 
		       (requires ( b <= c))
		       (ensures ( a * b <= a * c /\ b * a <= c * a))
let mul_incr_lemma a b c = ()

(* Lemma : distributivity of minus over parenthesized sum *)
val parenSub: a:int -> b:int -> c:int -> Lemma (a - (b + c) = a - b - c /\ a - (b - c) = a - b + c)
let parenSub a b c = ()

assume val log_incr_lemma: a:pos -> b:pos -> Lemma (requires (a < b)) (ensures (log_2 a <= log_2 b))
assume val log_2_lemma: a:nat -> b:nat -> Lemma (ensures (log_2 (pow2 a * pow2 b) = a + b))
