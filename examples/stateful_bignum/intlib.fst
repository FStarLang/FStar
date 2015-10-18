(*--build-config
  options:--verify_module IntLib;
  other-files:axiomatic.fst
  --*)

(*
  This library file contains definitions for standard math functions.
  They should be extended with anything necessary and the associated lemmas.
 *)
(*
  STATUS : 
    Missing real implementation of log and proof of its axioms.
 *)

module IntLib

open Axiomatic

(* Mathematical useful fonctions *)

(* Function : power of 2 *)
val pow2:
  n:nat -> Tot pos
let rec pow2 n =
  if n = 0 then 1
  else 2 * pow2 (n-1)

(* Function : power of x *)
val powx : x:int -> n:nat -> Tot int
let rec powx x n =
  match n with
  | 0 -> 1
  | _ -> x * powx x (n-1)

(* Lemmas of x^n *)
opaque val powx_lemma1:
  a:int ->
  Lemma
    (requires (True))
    (ensures ( powx a 1 = a ))
let powx_lemma1 a = ()

opaque val powx_lemma2 :
    x:int -> n:nat -> m:nat ->
    Lemma
      (requires (True))
      (ensures (powx x n * powx x m = powx x (n+m)))
let rec powx_lemma2 x n m =
  match m with
  | 0 -> ()
  | _ -> powx_lemma2 x n (m-1)

(* Function : absolute value *)
val abs:
  x:int ->
  Tot (y:int{ ((x >= 0) ==> ( y = x)) /\ ((x < 0) ==> y = -x) })
let abs x =
  if x >= 0 then x
  else -x

(* Function : maximum value *)
val max:
  x:int -> y:int ->
  Tot (z:int{ ( x >= y ==> z = x) /\ (x < y ==> z = y) })
let max x y =
  if x >= y then x else y

(* Function : minimum value *)
val min:
  x:int -> y:int ->
  Tot (z:int{ ( x >= y ==> z = y) /\ (x < y ==> z = x) })
let min x y =
  if x >= y then y else x

(* Function : standard euclidian division, the rest is always positive *)
val div:
  a:int -> b:pos -> Tot (c:int{ (a < 0 ==> c < 0) /\ (a >= 0 ==> c >= 0)})
let div a b =
  if a < 0 then
    (if a % b = 0 then -(-a/b)
    else -(-a/b) -1)
  else a / b

(* Function : equivalent of the '/' operator in C, hence the rest can be negative *)
val div_non_eucl:
  a:int -> b:pos ->
  Tot (q:int{ ( a >= 0 ==> q = a / b ) /\ ( a < 0 ==> q = -((-a)/b) ) })
let div_non_eucl a b =
  if a < 0 then -((-a) / b)
  else a / b

(* The equivalent of the << C operator *)
val shift_left: v:int -> i:nat -> Tot (res:int{ res = v * (pow2 i)})
let shift_left v i =
  v * (pow2 i)

(* asr OCaml operator *)
val arithmetic_shift_right: v:int -> i:nat -> Tot (res:int{ res = div v (pow2 i) })
let arithmetic_shift_right v i = 
  div v (pow2 i)

(* Case of C cast functions ? *)
(* Implemented by "mod" in OCaml *)
val signed_modulo:
  v:int ->
  p:pos ->
  Tot (res:int{ res = v - ((div_non_eucl v p) * p) })
let signed_modulo v p =
  if v >= 0 then v % p
  else - ( (-v) % p)

val op_Plus_Percent : a:int -> p:pos -> 
  Tot (res:int{ (a >= 0 ==> res = a % p) /\ (a < 0 ==> res = -((-a) % p)) }) 
let op_Plus_Percent a p = signed_modulo a p

(* Bitwize operations *)
assume val xor_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> x = y })
assume val and_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> (x = 0 /\ y = 0)})
assume val or_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> (x = 0 \/ y = 0) })
assume val lnot_op: int -> Tot int

(* Comparison *)
(* To replace with something constant time in real code *)
val compare : x:int -> y:int -> Tot (r:int{ (r = 0 <==> x = y)
					    /\ (r = 1 <==> x > y)
					    /\ (r = -1 <==> x < y) })
let compare x y =
  if x = y then 0
  else if x < y then -1
  else 1

(*** Lemmas ***)

(* Lemma : pow2 is a stricly increasing function *) 
val pow2_increases_lemma:
  n:nat -> m:nat ->
  Lemma
    (requires (m < n))
    (ensures (pow2 m < pow2 n))
    (decreases (n-m))
let rec pow2_increases_lemma n m =
  match n-m with
  | 1 -> ()
  | _ -> pow2_increases_lemma (n-1) m; pow2_increases_lemma n (n-1)

(* Lemma : definition of the exponential property of pow2 *)
val pow2_exp_lemma:
  n:nat -> m:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 n * pow2 m = pow2 (n+m)))
let rec pow2_exp_lemma n m =
  match n with
  | 0 -> ()
  | _ -> pow2_exp_lemma (n-1) (m)

(* Lemma : definition of the exponential property of pow2 *)
val pow2_div_lemma:
  n:nat -> m:nat{ n >= m } -> 
  Lemma
    (requires (True))
    (ensures ((pow2 n) / (pow2 m) = pow2 (n-m)))
let pow2_div_lemma n m =
  (
    if n = m then ()
    else 
      (pow2_increases_lemma n m;
       pow2_exp_lemma (n-m) m;
       slash_star_axiom (pow2 (n-m)) (pow2 m) (pow2 n);
       ())
  )
(* Lemma : absolute value of product is the product of the absolute values *)
val abs_mul_lemma:
  a:int -> b:int ->
  Lemma
    (requires (True))
    (ensures ( abs ( a * b ) = abs a * abs b ))
let abs_mul_lemma a b = ()

(* Lemma : Non-euclidian division has a smaller output compared to its input *)
val div_non_eucl_decr_lemma:
  a:int -> b:pos ->
  Lemma
    (requires (True))
    (ensures (abs (div_non_eucl a b) <= abs a))
let div_non_eucl_decr_lemma a b =
  (slash_decr_axiom (abs a) b)

(* Lemma : dividing by a bigger value leads to 0 if non euclidian division *)
val div_non_eucl_bigger_denom_lemma:
  a:int -> b:pos ->
  Lemma
    (requires ( b > abs a ))
    (ensures ( div_non_eucl a b = 0 ))
let div_non_eucl_bigger_denom_lemma a b = ()

(* Lemma : the absolute value of a signed_module b is bounded by b *)
val signed_modulo_property:
  v:int ->
  p:pos ->
  Lemma
    (requires (True))
    (ensures ( abs (signed_modulo v p ) < p ))
let signed_modulo_property v p = ()

(* Lemma : loss of precision in euclidian division *)
val multiply_fractions_lemma:
  a:nat -> n:pos ->
  Lemma
    (requires (True))
    (ensures ( n * ( a / n ) <= a ))
let multiply_fractions_lemma a n =
  (euclidian_div_axiom a n)

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
val parenSub: a:int -> b:int -> c:int -> Lemma (requires (True))
					       (ensures (a - (b + c) = a - b - c /\ a - (b - c) = a - b + c))
let parenSub a b c = ()

(* TODO : fix log implementation, though should only be used in specs *)
(* WARNING : this is actually not the log, but rather the number of bits necessary to 
   represent the integer *)
(* TODO : change the name of the function *)

assume val log: x:pos -> Tot (n:nat{ x < pow2 n /\ (forall (i:nat). x < pow2 i ==> i >= n) })

(* TODO : prove lemma *)
assume val log_incr_lemma: a:pos -> b:pos -> Lemma (requires (a < b)) 

(* TODO : prove lemma *)
assume val log_lemma: a:pos -> b:pos -> Lemma (ensures (log (a * b) = log a + log b))
