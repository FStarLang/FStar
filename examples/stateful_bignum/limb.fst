(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Limb;
  other-files:classical.fst seq.fsi seqproperties.fst set.fsi heap.fst st.fst all.fst ghost.fst axiomatic.fst intlib.fst;
  --*)

(* 
  This file contains functions and lemmas related to memory safety when 
  manipulating "concrete" integers which may overflow.
  The key predicate is "Bitsize x n" which implies that -2^n < x < 2^n.
  This predicate is used instead of the following : -2^n <= x < 2^n because it
  makes a lot of things simpler.

  Safe add, sub and mult functions are defined here.
 *)
(* 
  STATUS : remaining unproved lemmas (grep for TODO, assume and admit)
 *)

module Limb

open IntLib
open Axiomatic
open FStar.Ghost
open FStar.Seq

let max_size = 63

(* Represents the number of bits (-1) the integer fits in *)
type Bitsize (x:int) (n:nat) = -(pow2 n) < x /\ x < pow2 n
type GBitsize (x:erased int) (n:nat) = -(pow2 n) < reveal x /\ reveal x < pow2 n

(* Integer Types *)
type ulint (n:nat) = x:nat{ Bitsize x n }
type lint (n:nat) = x:int{ Bitsize x n } 

(* Standard definitions ? *)
type int64 = lint 63
type limb = int64
type uint64 = ulint 64
type int32 = lint 31
type uint32 = ulint 32

(* Bounded integer arrays *)
(* TODO : move those to the Limb module *)
type larray (n:nat) = s:seq int{ (forall (i:nat). i< length s ==> Bitsize (index s i) n) }
type ularray (n:nat) = s:seq nat{ (forall (i:nat). i < length s ==> Bitsize (index s i) n) }

(* These casts should be transformed directly into C casts when applied to n = 32 or n = 64 for instance *)
(* General cast functions from int to nint and nuint *)
val to_uintn: x:int -> n:nat -> Tot (y:ulint n{ y = x % (pow2 n)})
let to_uintn x n = x % (pow2 n)

val to_intn: 
  x:int -> n:pos ->
  Tot (y:lint n{ (x % pow2 n >= pow2 (n-1) ==> y = (x % pow2 n) - pow2 n ) 
	       /\ (x % pow2 n < pow2 (n-1) ==> y = x % pow2 n) })
let to_intn x n =
  let res = x % (pow2 n) in
  if res >= (pow2 (n-1)) then res - (pow2 n)
  else res


(* ---------------------------------------------------- *)
(* Series of lemmas on the bit size of different values *)
(* ---------------------------------------------------- *)

val size_of_add_lemma:
  n:nat -> a:lint n -> m:nat -> b:lint m ->
  Lemma
    (requires (True))
    (ensures (Bitsize (a+b) ((max n m)+1)))
let size_of_add_lemma n a m b =
    if n < m then pow2_increases_lemma m n
    else 
      if m < n then pow2_increases_lemma n m
      else ();
    pow2_increases_lemma ((max n m)+1) (max n m)
  
val size_of_sub_lemma:
  n:nat -> a:lint n -> m:nat -> b:lint m ->
  Lemma 
    (requires (True))
    (ensures ( Bitsize (a-b) ((max m n)+1) ))
let size_of_sub_lemma n a m b =
  if n < m then pow2_increases_lemma m n
    else 
      if m < n then pow2_increases_lemma n m
      else ();
	 pow2_increases_lemma ((max n m)+1) (max n m)

val size_of_mul_lemma:
  n:nat -> a:lint n -> m:nat -> b:lint m ->
  Lemma
    (requires (True))
    (ensures (Bitsize (a*b) (n+m)))	       
let size_of_mul_lemma n a m b = 
    pow2_exp_lemma n m;
    mul_ineq1 a (pow2 n) b (pow2 m)
    
val size_of_mul_by_pow2_lemma:
  n:nat -> a:lint n -> m:nat ->
  Lemma
    (requires (True))
    (ensures (Bitsize (a * (pow2 m)) (n+m) /\ Bitsize ((pow2 m) * a) (n+m)))
let size_of_mul_by_pow2_lemma n a m = 
 (pow2_exp_lemma n m)

val size_of_div_non_eucl:
  n:nat -> a:lint n -> b:pos ->
  Lemma
    (requires (True))
    (ensures (Bitsize (div_non_eucl a b) n))
let size_of_div_non_eucl n a b =
 (div_non_eucl_decr_lemma a b)

(* The difference between the euclidian and non euclidian division should be handled with care *)
(* TODO *)
assume val div_non_eucl_monotonous_lemma : 
	 a:int -> b:int -> c:pos -> 
	 Lemma
	   (requires (a < b))
	   (ensures (div_non_eucl a c <= div_non_eucl b c ))

(* TODO *)
assume val size_of_div_non_eucl_by_pow2:
  n:nat -> a:lint n -> m:nat ->
  Lemma
    (requires (True))
    (ensures (Bitsize (div_non_eucl a (pow2 m)) (max 0 (n-m))))

(* TODO *)
assume val size_of_div_by_pow2:
  n:nat -> a:lint n -> m:nat ->
  Lemma
    (requires (True))
    (ensures (Bitsize (div a (pow2 m)) (max 0 (n-m))))

val size_of_modulo_pow2:
  a:int -> n:nat ->
  Lemma
    (requires (True))
    (ensures (Bitsize (a % (pow2 n)) n))
    [SMTPat (a % (pow2 n))]
let size_of_modulo_pow2 a n = ()

assume val size_of_signed_modulo_by_pow2:
    a:int -> n:nat -> 
	 Lemma
	   (requires (True))
	   (ensures (Bitsize (signed_modulo a (pow2 n)) n))
	   [SMTPat (signed_modulo a (pow2 n))]

(* True but big loss of precision *)
val bits_of_pow2:
   n:nat ->
   Lemma 
     (requires (True))
     (ensures ( Bitsize (pow2 n) (n+1) /\ Bitsize (-(pow2 n)) (n+1) ))
let bits_of_pow2 n =
 (pow2_increases_lemma (n+1) n)

val order_n_bits:
  x:int -> n:nat -> m:nat ->
  Lemma
    (requires (n <= m /\ Bitsize x n))
    (ensures ( Bitsize x m ))
let order_n_bits x n m =
 (
    if n = m then ()
    else pow2_increases_lemma m n
  )

val bitsize_inverse_lemma:
  n:nat -> a:lint n ->
  Lemma
    (requires (True))
    (ensures (Bitsize (-a) n)) 
let bitsize_inverse_lemma a n = ()

val size_of_signed_modulo_lemma:
  v:int -> n:nat ->
  Lemma
    (requires (True))
    (ensures ( Bitsize (signed_modulo v (pow2 n)) n))
    [SMTPat (signed_modulo v (pow2 n))]
let size_of_signed_modulo_lemma v n = ()

(* ---------------------------------------------------- *)
(*                  SAFE FUNCTIONS                      *)
(* ---------------------------------------------------- *)

(* Safe addition taking the integer size into account *)
val add:
  n:nat -> a:lint n -> m:nat -> b:lint m{ (max n m)+1 <= max_size } ->
  Tot (c:lint ((max n m)+1){ c = a + b })
let add n a m b = 
 (size_of_add_lemma n a m b);
  a + b

(* Safe substraction taking the integer size into account *)
val sub:
  n:nat -> a:lint n -> m:nat -> b:lint m{ (max n m)+1 <= max_size } ->
  Tot (c:lint ((max n m) +1){ c = a - b })
let sub n a m b = 
 (size_of_sub_lemma n a m b);
  a - b

(* Safe multiplication taking the integer size into account *)
val mul :
  n:nat -> a:lint n -> m:nat -> b:lint m{ (n+m) <= max_size } ->
  Tot (c:lint (n+m){ c = a * b })
let mul  n a m b =
 (size_of_mul_lemma n a m b);
  a * b

assume val shift_left :
  n:nat -> a:lint n -> shift:nat{ n + shift <= max_size } ->
  Tot (c:lint (n+shift){ c = pow2 shift * a })

val one: one:lint 1{ one = 1 }
let one = 1

val zero: z:lint 0{ z = 0 }
let zero = 0

(* ---------------------------------------------------- *)
(*          SAFE FUNCTIONS RELATED LEMMAS               *)
(* ---------------------------------------------------- *)


(* Tighter bound on the result of the sum with a positive and a negative term *)
(* TODO *)
assume val add_negative:
  n:nat -> a:lint n -> m:nat{(max n m)+1 <= max_size} -> b:lint m ->
  Lemma
    (requires ( (a < 0 /\ b >= 0) \/ (a >= 0 /\ b < 0) ))
    (ensures ( add n a m b = a + b /\ Bitsize (add n a m b) (max m n) ))

(* TODO *)
assume val add_bigger_pow2:
  n:nat -> a:lint n -> m:pos ->
  Lemma
    (requires ( m > n ))
    (ensures ( a + pow2 m >= pow2 (m-1) )) 

val add_commutative:
  n:nat -> a:lint n -> m:nat{(max n m)+1 <= max_size} -> b:lint m ->
  Lemma
    (requires (True))
    (ensures ( add n a m b = add m b n a ))
let add_commutative n a m b = ()
