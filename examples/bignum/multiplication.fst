#include "preproc.h"

(* STATUS : verifies but still a couple of missing lemmas *)
(* TODO : improve the readability / elegance of the proofs *)

module Multiplication

open IntLib
open Limb
open FStar.Seq
open Eval
open Addition
open ScalarMultiplication
open ShiftArray
open Axiomatic

(* Verification query :
fstar.exe $FSTAR_HOME/lib/seq.fsi --admit_fsi Seq axiomatic.p.fst intlib.fst limb.fst eval.fst addition.fst shift_array.fst scalar_multiplication.fst multiplication.fst --verify_module Multiplication
 *)

(* Helper lemmas that avoid super long computation or intensive use of "cuts" *)
val helper_lemma_0 : 
  a:int -> b:int -> c:int -> 
  Lemma
    (requires (True))
    (ensures ( a - c - b + c = a - b ))
let helper_lemma_0 a b c = ()

val helper_lemma_1 : a:int -> Lemma (ensures (1 * a = a))
let helper_lemma_1 a = ()

val helper_lemma_2 : a:nat -> Lemma (ensures (a + a = 2 * a))
let helper_lemma_2 a = ()

type norm_bigint = a:bigint{ (forall (n:nat). getTemplate a n = getTemplate a 0) }

val max_size_lemma:
  a:bigint -> l:nat ->
  Lemma
    (requires (l >= maxSize a))
    (ensures ( forall (n:nat). n < getLength a ==> getSize a n <= l ))
let max_size_lemma a l = ()

val size_lemma_1:
  a:nat -> b:nat ->
  Lemma
    (requires (True))
    (ensures (size ( a * b ) <= size a + size b ))
let size_lemma_1 a b =
  if a = 0 then ()
  else if b = 0 then ()
  else log_lemma a b

val size_lemma_2:
  a:bigint -> x:nat -> n:nat ->
  Lemma
    (requires (maxValue a <= x * (pow2 n))) 
    (ensures ( forall (i:nat). i < getLength a ==> Bitsize (get a i) (size x + n) ))
let size_lemma_2 a x n =
  cut (x < pow2 (size x) /\ True );
  pow2_exp_lemma (size x) n;
  cut ( pow2 (size x) * (pow2 n) = pow2 (size x + n) /\ True );
  mul_pos_strict_incr_lemma (pow2 n) x (pow2 (size x));
  cut ( maxValue a < pow2 (size x + n) /\ True );
  cut ( forall (i:nat). i < getLength a ==> Bitsize (get a i) (size x + n) /\ True );
  ()

val size_lemma_3:
	 a:nat -> b:nat -> 
	 Lemma
	   (requires (a <= b))
	   (ensures (size a <= size b))
let size_lemma_3 a b =
  if a = 0 then ()
  else if a < b then log_incr_lemma a b
  else ()

val helper_lemma_3:
	 a:nat -> b:nat -> c:nat -> d:nat ->
	 Lemma
	   (requires ( a <= c /\ b <= d ))
	   (ensures ( a*b <= c*d ))
let helper_lemma_3 a b c d =
  mul_incr_lemma a b d;
  assert ( a * b <= a * d );
  swap_mul a d;
  swap_mul c d;
  mul_incr_lemma d a c;
  ()

val helper_lemma_4:
  a:nat -> b:nat -> Lemma (ensures ( a * b >= 0 ))
let helper_lemma_4 a b = ()
			   
RESET

val auxiliary_lemma_2:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) - 1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) - 1 ) / 2) } ->
  ctr:nat{ (ctr <= getLength a) } ->
  c:bigint{ (maxValue c <= ctr * (maxValue a * maxValue b)) } ->
  Lemma
    (requires (True))
    (ensures ((maxValue a <= pow2 ((maxLimbSize a - log (getLength a) - 1) / 2 )) 
	    /\ (maxValue b <= pow2 ((maxLimbSize b - log (getLength b) - 1) / 2 ))))

let auxiliary_lemma_2 a b ctr c =
  cut ( maxValue a <= pow2 (maxSize a) /\ True );
  if (((maxLimbSize a - log (getLength a) - 1) / 2) > (maxSize a)) then
    pow2_increases_lemma ((maxLimbSize a - log (getLength a) - 1) / 2) (maxSize a);
  if (((maxLimbSize b - log (getLength b) - 1) / 2) > (maxSize b)) then
    pow2_increases_lemma ((maxLimbSize b - log (getLength b) - 1) / 2) (maxSize b);
  cut (pow2 (maxSize a) <= pow2 ((maxLimbSize a - log (getLength a) - 1) / 2) /\ True );
  cut (maxValue a <= pow2 (maxSize a) /\ True );
  cut (maxValue a <= pow2 ((maxLimbSize a - log (getLength a) - 1) / 2 ) /\ True );
  cut (pow2 (maxSize b) <= pow2 ((maxLimbSize b - log (getLength b) - 1) / 2) /\ True );
  cut (maxValue b <= pow2 (maxSize b) /\ True );
  cut (maxValue b <= pow2 ((maxLimbSize b - log (getLength b) - 1) / 2 ) /\ True )

RESET

val auxiliary_lemma_3:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) - 1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) - 1 ) / 2) } ->
  ctr:nat{ (ctr <= getLength a) } ->
  c:bigint{ (maxValue c <= ctr * (maxValue a * maxValue b)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue a * maxValue b <= pow2 (maxLimbSize a - log (getLength a) - 1)))

let auxiliary_lemma_3 a b ctr c =
  auxiliary_lemma_2 a b ctr c;
  let s = (maxLimbSize a - log (getLength a) - 1) in
  cut (maxLimbSize b - log (getLength b) - 1 = s /\ True);
  helper_lemma_3 (maxValue a) (maxValue b) (pow2 ((maxLimbSize a - log (getLength a) -1)/2)) (pow2 ((maxLimbSize b - log (getLength b) -1)/2));
  pow2_exp_lemma (s/2) (s/2);
  cut (maxValue a * maxValue b <= pow2 ((s/2)+(s/2)) /\ True);
  helper_lemma_2 (s/2);
  multiply_fractions_lemma s 2;
  cut ((s / 2)+(s/2) <= (s) /\ True);
  if (((s/2)+(s/2)) < s ) then
    pow2_increases_lemma s ((s/2)+(s/2));
  cut (pow2 (((s/2)+(s/2))) <= pow2 s /\ True);
  cut (maxValue a * maxValue b <= pow2 s /\ True);
  ()

RESET

(* Changes the "size" parameter of the bigint to a tighter value *)
val auxiliary_function_1:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) - 1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) - 1 ) / 2) } ->
  ctr:pos{ (ctr <= getLength a) } ->
  c:bigint{ (maxValue c <= ctr * (maxValue a * maxValue b)) } ->
  Tot (d:bigint{ (EqualBigint c d)
		 /\ (getSign d = getSign c)
		 /\ (maxSize d <= maxLimbSize b - 1) } )

let auxiliary_function_1 a b ctr c =
  let s = (maxLimbSize a - log (getLength a) - 1) in
  auxiliary_lemma_3 a b ctr c;
  cut ( maxValue a * maxValue b <= pow2 s /\ True );
  helper_lemma_4 (maxValue a) (maxValue b);
  mul_incr_lemma ctr (maxValue a * maxValue b) (pow2 s);
  cut ( maxValue c <= ctr * pow2 s /\ True );
  size_lemma_2 c ctr s;
  cut ( forall (i:nat). i < getLength c ==> Bitsize (get c i) (size ctr + s) );
  if ctr < getLength a then log_incr_lemma ctr (getLength a);
  cut (size ctr + s <= maxLimbSize a - 1 /\ True );
  if (size ctr + s < maxLimbSize a - 1) then pow2_increases_lemma (maxLimbSize a - 1) (size ctr + s);
  cut ( forall (i:nat). i < getLength c ==> Bitsize (get c i) (maxLimbSize a - 1) );
  let (size:template) = fun (n:nat) -> maxLimbSize a - 1 in
  let res = Bigint64 (getData c) (getTemplate c) size (getSign c) in
  cut (maxSize res = maxLimbSize a - 1 /\ True );
  res

RESET

val multiplication_step:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) - 1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) - 1 ) / 2) } ->
  ctr:nat{ (ctr < getLength a) } ->
  c:norm_bigint{ (getLength c = (2 * (getLength a)) - 1 )
		 /\ (getTemplate c = getTemplate a)
		 /\ (maxSize c <= (maxLimbSize b - 1))
		 /\ (maxValue c <= ctr * (maxValue a * maxValue b)) } ->
  Tot (d:norm_bigint{ 
	   (SameFormat c d)  
	   /\ ( maxValue d <= (ctr+1) * (maxValue a * maxValue b))
	   /\ ( maxSize d <= (maxLimbSize b - 1))
	   /\ ( eval d (getLength d) = (eval a (getLength a) * (get b ctr)) * (pow2 (bitweight (getTemplate a) ctr)) + eval c (getLength c)) }) 
 
let multiplication_step a b ctr c =
  let s = get b ctr in
  max_size_lemma a ((maxLimbSize a)/2);
  cut ( (forall (n:nat). n < getLength a ==> getSize a n <= maxLimbSize a / 2) );
  let sa = scalar_multiplication a (getSize b ctr) s in
  theorem_scalar_multiplication a (getSize b ctr) s (getLength a);
  cut ( eval sa (getLength sa) = eval a (getLength a) * s /\ True);
  let tmp = extendTo sa ((2 * getLength a - ctr) - 1) in
  extendTo_lemma a ((2 * getLength a - ctr)-1);
  cut ( eval tmp (getLength tmp) = eval sa (getLength sa) /\ True );
  let tmp2 = shift_array tmp ctr in
  theorem_shift_array tmp ctr;
  cut ( eval tmp2 (getLength tmp2) = eval tmp (getLength tmp) * (pow2 (bitweight (getTemplate a) ctr)) /\ True);
  helper_lemma_0 (2 * getLength a) 1 ctr;
  cut ( SameFormat tmp2 c /\ True );
  cut ( maxValue tmp2 = maxValue tmp /\ True );
  cut ( maxValue tmp = maxValue a * abs s /\ True);
  cut ( abs s <= pow2 (maxSize b) /\ True);
  multiply_fractions_lemma (maxLimbSize a - log (getLength a)) 2;
  cut ( maxSize tmp <= maxLimbSize a - log (getLength a) /\ True );
  cut ( maxSize tmp2 = maxSize tmp /\ True) ;
  cut ( maxValue tmp2 <= maxValue a * abs s /\ True );
  cut ( abs s <= maxValue b /\ True );
  mul_incr_lemma (maxValue a) (abs s) (maxValue b);
  cut ( maxValue tmp2 <= maxValue a * maxValue b /\ True );
  cut ( maxSize tmp2 <= maxLimbSize tmp2 - log (getLength a) - 1 /\ True );
  cut ( maxSize c <= maxLimbSize tmp2 - 1 /\ True );
  let res = addition tmp2 c in
  addition_max_value_lemma tmp2 c;
  cut ( maxValue res <= maxValue tmp2 + maxValue c /\ True);
  cut ( maxValue res <= (maxValue a * maxValue b) + ctr * (maxValue a * maxValue b) /\ True );
  helper_lemma_1 (maxValue a * maxValue b);
  cut ( (maxValue a * maxValue b) + ctr * (maxValue a * maxValue b) = 1 * (maxValue a * maxValue b) + ctr * (maxValue a * maxValue b) /\ True );
  distributivity_add_left 1 ctr (maxValue a * maxValue b);
  cut ( maxValue res <= (ctr + 1) * (maxValue a * maxValue b) /\ True );
  theorem_addition tmp2 c (getLength tmp2);
  cut ( eval res (getLength res) = eval tmp2 (getLength tmp2) + eval c (getLength c) /\ True );
  cut ( eval res (getLength res) = (eval a (getLength a) * (get b ctr)) * (pow2 (bitweight (getTemplate a) ctr)) + eval c (getLength c) /\ True );
  let d = auxiliary_function_1 a b (ctr+1) res in
  maxValue_eq_lemma d res;
  eval_equal_lemma d res;
  d
  

RESET

val multiplication_step_lemma_1:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) -1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) -1 ) / 2) } ->
  ctr:pos{ (ctr <= getLength a) } ->
  c:norm_bigint{ (getLength c = 2 * (getLength a) - 1)
		 /\ (getTemplate c = getTemplate a)  } ->
  Lemma 
    (requires ( 
	 eval c (getLength c) =
	   ((eval a (getLength a)) * (get b (getLength a - ctr))) * (pow2 (bitweight (getTemplate a) (getLength a - ctr))) 
	   + (eval a (getLength a)) * (eval b (getLength a - ctr))))
    (ensures (
	 eval c (getLength c) = 
	   (eval a (getLength a)) * ((pow2 (bitweight (getTemplate a) (getLength a - ctr))) * (get b (getLength a - ctr)) + (eval b (getLength a - ctr))) ))

let multiplication_step_lemma_1 a b ctr c =
  let t = getTemplate a in
  let lena = getLength a in
  paren_mul_left (eval a lena) (get b (lena - ctr)) (pow2 (bitweight t (lena - ctr)));
  assert (  eval c (getLength c) =
	      (eval a (getLength a)) * (get b (getLength a - ctr)) * (pow2 (bitweight (getTemplate a) (getLength a - ctr)))  
	   + ((eval a (getLength a)) * (eval b (getLength a - ctr)))) ;
  swap_mul (get b (lena - ctr)) (pow2 (bitweight t (lena - ctr)));
  assert (  eval c (getLength c) =
	      (eval a (getLength a)) * (pow2 (bitweight (getTemplate a) (getLength a - ctr))) * (get b (getLength a - ctr))  
	   + ((eval a (getLength a)) * (eval b (getLength a - ctr)))) ;
  distributivity_add_right (eval a lena) ((pow2 (bitweight t (lena - ctr))) * (get b (lena - ctr))) (eval b (lena - ctr));
  assert (  eval c (getLength c) =
	      (eval a (getLength a)) * ( (pow2 (bitweight (getTemplate a) (getLength a - ctr))) * (get b (getLength a - ctr))  
	   + (eval b (getLength a - ctr))) ) ;
  () 

RESET

val multiplication_step_lemma:
  a:norm_bigint{ (maxLimbSize a >= log (getLength a) + 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) -1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) -1 ) / 2) } ->
  ctr:pos{ (ctr <= getLength a) } ->
  c:norm_bigint{ (getLength c = 2 * (getLength a) - 1)
	    /\ (getTemplate c = getTemplate a)  } ->
  Lemma (requires ( eval c (getLength c) =
		      ((eval a (getLength a)) * ((get b (getLength a - ctr)))) * (pow2 (bitweight (getTemplate a) (getLength a - ctr))) + (eval a (getLength a)) * (eval b (getLength a - ctr))))
	(ensures ( eval c (getLength c) = (eval a (getLength a)) * (eval b ((getLength a - ctr) + 1))))

let multiplication_step_lemma a b ctr c =
  multiplication_step_lemma_1 a b ctr c;
  ()


RESET

val multiplication_aux: 
  a:norm_bigint{ (log (getLength a) <= maxLimbSize a - 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) -1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) -1 ) / 2) } ->
  ctr:nat{ (ctr <= getLength a) } ->
  c:norm_bigint{ (getLength c = 2 * (getLength a) - 1) 
		 /\ (maxSize c <= (maxLimbSize b - 1))
		 /\ (maxValue c <= (getLength a - ctr) * (maxValue a * maxValue b))
		 /\ (getTemplate c = getTemplate a)
		 /\ (eval c (getLength c) = (eval a (getLength a)) * (eval b (getLength a - ctr))) } ->
  Tot (d:norm_bigint{ (SameFormat c d)
		      /\ (eval d (getLength d) = eval a (getLength a) * (eval b (getLength b))) })

let rec multiplication_aux a b ctr c = 
  match ctr with
  | 0 -> 
     c
  | _ -> 
     let i = getLength b - ctr in
     let c' = multiplication_step a b i c in     
     multiplication_step_lemma a b ctr c';
     assert ( getLength c' = 2 * getLength a - 1 );
     assert ( (maxSize c' <= (maxLimbSize b - 1)) );
     assert ( (maxValue c' <= (getLength a - ctr + 1) * (maxValue a * maxValue b)));
     parenSub (getLength a) ctr 1;
     assert ( (maxValue c' <= (getLength a - (ctr-1)) * (maxValue a * maxValue b) ));
     multiplication_aux a b (ctr-1) c'

RESET

val multiplication: 
  a:norm_bigint{ (log (getLength a) <= maxLimbSize a - 1)
		 /\ (maxSize a <= (maxLimbSize a - log (getLength a) -1 ) / 2) } ->
  b:norm_bigint{ (SameFormat a b)
		 /\ (maxSize b <= (maxLimbSize b - log (getLength b) -1 ) / 2) } ->
  Tot (c:norm_bigint{ (getLength c = (2 * (getLength a) - 1))
		    /\ ((eval c (getLength c)) = (eval a (getLength a)) * (eval b (getLength b)) ) })

let multiplication a b =
  let data = create (2 * (getLength a) - 1) zero in
  let t = getTemplate a in
  let (size:template) = fun (x:nat) -> 0 in
  let c = Bigint64 data t size true in
  (* To show required equality on maxValue *)
  cut ( maxValue c = 0 /\ True );
  cut (getLength a - getLength a = 0 /\ True );
  cut ( 0 * (maxValue a * maxValue b) = 0 /\ True );
  cut ( (getLength a - getLength a ) * (maxValue a * maxValue b) = 0 /\ True );
  (* To show required equality on eval *) 
  cut ( eval c (getLength c) = 0 /\ True );
  cut ( eval b 0 = 0 /\ True );
  cut ( eval a (getLength a) * 0 = 0 /\ True );
  cut ( eval c (getLength c) = (eval a (getLength a)) * eval b 0 /\ True );
  multiplication_aux a b (getLength a) c
