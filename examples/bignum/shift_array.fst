(* STATUS : lemmas to prove at the end of the file, see TODOS *)

module ShiftArray

open IntLib
open Limb
open Seq
open Eval
open Axiomatic

val swap_add_plus_minus:
  a:int -> b:int -> c:int ->
  Lemma (requires (True))
	(ensures ( a + b - c = (a - c) + b ))
let swap_add_plus_minus a b c = ()

val shift_array: 
  a:bigint -> 
  shift:nat -> 
  Tot (c:bigint{ (getLength c = getLength a + shift)
		 /\ (getTemplate c = getTemplate a)
		 /\ (forall (j:nat).
		     (j < getLength a ==> get c (j+shift) = get a j)
		     /\ (j < shift ==> get c j = 0)) })
let shift_array a shift =
  let data = append (create shift 0) (getData a) in
  let t = getTemplate a in
  let (size:template) =
    fun n -> if n < shift then zero
	     else if n >= length data then zero
	     else getSize a (n-shift) in
  Bigint64 data t size true

val const_sum_lemma:
  t:template ->
  n:nat ->
  Lemma
    (requires ( forall (i:nat). t i = t 0 ))
    (ensures ( bitweight t n = n * (t 0) ))
    [SMTPat (bitweight t n)]
let rec const_sum_lemma t n =
  match n with
  | 0 -> ()
  | _ -> 
     const_sum_lemma t (n-1)

val pow2_const_template_lemma:
  a:bigint{ forall (i:nat). getTemplate a i = getTemplate a 0 } ->
  n:nat -> 
  m:nat -> 
  Lemma
    (requires (True))
    (ensures ( pow2 (bitweight (getTemplate a) (n+m)) = pow2 (bitweight (getTemplate a) n) * pow2 (bitweight (getTemplate a) m)) )
let pow2_const_template_lemma a n m =
  let t = getTemplate a in
  let c = t 0 in
  distributivity_add_left n m c;
  pow2_exp_lemma (bitweight t n) (bitweight t m)

val shift_array_lemma_aux: 
  a:bigint{ forall (n:nat). getTemplate a n = getTemplate a 0 } -> 
  len:nat{ len >= 1 /\ len <= getLength a } -> 
  i:nat -> 
  b:bigint{ (getLength b = getLength a + i)
	    /\ (getTemplate a = getTemplate b) } ->
  Lemma 
    (requires ( (eval b (len+i-1) = (eval a (len-1)) * (pow2 (bitweight (getTemplate a) i)))
		/\ ( get b (len+i-1) = get a (len-1) ) ))
    (ensures ( eval b (len+i) = (eval a len) * (pow2 (bitweight (getTemplate a) i)) ) )
let shift_array_lemma_aux a len i b = 
  let t = getTemplate a in
  pow2_const_template_lemma a (len-1) i;
  paren_mul_left (pow2 (bitweight t (len-1))) (pow2 (bitweight t i)) (get b (len+i-1));
  //swap_add_plus_minus len i 1;
  swap_mul (pow2 (bitweight t i)) (get a (len-1));
  paren_mul_left (pow2 (bitweight t (len-1))) (get a (len-1)) (pow2 (bitweight t i));
  distributivity_add_left (pow2 (bitweight t (len-1)) * get a (len-1)) (eval a (len-1)) (pow2 (bitweight t i))

val shift_array_lemma : 
  a:bigint{ forall (n:nat). getTemplate a n = getTemplate a 0 } -> 
  len:nat{ len <= getLength a } -> 
  i:nat -> 
  b:bigint{ (getLength b = getLength a + i) 
	    /\ (getTemplate b = getTemplate a)
		 /\ (forall (j:nat).
		     (j < getLength a ==> get b (j+i) = get a j)
		     /\ (j < i ==> get b j = 0)) } ->
  Lemma 
    (requires (True))
    (ensures ( ( eval b (len+i) ) = (eval a len) * (pow2 (bitweight (getTemplate a) i)) ) )
let rec shift_array_lemma a len i b = 
  match len with
  | 0 -> eval_of_zero b i
  | _ ->
     let t = getTemplate a in
     shift_array_lemma a (len-1) i b ; 
     //swap_add_plus_minus len i 1;
     shift_array_lemma_aux a len i b 

val theorem_shift_array:
  a:bigint{ forall (n:nat). getTemplate a n = getTemplate a 0 } -> 
  i:nat -> 
  Lemma 
    (requires (True))
    (ensures ( eval (shift_array a i) (getLength a + i) = eval a (getLength a) * (pow2 (bitweight (getTemplate a) i)) ) )
    [SMTPat (shift_array a i)]
let theorem_shift_array a i =
  shift_array_lemma a (getLength a) i (shift_array a i)

val shift_array_max_value_lemma:
  a:bigint{ forall (n:nat). getTemplate a n = getTemplate a 0 } -> 
  i:nat -> 
  Lemma
    (requires (True))
    (ensures ( maxValue (shift_array a i) = maxValue a ))
    [SMTPat (shift_array a i)]
let shift_array_max_value_lemma a i = ()

val shift_array_max_size_lemma:
  a:bigint{ forall (n:nat). getTemplate a n = getTemplate a 0 } -> 
  i:nat -> 
  Lemma
    (requires (True))
    (ensures ( maxSize (shift_array a i) = maxSize a ))
    [SMTPat (shift_array a i)]
let shift_array_max_size_lemma a i = ()


