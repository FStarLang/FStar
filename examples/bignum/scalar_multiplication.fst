(* STATUS : incomplete lemmas at the end of the file, see TODOS *)

module ScalarMultiplication

open IntLib
open Limb
open FStar.Seq
open Eval
open Axiomatic

val scalar_multiplication_lemma_aux:
  a:bigint ->
  b:bigint{ SameFormat a b } ->
  s:int ->
  len:pos{ len <= getLength a } ->
  Lemma
    (requires ( (eval a (len-1) * s = eval b (len-1))
		/\ (get a (len-1) * s = get b (len-1))))
    (ensures ( eval a len * s = eval b len ))
let scalar_multiplication_lemma_aux a b s len =
  paren_mul_left (pow2 (bitweight (getTemplate a) (len-1))) (get a (len-1)) s;
  distributivity_add_left ((pow2 (bitweight (getTemplate a) (len-1))) * (get a (len-1))) (eval a (len-1)) s

val scalar_multiplication_lemma:
  a:bigint -> 
  b:bigint{ SameFormat a b } -> 
  s:int ->
  len:nat{ len <= getLength a } ->
  Lemma
    (requires ( forall (i:nat). i < len ==> get a i * s = get b i ))
    (ensures ( eval a len * s = eval b len ))
let rec scalar_multiplication_lemma a b s len =
  match len with
  | 0 -> ()
  | _ -> scalar_multiplication_lemma a b s (len-1); scalar_multiplication_lemma_aux a b s len

val scalar_multiplication_aux:
  a:bigint{ maxSize a <= (maxLimbSize a) / 2 } ->
  n:nat{ n <= (maxLimbSize a) / 2 } ->
  s:lint n ->
  len:nat{ len <= getLength a } ->
  c:larray (maxLimbSize a){ (length c = getLength a)
			    /\ (forall (i:nat).
				(len <= i /\ i < length c) ==> 
				  ( (index c i = get a i * s)
				    /\ (Bitsize (index c i) (getSize a i + n)))) } -> 
  Tot (b:bigint{ (SameFormat a b)
		    /\ (forall (i:nat). i < getLength b ==> 
			  ((get a i * s = get b i)
			   /\ (getSize b i = getSize a i + n))) })
let rec scalar_multiplication_aux a n s len c =
  match len with
  | 0 -> 
     let data = c in
     let t = getTemplate a in
     let (size:template) = fun (i:nat) -> if i >= length c then 0 else getSize a i + n in
     Bigint64 data t size true
  | _ -> 
     let i = len-1 in
     let ai = get a i in
     let size_ai = getSize a i in
     let v = mul size_ai ai n s in
     order_n_bits v (size_ai+n) (maxLimbSize a);
     let c = upd c i v in
     scalar_multiplication_aux a n s (len-1) c

val scalar_multiplication :
  a:bigint{ maxSize a <= (maxLimbSize a) / 2 } ->
  n:nat{ n <= (maxLimbSize a) / 2 } ->
  s:lint n ->
  Tot (b:bigint{ (SameFormat a b)
		    /\ (forall (i:nat). i < getLength b ==> 
			  ((get a i * s = get b i)
			   /\ (getSize b i = getSize a i + n))) })
let scalar_multiplication a n s =
  let c = create (getLength a) zero in
  scalar_multiplication_aux a n s (getLength a) c
     	 
val theorem_scalar_multiplication: 
  a:bigint{ maxSize a <= (maxLimbSize a) / 2 } ->
  n:nat{ n <= (maxLimbSize a) / 2 } ->
  s:lint n ->
  len:nat{len <= getLength a} -> 
  Lemma 
    (requires (True))
    ( ensures ( (eval (scalar_multiplication a n s) len) = (eval a len) * s ) )
    [SMTPat (scalar_multiplication a n s)]
let theorem_scalar_multiplication a n s len = 
  scalar_multiplication_lemma a (scalar_multiplication a n s) s len; ()

(* TODO : prove *)
assume val scalar_multiplication_max_value_lemma:
  a:bigint{ maxSize a <= (maxLimbSize a) / 2 } ->
  n:nat{ n <= (maxLimbSize a) / 2 } ->
  s:lint n ->
  Lemma
    (requires (True))
    (ensures ( maxValue (scalar_multiplication a n s) = maxValue a * (abs s) ))
    [SMTPat (scalar_multiplication a n s)]
//let scalar_multiplication_max_value_lemma a n s = ()

val scalar_multiplication_max_size_lemma:
  a:bigint{ maxSize a <= (maxLimbSize a) / 2 } ->
  n:nat{ n <= (maxLimbSize a) / 2 } ->
  s:lint n ->
  Lemma
    (requires (True))
    (ensures ( maxSize (scalar_multiplication a n s) = maxSize a + n ))
    [SMTPat (scalar_multiplication a n s)]
let scalar_multiplication_max_size_lemma a n s = ()


	       
