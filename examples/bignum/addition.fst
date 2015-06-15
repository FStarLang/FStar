#include "preproc.h"

module Addition

open IntLib
open Limb
open Seq
open Eval
open Axiomatic

(* TODO : incomplete lemmas at the end, see TODOS *)
(* 
   Auxiliary addition function. 
   Takes two input arrays, the current index for the computation and the temporary result 
 *)
val addition_aux:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } -> 
  b:bigint{ (SameFormat a b)
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  len:nat{ len <= getLength a } ->
  c:larray (maxLimbSize a){ (length c = getLength a)
	       /\ (forall (i:nat). 
                   ( len <= i /\ i < length c) ==> 
                     ( (index c i = get a i + get b i)
		       /\ (Bitsize (index c i) ((max (getSize a i) (getSize b i))+1)))) } ->
  Tot (d:bigint{ (SameFormat a d)
		 /\ (forall (i:nat). (i < getLength d) ==> 
		       ((get d i = get a i + get b i)
			/\ (getSize d i = 1 + max (getSize a i) (getSize b i)))) })
let rec addition_aux a b len c =
  match len with
  | 0 -> 
     let data = c in
     let t = getTemplate a in
     let (size:template) = fun (i:nat) -> if i >= length c then 0 else 1 + max ((getSize a) i) ((getSize b) i) in
     Bigint64 data t size true
  | _ ->
     (
       let i = len - 1 in
       let ai = get a i in
       let bi = get b i in
       let size_ai = (getSize a) i in
       let size_bi = (getSize b) i in
       let v = add size_ai ai size_bi bi in
       order_n_bits v ((max size_ai size_bi)+1) (maxLimbSize a);
       let c = upd c i v in
       addition_aux a b i c
     )
       (* | Other bigint constructors *)
  
val addition:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } ->
  b:bigint{ (SameFormat a b) 
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  Tot (c:bigint{ (SameFormat a c)
		 /\ (forall (i:nat). (i < getLength c) ==> 
		       ((get c i = get a i + get b i)
			/\ (getSize c i = 1 + max (getSize a i) (getSize b i))))})
let addition a b =
  let c = create (getLength a) zero in
  addition_aux a b (getLength a) c 

val addition_lemma_aux:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } -> 
  b:bigint{ (SameFormat a b) 
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  len:nat{ len >= 1 /\ len <= getLength a } ->
  c:bigint{ (SameFormat a c)
	    /\ (forall (i:nat). i < len ==> get c i = get a i + get b i) } ->
  Lemma
    (requires ( (eval a (len-1) + eval b (len-1) = eval c (len-1))
		/\ ( get a (len-1) + get b (len-1) = get c (len-1) ) ))
    (ensures ( (eval a len + eval b len = eval c len)))
let addition_lemma_aux a b len c =
  distributivity_add_right (pow2 (bitweight (getTemplate a) (len-1))) (get a (len-1)) (get b (len-1))

val addition_lemma:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } -> 
  b:bigint{ (SameFormat a b) 
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  len:nat{ len <= getLength a } ->
  c:bigint{ (SameFormat a c)
	    /\ (forall (i:nat). i < len ==> get c i = get a i + get b i) } ->
  Lemma
    (requires (True))
    (ensures ( eval a len + eval b len = eval c len ))
let rec addition_lemma a b len c =
  match len with
    | 0 -> ()
    | _ -> addition_lemma a b (len-1) c;
	   addition_lemma_aux a b len c
	   
val theorem_addition: 
  a:bigint{ maxSize a <= maxLimbSize a - 1 } ->
  b:bigint{ SameFormat a b /\ (maxSize b <= maxLimbSize a - 1) } ->
  len:nat{ len <= getLength a } ->
  Lemma
    (requires (True))
    (ensures (eval (addition a b) len = eval a len + eval b len ))
    [SMTPat (addition a b)]
let theorem_addition a b len = addition_lemma a b len (addition a b)

val addition_max_value_lemma:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } ->
  b:bigint{ (SameFormat a b) 
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  Lemma
    (requires (True))
    (ensures (maxValue (addition a b) <= maxValue a + maxValue b))
    [SMTPat (addition a b)]
let addition_max_value_lemma a b = ()

(* TODO : prove *)
#ifndef COMPILE
assume 
#endif
val addition_max_size_lemma:
  a:bigint{ maxSize a <= maxLimbSize a - 1 } ->
  b:bigint{ (SameFormat a b) 
	    /\ (maxSize b <= maxLimbSize a - 1) } ->
  Lemma
    (requires (True))
    (ensures (maxSize (addition a b) <= max (maxSize a) (maxValue b) + 1))
    [SMTPat (addition a b)]
#ifdef COMPILE
let addition_max_size_lemma a b = ()
#endif
