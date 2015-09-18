#include "preproc.h"

(* 
  This library file shoul contains types and functions related to big integer 
  representation.
 *)
(* 
  STATUS :  
  Unproven lemmas, see TODOs
 *)

module Eval

open IntLib
open Limb
open FStar.Seq

RESET

(* TODO : unify the types and notations for bigint *)
type int64 = int

type intarray = seq int

(* Mathematical integer *)
type integer = int
type u8 = int

(* Bounded integer arrays *)
(* TODO : move those to the Limb module *)
type larray (n:nat) = s:seq int{ (forall (i:nat). i< length s ==> Bitsize (index s i) n) }
type ularray (n:nat) = s:seq nat{ (forall (i:nat). i < length s ==> Bitsize (index s i) n) }

(* Maps the index of the integer data to the theoretic bit size of the cell *)
type template = nat -> Tot nat
type template_const = t:template{ forall (n:nat). t n = t 0 }

(* Template examples : *)
val template_25519 : template
let template_25519 = fun n ->
  if n % 2 = 0 then 26 else 25

val template_bytearray : template
let template_bytearray = fun n -> 8


(* Represents a big integer as an array and a template *)
(* Data is the concrete representation of the bigint *)
(* Template gives information on how to mathematically evaluate it *)
(* Sign is its sign *)
(* Size is a ghost value bounding the size of each element of data to show absence of overflows *)
type bigint = 
  //| Bigint : data:seq integer -> t:template -> size:template -> sign:bool -> bigint
  | Bigint64 : data:larray 63{ length data > 0 } -> 
	       t:template -> (* TODO : is a 63 bits bound necessary here ? *) 
	       size:template{ forall (n:nat). n < length data ==> 
				(Bitsize (index data n) (size n)
				 /\ size n <= 63 ) } ->
	       sign:bool -> bigint

type SameFormat (a:bigint) (b:bigint) = 
  (Bigint64.t a = Bigint64.t b /\ length (Bigint64.data a) = length (Bigint64.data b) )



(* Getters *)
val getData : bigint -> Tot (seq int)
let getData b =
  match b with
  //| Bigint data t size sign -> data
  | Bigint64 data t size sign -> data

val getTemplate : bigint -> Tot template
let getTemplate b =
  match b with
  //| Bigint data t size sign -> t
  | Bigint64 data t size sign -> t

val getSize : bigint -> Tot template
let getSize b =
  match b with
  //| Bigint data t size sign -> size
  | Bigint64 data t size sign -> size

val getSign : bigint -> Tot bool
let getSign b =
  match b with
  //| Bigint data t size sign -> sign
  | Bigint64 data t size sign -> sign				   

val getLength : bigint -> Tot nat
let getLength b =
  length (getData b)

val get: b:bigint -> n:nat{ n < getLength b } -> Tot (lint ((getSize b) n))
let get b n =
  let data = getData b in
  index data n

val maxLimbSize: bigint -> Tot pos
let maxLimbSize b = 
  match b with
    | Bigint64 _ _ _ _ -> 63

type Normalized (b:bigint) =
  (forall (n:nat). n < getLength b ==> getSize b n <= getTemplate b n)

(* Eval computes the mathematical value of the bigint from its content and its template *)
val bitweight : t:template -> n:nat -> Tot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> (t n) + bitweight t (n-1)

val eval_aux : a:seq int -> t:template -> n:nat{ n <= length a } -> Tot int
let rec eval_aux (a:seq int) t n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight t (n-1)) * index a (n-1) + eval_aux a t (n-1)
	
val eval : b:bigint -> n:nat{ n <= getLength b } -> Tot int
let eval b len =
  let data = getData b in
  let template = getTemplate b in
  eval_aux data template len

(* Function returning the size of the integer *)
val size : x:int -> Tot (n:nat{ Bitsize x n })
let size x = 
  if x = 0 then 0
  else if x < 0 then log (-x)
  else log x


(* Universal bytearray type ? *)
type bytearray = b:bigint{ (is_Bigint64 b)
			   /\ (getTemplate b = template_bytearray)
			   /\ (forall (n:nat). (getSize b) n <= 8)
			   /\ (getSign b = true) }

type EqualBigint (a:bigint) (b:bigint) =
  (Eq (getData a) (getData b) /\ getTemplate a = getTemplate b )

(* Helpful functions *)

val extendTo : a:bigint -> len:nat{ len >= getLength a } -> 
	       Tot (b:bigint{ (getLength b = len)
			      /\ (getTemplate a = getTemplate b)
			      /\ (forall (i:nat). 
				  (i < getLength a ==> 
				     (getSize a i = getSize b i /\ get a i = get b i))
				  /\ ((i >= getLength a /\ i < len) ==> 
					(getSize b i = 0 /\ get b i = 0)))
			      /\ (getSign a = getSign b) })
let extendTo a len =
  let data = append (getData a) (create (len-(getLength a)) zero) in
  let t = getTemplate a in
  let (size:template) = fun (n:nat) -> if n < getLength a then (getSize a n)
				       else 0 in
  let sign = getSign a in
  Bigint64 data t size sign    
		 
val maxValue_aux: 
  a:bigint -> 
  len:nat{ len <= getLength a } -> 
  tmp:nat{ (forall (n:nat). n < len ==> abs (get a n) <= tmp)
	   /\ (exists (i:nat). i < len /\ abs (get a i) = tmp) } -> 
  Tot (m:nat{ (forall (n:nat). n < getLength a ==> abs (get a n) <= m)
	      /\ (exists (i:nat). i < getLength a /\ abs (get a i) = m) })
      (decreases (getLength a - len))
let rec maxValue_aux a len tmp =
  match getLength a - len with
  | 0 -> tmp
  | _ -> 
     let v = get a len in
     let tmp = if abs v > tmp then abs v else tmp in
     maxValue_aux a (len+1) tmp

val maxValue: a:bigint{ getLength a >= 1 } -> Tot (m:nat{ (forall (n:nat). n < getLength a ==> abs (get a n) <= m)
				      /\ (exists (i:nat). i < getLength a /\ abs (get a i) = m) })
let maxValue a = 
  maxValue_aux a 1 (abs (get a 0))

val maxValueIdx_aux: 
  a:bigint -> 
  len:nat{ len <= getLength a } -> 
  tmp:nat{ tmp < len /\ (forall (n:nat). n < len ==> abs (get a n) <= abs (get a tmp) ) } -> 
  Tot (m:nat{ (m < getLength a) 
	      /\ (forall (n:nat). n < getLength a ==> abs (get a n) <= abs (get a m)) })
      (decreases (getLength a - len))
let rec maxValueIdx_aux a len tmp =
  match getLength a - len with
  | 0 -> tmp
  | _ -> 
     let tmp = if abs (get a len) > abs (get a tmp) then len else tmp in
     maxValueIdx_aux a (len+1) tmp

val maxValueIdx: a:bigint{ getLength a >= 1 } -> Tot (m:nat{ (m < getLength a) 
	      /\ (forall (n:nat). n < getLength a ==> abs (get a n) <= abs (get a m)) })
let maxValueIdx a = 
  maxValueIdx_aux a 1 0

val maxSize_aux : a:bigint -> len:nat{ len <= getLength a } -> 
		  tmp:nat{ (forall (n:nat). n < len ==> getSize a n <= tmp )
			   /\ (exists (i:nat). i < len /\ getSize a i = tmp) } ->
		  Tot (m:nat{ (forall (n:nat). n < getLength a ==> getSize a n <= m)
			      /\ (exists (i:nat). i < getLength a /\ getSize a i = m) })
		      (decreases (getLength a - len))
let rec maxSize_aux a len tmp =
  match getLength a - len with
  | 0 -> tmp
  | _ -> let v = getSize a len in
	 let tmp = if v > tmp then v else tmp in
	 maxSize_aux a (len+1) tmp

val maxSize: 
  a:bigint -> 
  Tot (m:nat{ (forall (n:nat). n < getLength a ==> getSize a n <= m)
	      /\ (exists (i:nat). i < getLength a /\ getSize a i = m) })
let maxSize a =
  maxSize_aux a 1 (getSize a 0)

val max_size_max_value_lemma:
  a:bigint -> 
  Lemma
    (requires (True))
    (ensures (maxValue a <= pow2 (maxSize a)))
    [SMTPat (maxValue a); SMTPat (maxSize a)]
let max_size_max_value_lemma a = 
  cut (forall (n:nat). n < getLength a ==> get a n <= maxValue a);
  cut (forall (n:nat). n < getLength a ==> getSize a n <= maxSize a); 
  let midx = maxValueIdx a in
  cut (abs (get a midx) = maxValue a /\ Bitsize (abs (index (Bigint64.data a) midx)) (Bigint64.size a midx) );
  if (Bigint64.size a midx < maxSize a) then
    pow2_increases_lemma (maxSize a) (Bigint64.size a midx);
  cut ( pow2 (maxSize a) >= pow2 (Bigint64.size a midx) /\ True);
  cut ( maxValue a <= pow2 (maxSize a) /\ True);
  ()

val maxValue_eq_lemma: a:bigint -> b:bigint -> Lemma (requires (EqualBigint a b)) (ensures (maxValue a = maxValue b))
let maxValue_eq_lemma a b = ()

(* let maxSize a = 
  

val uniformizeSize: a:bigint -> Tot b:bigint{ (EqualBigint a b)
					      /\ (forall 
 *)

(* Lemmas *)
val eval_of_zero: 
  a:bigint -> 
  len:nat{ (len <= getLength a) } ->
  Lemma 
    (requires (forall (i:nat). i < len ==> get a i = zero))
    ( ensures ( eval a len = zero ) )
    [SMTPat (eval a len)]
let rec eval_of_zero a len =
  match len with
  | 0 -> ()
  | _ -> 
     cut ( eval a len = pow2 (bitweight (getTemplate a) (len-1)) * get a (len-1) + eval_aux (getData a) (getTemplate a) (len-1) /\ True );
     eval_of_zero a (len-1)

val eval_equal_lemma:
  a:bigint -> b:bigint -> 
  Lemma
    (requires (EqualBigint a b))
    (ensures (eval a (getLength a) = eval b (getLength b)))
let eval_equal_lemma a b = ()

val eval_partial_eq_lemma:
  a:bigint -> b:bigint -> i:nat{ i <= getLength a /\ i <= getLength b } ->
  Lemma
    (requires ((forall (n:nat). n < i ==> (get a n = get b n /\ getTemplate a = getTemplate b)))) 
    (ensures ( eval a i = eval b i))
let rec eval_partial_eq_lemma a b i =
  match i with 
  | 0 -> ()
  | _ -> 
     eval_partial_eq_lemma a b (i-1);
     cut ( eval a i = pow2 (bitweight (getTemplate a) (i-1)) * get a (i-1) + eval_aux (getData a) (getTemplate a) (i-1) /\ True );
     cut ( eval b i = pow2 (bitweight (getTemplate b) (i-1)) * get b (i-1) + eval_aux (getData b) (getTemplate b) (i-1) /\ True );
     ()

RESET
SET "--z3timeout 60"

val extendTo_lemma: a:bigint -> len:nat{ len >= getLength a } ->
		    Lemma
		      (requires (True))
		      (ensures ( eval a (getLength a) = eval (extendTo a len) len))
		      [SMTPat (extendTo a len)]
		      (decreases (len - (getLength a)))
let rec extendTo_lemma a len =
  match (len - getLength a) with
  | 0 -> 
     eval_equal_lemma a (extendTo a (getLength a))
  | _ ->
     extendTo_lemma a (len-1);
     cut ( eval (extendTo a len) len = eval (extendTo a len) (len-1) /\ True );
     eval_partial_eq_lemma (extendTo a (len-1)) (extendTo a len) (len-1)

  
(* TODO : prove this lemma *)
#ifndef COMPILE
assume 
#endif
val extendTo_max_size_and_values_lemma : 
  a:bigint -> len:nat{ len >= getLength a } -> 
  Lemma
    (requires (True))
    (ensures (maxSize (extendTo a len) = maxSize a /\ maxValue (extendTo a len) = maxValue a))
    [SMTPat (extendTo a len)]
#ifdef COMPILE
let extendTo_max_size_and_values_lemma a len = ()
#endif
