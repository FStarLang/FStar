(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Eval --z3timeout 10 --use_eq_at_higher_order;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst;
  --*)

(* 
  This library file should contain types and functions related to big integer 
  representation.
 *)

module Eval

open IntLib
open Limb
open Bigint
open FStar.ST
open FStar.Seq
open FStar.Heap
open FStar.Array
open FStar.Ghost

(* Bit weight of each of the cells of the array of the big integer *)
val bitweight : t:template -> n:nat -> Tot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> t (n-1) + bitweight t (n-1)

(* GHOST : Eval computes the mathematical value of the bigint from its content and its template *)
val eval : h:heap -> b:bigint{ inHeap h b } -> n:nat{ n <= getLength h b } -> Tot int
let rec eval h b n =
  match n with
  | 0 -> 0
  | _ -> 
    let t = getTemplate b in
    pow2 (bitweight t (n-1)) * getValue h b (n-1) + eval h b (n-1)

(* Function returning the size of the integer *)
assume logic val sizeOf: x:int -> Tot (n:nat{ Bitsize x n /\ (forall (m:nat). Bitsize x m ==> m >= n) }) 

assume logic val lsizeOf: x:int -> Tot (n:erased nat{ Bitsize x (reveal n) /\ (forall (m:nat). Bitsize x m ==> m >= reveal n) }) 

assume logic val maxValue: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:nat{ (forall (n:nat). 
	    n < getLength h a ==> abs (getValue h a n) <= m)
	    /\ (exists (i:nat). i < getLength h a /\ abs (getValue h a i) = m) })

assume logic val lmaxValue: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:erased nat{ (forall (n:nat). 
	    n < getLength h a ==> abs (getValue h a n) <= reveal m)
	    /\ (exists (i:nat). i < getLength h a /\ abs (getValue h a i) = reveal m) })

assume logic val maxValueIdx: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:nat{ (m < getLength h a) 
	    /\ (forall (n:nat). n < getLength h a ==> abs (getValue h a n) <= abs (getValue h a (m))) })

assume logic val lmaxValueIdx: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:erased nat{ (reveal m < getLength h a) 
	    /\ (forall (n:nat). n < getLength h a ==> abs (getValue h a n) <= abs (getValue h a (reveal m))) })

assume logic val maxSize: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:nat{ (forall (n:nat). n < getLength h a ==> getSize h a n <= m)
	      /\ (exists (i:nat). i < getLength h a /\ getSize h a i = m) })

assume logic val lmaxSize: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:erased nat{ (forall (n:nat). n < getLength h a ==> getSize h a n <= reveal m)
	      /\ (exists (i:nat). i < getLength h a /\ getSize h a i = reveal m) })

val max_size_max_value_lemma:
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Lemma
    (requires (True))
    (ensures (maxValue h a <= pow2 (maxSize h a)))
    [SMTPat (maxValue h a); SMTPat (maxSize h a)]
let max_size_max_value_lemma h a = 
      cut (forall (n:nat). n < getLength h a ==> getValue h a n <= maxValue h a);
      cut (forall (n:nat). n < getLength h a ==> getSize h a n <= maxSize h a); 
      let midx = maxValueIdx h a in
      cut (abs (getValue h a (midx)) = maxValue h a /\ True);
      size_of_value_lemma h a midx;
      cut (Bitsize (abs (getValue h a (midx))) (getSize h a (midx)) /\ True);
      if (getSize h a midx < maxSize h a) then
	pow2_increases_lemma (maxSize h a) (getSize h a (midx))
	else ();
      cut ( pow2 (maxSize h a) >= pow2 (getSize h a (midx)) /\ True);
      cut ( maxValue h a <= pow2 (maxSize h a) /\ True)


val maxValue_eq_lemma: 
  ha:heap -> hb:heap -> a:bigint{ inHeap ha a }  -> b:bigint{ inHeap hb b } -> 
  Lemma 
    (requires (EqualBigint a b ha hb)) 
    (ensures (maxValue ha a = maxValue hb b))
let maxValue_eq_lemma ha hb a b = ()

val eval_eq_lemma:
  ha:heap ->
  hb:heap -> 
  a:bigint{ inHeap ha a } ->
  b:bigint{ (inHeap hb b)
	    /\ (Bigint63.t a = Bigint63.t b) } ->
  len:nat{ (len <= getLength ha a)
	   /\ (len <= getLength hb b) } ->
  Lemma
    (requires ( (forall (i:nat). i < len 
		 ==> getValue ha a i = getValue hb b i) ))
    (ensures ( eval ha a len = eval hb b len ))
let rec eval_eq_lemma ha hb a b len =
  match len with
  | 0 -> ()
  | _ -> eval_eq_lemma ha hb a b (len-1)

val eval_null:
  h:heap ->
  b:bigint{ inHeap h b } ->
  len:nat{ len <= getLength h b } ->
  Lemma
    (requires (forall (i:nat). i < len ==> getValue h b i = 0))
    (ensures (eval h b len = 0))
let rec eval_null h b len =
  match len with
  | 0 -> ()
  | _ -> 
     eval_null h b (len-1)

val max_value_of_null_lemma:
  h:heap ->
  b:bigint{ inHeap h b } ->
  Lemma
    (requires (IsNull h b))
    (ensures (maxValue h b = 0))
let max_value_of_null_lemma h b = ()
  
