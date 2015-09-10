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
  erase (
      match b, n with
      | Bigint63 data t, 0 -> 0
      | Bigint63 data t, _ -> pow2 (bitweight t (n-1)) * getValue h b (n-1) + eval h b (n-1)
    )

(* Function returning the size of the integer *)
assume logic val sizeOf: x:int -> Tot (n:nat{ Bitsize x n /\ (forall (m:nat). Bitsize x m ==> m >= n) }) 
     
(* Helper functions for stateful array manipulation *)
val array_copy_aux:
  s:array int -> cpy:array int -> ctr:nat ->
  ST unit
     (requires (fun h -> (contains h s /\ contains h cpy /\ s <> cpy)
			 /\ (Seq.length (sel h cpy) = Seq.length (sel h s))
			 /\ (ctr <= Seq.length (sel h cpy))
			 /\ (forall (i:nat). i < ctr ==> Seq.index (sel h s) i = Seq.index (sel h cpy) i)))
     (ensures (fun h0 u h1 -> (contains h1 s /\ contains h1 cpy /\ s <> cpy )
			      /\ (modifies !{cpy} h0 h1)
			      /\ (Seq.Eq (sel h1 cpy) (sel h1 s))))
let rec array_copy_aux s cpy ctr =
  match Array.length cpy - ctr with
  | 0 -> ()
  | _ -> Array.upd cpy ctr (Array.index s ctr);
	 array_copy_aux s cpy (ctr+1)

val array_copy: 
	 s:array int -> 
	 ST (array int)
	    (requires (fun h -> contains h s))
	    (ensures (fun h0 r h1 -> (modifies !{} h0 h1)
				     /\ not(contains h0 r)
				     /\ (contains h1 r)
				     /\ (Seq.Eq (sel h1 r) (sel h0 s))))
let array_copy s =
  let cpy = Array.create (Array.length s) 0 in
  array_copy_aux s cpy 0;
  cpy

val array_blit_aux:
  s:array int -> s_idx:nat -> t:array int -> t_idx:nat -> len:nat -> ctr:nat ->
  ST unit
     (requires (fun h -> 
		(contains h s /\ contains h t /\ s <> t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)
		/\ (ctr <= len)
		/\ (forall (i:nat). 
		    i < ctr ==> Seq.index (sel h s) (s_idx+i) = Seq.index (sel h t) (t_idx+i))))
     (ensures (fun h0 u h1 -> 
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ (modifies !{t} h0 h1)
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat). 
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) = Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==> 
		     Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))
let rec array_blit_aux s s_idx t t_idx len ctr =
  match len - ctr with
  | 0 -> ()
  | _ -> Array.upd t (t_idx + ctr) (Array.index s (s_idx + ctr));
	 array_blit_aux s s_idx t t_idx len (ctr+1)

val array_blit:
  s:array int -> s_idx:nat -> t:array int -> t_idx:nat -> len:nat ->
  ST unit
     (requires (fun h -> 
		(contains h s) 
		/\ (contains h t)
		/\ (s <> t)
		/\ (Seq.length (sel h s) >= s_idx + len)
		/\ (Seq.length (sel h t) >= t_idx + len)))
     (ensures (fun h0 u h1 -> 
	       (contains h1 s /\ contains h1 t /\ s <> t )
	       /\ (Seq.length (sel h1 s) >= s_idx + len)
	       /\ (Seq.length (sel h1 t) >= t_idx + len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (modifies !{t} h0 h1)
	       /\ (forall (i:nat). 
		   i < len ==> Seq.index (sel h1 s) (s_idx+i) = Seq.index (sel h1 t) (t_idx+i))
	       /\ (forall (i:nat).
		   (i < Seq.length (sel h1 t) /\ (i < t_idx \/ i >= t_idx + len)) ==> 
		     (Seq.index (sel h1 t) i = Seq.index (sel h0 t) i)) ))
let rec array_blit s s_idx t t_idx len =
  array_blit_aux s s_idx t t_idx len 0

assume logic val maxValue: 
	       h:heap ->
	       a:bigint{ inHeap h a } -> 
	       Tot (m:nat{ (forall (n:nat). 
			    n < getLength h a ==> abs (getValue h a n) <= m)
			   /\ (exists (i:nat). i < getLength h a /\ abs (getValue h a i) = m) })

assume logic val maxValueIdx: 
	       h:heap ->
	       a:bigint{ inHeap h a } -> 
	       Tot (m:nat{ (m < getLength h a) 
			   /\ (forall (n:nat). n < getLength h a ==> abs (getValue h a n) <= abs (getValue h a m)) })

assume logic val maxSize: 
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Tot (m:nat{ (forall (n:nat). n < getLength h a ==> getSize h a n <= m)
	      /\ (exists (i:nat). i < getLength h a /\ getSize h a i = m) })

val max_size_max_value_lemma:
  h:heap ->
  a:bigint{ inHeap h a } -> 
  Lemma
    (requires (True))
    (ensures (maxValue h a <= pow2 (maxSize h a)))
    [SMTPat (maxValue h a); SMTPat (maxSize h a)]
let max_size_max_value_lemma h a = 
  erase (
      cut (forall (n:nat). n < getLength h a ==> getValue h a n <= maxValue h a);
      cut (forall (n:nat). n < getLength h a ==> getSize h a n <= maxSize h a); 
      let midx = maxValueIdx h a in
      cut (abs (getValue h a midx) = maxValue h a /\ True);
      size_of_value_lemma h a midx;
      cut (Bitsize (abs (getValue h a midx)) (getSize h a midx) /\ True);
      if (getSize h a midx < maxSize h a) then
	pow2_increases_lemma (maxSize h a) (getSize h a midx);
      cut ( pow2 (maxSize h a) >= pow2 (getSize h a midx) /\ True);
      cut ( maxValue h a <= pow2 (maxSize h a) /\ True)
    )

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
  
