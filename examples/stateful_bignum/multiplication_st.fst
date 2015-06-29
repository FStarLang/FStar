module Multiplication

open IntLib
open Limb
open Seq
open Bigint
open Eval
open ST
open Heap
open Addition
open ScalarMultiplication
open Axiomatic

(* Verification query :
fstar.exe $FSTAR_HOME/lib/seq.fsi --admit_fsi Seq axiomatic.p.fst intlib.fst limb.fst eval.fst addition.fst shift_array.fst scalar_multiplication.fst multiplication.fst --verify_module Multiplication
 *)

(* Type of bigintegers with constant template *)
type norm_bigint = a:bigint{ (forall (n:nat). Bigint63.t a n = Bigint63.t a 0) }

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_0: a:int -> b:int -> c:int -> Lemma (ensures (a+b-c = a-c+b))
let auxiliary_lemma_0 a b c = ()

(* Lemma : additivity property of the "bitweight" function if the template is normalized *)
val bitweight_lemma_0:
  t:template{ forall (n:nat). t n = t 0 } -> i:nat -> j:nat -> 
  Lemma
    (requires (True))
    (ensures ( bitweight t (i+j) = bitweight t i + bitweight t j))
let rec bitweight_lemma_0 t i j =
  match i with
  | 0 -> ()
  | _ -> bitweight_lemma_0 t (i-1) j

(* Lemma : combines the additivity property of the bitweight function and the exponential property 
   of the pow2 function *)
val auxiliary_lemma_1: t:template{ forall (n:nat). t n = t 0 } -> a:nat -> b:nat -> 
		       Lemma (ensures ( pow2 (bitweight t (a+b)) = pow2 (bitweight t a) * pow2 (bitweight t b)))
let auxiliary_lemma_1 t a b =
  bitweight_lemma_0 t a b;
  pow2_exp_lemma (bitweight t a) (bitweight t b)

(* Lemma : first half of the helper for the multiplication_step_lemma *)
assume val multiplication_step_lemma_p1:
  h0:heap -> 
  h1:heap -> 
  a:norm_bigint{ inHeap h0 a } -> 
  b:norm_bigint{ inHeap h0 b /\ Bigint63.t b = Bigint63.t a } -> 
  c:norm_bigint{ inHeap h1 c /\ Bigint63.t c = Bigint63.t a } ->
  idx:nat ->
  len:pos{ (len + idx <= getLength h0 a) 
	   /\ (len <= getLength h0 b) 
	   /\ (getLength h0 a = getLength h1 c) } ->
  Lemma
    (requires (
	 (forall (i:nat).
	  ((i < len ==> getValue h1 c (i+idx) = getValue h0 a (i+idx) + getValue h0 b i)
	   /\ ((i < idx) ==> getValue h1 c i = getValue h0 a i)))
	 /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1)
	     ))
(*
let multiplication_step_lemma_p1 h0 h1 a b c idx len =
  auxiliary_lemma_0 len idx 1;
  cut (eval h1 c (len+idx-1) = eval h0 a (len+idx-1) + (pow2 (bitweight (Bigint63.t a) idx)) * eval h0 b (len-1) /\ True);
  cut (getValue h1 c (len+idx-1) = getValue h0 a (len+idx-1) + getValue h0 b (len-1) /\ True);
  cut (eval h1 c (len+idx) = eval h1 c (len+idx-1) + pow2 (bitweight (Bigint63.t a) (len+idx-1)) * (getValue h1 c (len+idx-1)) /\ True );
  cut (eval h1 c (len+idx) = 
	 eval h0 a (len+idx-1) + (pow2 (bitweight (Bigint63.t a) idx)) * eval h0 b (len-1)
	 +
	   pow2 (bitweight (Bigint63.t a) (len-1+idx)) * (getValue h0 a (len+idx-1) + getValue h0 b (len-1)) /\ True);
  distributivity_add_right (pow2 (bitweight (Bigint63.t a) (len-1+idx))) (getValue h0 a (len+idx-1)) (getValue h0 b (len-1));
  cut (True /\ eval h1 c (len+idx) = 
	 eval h0 a (len+idx-1) + (pow2 (bitweight (Bigint63.t a) idx)) * eval h0 b (len-1)
	 +
	   pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 a (len+idx-1) + 
           pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1));
  cut (True /\ eval h1 c (len+idx) = 
	 pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 a (len+idx-1) + eval h0 a (len+idx-1) + 
           pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1)  +	        
           pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1));
  cut (True /\ eval h0 a (len+idx) = pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 a (len+idx-1) + eval h0 a (len+idx-1));
  cut (True /\ eval h1 c (len+idx) = eval h0 a (len+idx) +  
				       pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1)  +	        
				       pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1))
 *)

(* Lemma : second half of the helper for the multiplciation_step_lemma *)
assume val multiplication_step_lemma_p2:
  h0:heap -> 
  h1:heap -> 
  a:norm_bigint{ inHeap h0 a } -> 
  b:norm_bigint{ inHeap h0 b /\ Bigint63.t b = Bigint63.t a } -> 
  c:norm_bigint{ inHeap h1 c /\ Bigint63.t c = Bigint63.t a } ->
  idx:nat ->
  len:pos{ (len + idx <= getLength h0 a) 
	   /\ (len <= getLength h0 b) 
	   /\ (getLength h0 a = getLength h1 c) } ->
  Lemma
    (requires (
	 eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1)
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (Bigint63.t a) idx) * eval h0 b len
	     ))
(*
let multiplication_step_lemma_p2 h0 h1 a b c idx len =
  auxiliary_lemma_0 len idx 1;
  auxiliary_lemma_1 (Bigint63.t a) idx (len-1);
  cut (True /\ pow2 (bitweight (Bigint63.t a) (len-1+idx)) = pow2 (bitweight (Bigint63.t a) idx) * pow2 (bitweight (Bigint63.t a) (len-1)) );
  paren_mul_left (pow2 (bitweight (Bigint63.t a) idx)) (pow2 (bitweight (Bigint63.t a) (len-1))) (getValue h0 b (len-1));
  cut (eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight (Bigint63.t a) idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight (Bigint63.t a) idx) * pow2 (bitweight (Bigint63.t a) (len-1)) * getValue h0 b (len-1) /\ True);
  distributivity_add_right (pow2 (bitweight (Bigint63.t a) idx)) (eval h0 b (len-1)) (pow2 (bitweight (Bigint63.t a) (len-1)) * (getValue h0 b (len-1)));     
  cut (True /\ eval h0 b len = eval h0 b (len-1) + (pow2 (bitweight (Bigint63.t a) (len-1))) * (getValue h0 b (len-1)) );  
  cut (True /\ pow2 (bitweight (Bigint63.t a) (len-1+idx)) * getValue h0 b (len-1) =
         pow2 (bitweight (Bigint63.t a) idx) * pow2 (bitweight (Bigint63.t a) (len-1)) * getValue h0 b (len-1) );
  cut ( True /\ eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (Bigint63.t a) idx) * eval h0 b len) 
 *)

(* Lemma : changes the result of the addition function into the equivalent relation between 
  evaluated bigints *)
val multiplication_step_lemma:
  h0:heap -> 
  h1:heap -> 
  a:norm_bigint{ inHeap h0 a } -> 
  b:norm_bigint{ inHeap h0 b /\ Bigint63.t b = Bigint63.t a } -> 
  c:norm_bigint{ inHeap h1 c /\ Bigint63.t c = Bigint63.t a } ->
  idx:nat ->
  len:nat{ (len + idx <= getLength h0 a) 
	   /\ (len <= getLength h0 b) 
	   /\ (getLength h0 a = getLength h1 c) } ->
  Lemma
    (requires (
	 (forall (i:nat).
	  ((i < len ==> getValue h1 c (i+idx) = getValue h0 a (i+idx) + getValue h0 b i)
	   /\ ((i < idx) ==> getValue h1 c i = getValue h0 a i)))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight (Bigint63.t a) idx) * eval h0 b len
	     ))

#reset-options

let rec multiplication_step_lemma h0 h1 a b c idx len =
  match len with
  | 0 ->
     admit () //eval_eq_lemma h0 h1 a c idx
  | _ ->
     auxiliary_lemma_0 len idx 1;
     multiplication_step_lemma h0 h1 a b c idx (len-1);
     multiplication_step_lemma_p1 h0 h1 a b c idx len;
     multiplication_step_lemma_p2 h0 h1 a b c idx len

(* Helper lemmas that avoid super long computation or intensive use of "cuts" *)
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_0 : 
  a:int -> b:int -> c:int -> 
  Lemma
    (requires (True))
    (ensures ( a - c - b + c = a - b ))
let helper_lemma_0 a b c = ()

(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_1 : a:int -> Lemma (ensures (1 * a = a))
let helper_lemma_1 a = ()

(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_2 : a:nat -> Lemma (ensures (a + a = 2 * a))
let helper_lemma_2 a = ()

(* Lemma : bound property of the "maxSize" function *)
val max_size_lemma:
  h:heap -> a:bigint{ inHeap h a } -> l:nat ->
  Lemma
    (requires (l >= maxSize h a))
    (ensures ( forall (n:nat). n < getLength h a ==> getSize h a n <= l ))
let max_size_lemma h a l = ()

(* Lemma : additivity property of the "sizeOf" function (log equivalent) *)
val size_lemma_1:
  a:nat -> b:nat ->
  Lemma
    (requires (True))
    (ensures (sizeOf( a * b ) <= sizeOf a + sizeOf b ))
let size_lemma_1 a b =
  if a = 0 then ()
  else if b = 0 then ()
  else log_lemma a b

(* Lemma : extension of the previous lemma *)
val size_lemma_2:
  h:heap -> a:bigint{ inHeap h a } -> x:nat -> n:nat ->
  Lemma
    (requires (maxValue h a <= x * (pow2 n))) 
    (ensures ( forall (i:nat). i < getLength h a ==> Bitsize (getValue h a i) (sizeOf x + n) ))
let size_lemma_2 h a x n =
  erase (
      cut (x < pow2 (sizeOf x) /\ True );
      pow2_exp_lemma (sizeOf x) n;
      cut ( pow2 (sizeOf x) * (pow2 n) = pow2 (sizeOf x + n) /\ True );
      mul_pos_strict_incr_lemma (pow2 n) x (pow2 (sizeOf x));
      cut ( maxValue h a < pow2 (sizeOf x + n) /\ True );
      cut ( forall (i:nat). i < getLength h a ==> Bitsize (getValue h a i) (sizeOf x + n) /\ True );
      ()
    )

(* Lemma : "sizeOf" increases *)
val size_lemma_3:
	 a:nat -> b:nat -> 
	 Lemma
	   (requires (a <= b))
	   (ensures (sizeOf a <= sizeOf b))
let size_lemma_3 a b =
  erase (
      if a = 0 then ()
      else if a < b then log_incr_lemma a b
      else ()
    )
	
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_3:
	 a:nat -> b:nat -> c:nat -> d:nat ->
	 Lemma
	   (requires ( a <= c /\ b <= d ))
	   (ensures ( a*b <= c*d ))
let helper_lemma_3 a b c d =
  erase (
      mul_incr_lemma a b d;
      assert ( a * b <= a * d );
      swap_mul a d;
      swap_mul c d;
      mul_incr_lemma d a c;
      ()
    )
	
(* Helper lemma, ensures clause is self explainatory *)
val helper_lemma_4:
  a:nat -> b:nat -> Lemma (ensures ( a * b >= 0 ))
let helper_lemma_4 a b = ()
			   
#reset-options

(* Lemma *)
assume val auxiliary_lemma_2:
  h0:heap ->
  h1:heap ->
  h2:heap ->
  a:norm_bigint{ 
      (inHeap h0 a) 
      /\ (getLength h0 a > 0)
      /\ (wordSize a - 2 >= log (getLength h0 a))
      /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2 ) / 2) } ->
  b:norm_bigint{ 
      (inHeap h1 b)
      /\ (SameFormat h0 h1 a b)
      /\ (maxSize h1 b <= (wordSize b - log (getLength h1 b) - 2 ) / 2) } ->
  ctr:nat{ (ctr <= getLength h0 a) } ->
  c:bigint{ 
      (inHeap h2 c)
      /\ (maxValue h2 c <= ctr * (maxValue h0 a * maxValue h1 b)) } ->
  Lemma
    (requires (True))
    (ensures ((maxValue h0 a <= pow2 ((wordSize a - log (getLength h0 a) - 2 ) / 2 )) 
	    /\ (maxValue h1 b <= pow2 ((wordSize b - log (getLength h0 a) - 2 ) / 2))))
(*
let auxiliary_lemma_2 h0 h1 h2 a b ctr c =
  cut ( maxValue h0 a <= pow2 (maxSize h0 a) /\ True );
  if (((wordSize a - log (getLength h0 a) - 2) / 2) > (maxSize h0 a)) then
    pow2_increases_lemma ((wordSize a - log (getLength h0 a) - 2) / 2) (maxSize h0 a);
  if (((wordSize b - log (getLength h1 b) - 2) / 2) > (maxSize h1 b)) then
    pow2_increases_lemma ((wordSize b - log (getLength h1 b) - 2) / 2) (maxSize h1 b);
  cut (pow2 (maxSize h0 a) <= pow2 ((wordSize a - log (getLength h0 a) - 2) / 2) /\ True );
  cut (maxValue h0 a <= pow2 (maxSize h0 a) /\ True );
  cut (maxValue h0 a <= pow2 ((wordSize a - log (getLength h0 a) - 2) / 2 ) /\ True );
  cut (pow2 (maxSize h1 b) <= pow2 ((wordSize b - log (getLength h1 b) - 2) / 2) /\ True );
  cut (maxValue h1 b <= pow2 (maxSize h1 b) /\ True );
  cut (maxValue h1 b <= pow2 ((wordSize b - log (getLength h1 b) - 2) / 2 ) /\ True )
 *)
  
#reset-options


(* Lemma : bounds the maxValues product *)
assume val auxiliary_lemma_3:
  h0:heap ->
  h1:heap ->
  h2:heap ->
  a:norm_bigint{ 
      (inHeap h0 a) 
      /\ (getLength h0 a > 0)
      /\ (wordSize a - 1 >= log (getLength h0 a) + 1)
      /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2 ) / 2) } ->
  b:norm_bigint{ 
      (inHeap h1 b)
      /\ (SameFormat h0 h1 a b)
      /\ (maxSize h1 b <= (wordSize b - log (getLength h1 b) - 2 ) / 2) } ->
  ctr:nat{ (ctr <= getLength h0 a) } ->
  c:bigint{ 
      (inHeap h2 c)
      /\ (maxValue h2 c <= ctr * (maxValue h0 a * maxValue h1 b)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h0 a * maxValue h1 b <= pow2 (wordSize a - log (getLength h0 a) - 2)))
(*
let auxiliary_lemma_3 h0 h1 h2 a b ctr c =
  erase 
    (
      auxiliary_lemma_2 h0 h1 h2 a b ctr c;
      let s = (wordSize a - log (getLength h0 a) - 2) in
      cut (wordSize b - log (getLength h1 b) - 2 = s /\ True);
      helper_lemma_3 (maxValue h0 a) (maxValue h1 b) (pow2 ((wordSize a - log (getLength h0 a) -2)/2)) (pow2 ((wordSize b - log (getLength h1 b) -2)/2));
      pow2_exp_lemma (s/2) (s/2);
      cut (maxValue h0 a * maxValue h1 b <= pow2 ((s/2)+(s/2)) /\ True);
      helper_lemma_2 (s/2);
      multiply_fractions_lemma s 2;
      cut ((s / 2)+(s/2) <= (s) /\ True);
      if (((s/2)+(s/2)) < s ) then
	pow2_increases_lemma s ((s/2)+(s/2));
      cut (pow2 (((s/2)+(s/2))) <= pow2 s /\ True);
      cut (maxValue h0 a * maxValue h1 b <= pow2 s /\ True);
      ()
    )
 *)

#reset-options

(* GHOST CODE, not tail recursive because this function should only be ghost *)
assume val multiplication_step_resize_iterate:
  a:bigint -> size:nat -> ctr:nat ->
  ST unit
     (requires (fun h ->
		(inHeap h a)
		/\ (ctr <= getLength h a)
		/\ (size < wordSize a)
		/\ (forall (i:nat). i < getLength h a
		    ==> Bitsize (getValue h a i) size)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a) /\ (inHeap h1 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (ctr <= getLength h0 a)
	       /\ (size < wordSize a)
	       /\ (getLength h1 a = getLength h0 a)
	       /\ (forall (i:nat). 
		   (i < ctr ==> getSize h1 a i = size)
		   /\ (i < getLength h1 a ==> getValue h0 a i = getValue h1 a i))
     ))
(*
let rec multiplication_step_resize_iterate a size ctr =
  match ctr with
  | 0 -> ()
  | _ ->
     let i = ctr - 1 in
     multiplication_step_resize_iterate a size i;
     let t = mk_tint a size (Bigint.get a i) in
     updateBigint a i t
 *)

(* GHOST CODE : resizes a bigint, knowing a tighter bound on its maximum value *)
(* It should be erased since the size is a ghost parameter *)
assume val multiplication_step_resize : 
  a:norm_bigint -> b:norm_bigint -> ctr:pos -> c:norm_bigint ->
  ST unit
     (requires (fun h -> 
		(inHeap h a) /\ (inHeap h b) /\ (inHeap h c)
		/\ (Bigint63.data a <> Bigint63.data c)
		/\ (Bigint63.data b <> Bigint63.data c)
		/\ (getLength h a > 0)
		/\ (wordSize a - 2 >= log (getLength h a))
		/\ (maxSize h a <= (wordSize a - log (getLength h a) - 2) / 2)
		/\ (maxSize h b <= (wordSize a - log (getLength h a) - 2) / 2)
		/\ (SameFormat h h a b)
		/\ (ctr <= getLength h a)
		/\ (maxValue h c <= ctr * (maxValue h a * maxValue h b))
     ))
     (ensures (fun h0 u h1 -> 
	       (inHeap h0 a) /\ (inHeap h0 b) /\ (inHeap h0 c)
	       /\ (inHeap h1 a) /\ (inHeap h1 b) /\ (inHeap h1 c)
	       /\ (Bigint63.data a <> Bigint63.data c)
	       /\ (Bigint63.data b <> Bigint63.data c)
	       /\ (getLength h0 a > 0)
	       /\ (wordSize a - 2 >= log (getLength h0 a))
	       /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 b <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (SameFormat h0 h0 a b)
	       /\ (ctr <= getLength h0 a)
	       /\ (maxValue h0 c <= ctr * (maxValue h0 a * maxValue h0 b))
	       /\ (modifies !{Bigint63.data c} h0 h1)
	       /\ (getLength h1 c = getLength h0 c)
	       /\ (forall (i:nat). i < getLength h1 c
		   ==> ((getValue h1 c i = getValue h0 c i)
			/\ (getSize h1 c i = wordSize a - 2)))

     ))
(*
let multiplication_step_resize a b ctr c =
  let h0 = ST.get() in
  let s = (wordSize a - log (getLength h0 a) - 2) in
  auxiliary_lemma_3 h0 h0 h0 a b ctr c;
  cut ( maxValue h0 a * maxValue h0 b <= pow2 s /\ True);
  helper_lemma_4 (maxValue h0 a) (maxValue h0 b);
  mul_incr_lemma ctr (maxValue h0 a * maxValue h0 b) (pow2 s);
  cut (maxValue h0 c <= ctr * pow2 s /\ True);
  size_lemma_2 h0 c ctr s;
  cut ( forall (i:nat). i < getLength h0 c ==> Bitsize (getValue h0 c i) (sizeOf ctr + s) );
  if ctr < getLength h0 a then log_incr_lemma ctr (getLength h0 a);
  cut (sizeOf ctr + s <= wordSize a - 2 /\ True );
  if (sizeOf ctr + s < wordSize a - 2) then pow2_increases_lemma (wordSize a - 2) (sizeOf ctr + s);
  cut ( forall (i:nat). i < getLength h0 c ==> Bitsize (getValue h0 c i) (wordSize a - 2) );
  let new_size = wordSize a - 2 in
  multiplication_step_resize_iterate c new_size (getLength h0 c)
 *)

#reset-options

(* Lemma : equality between the content of arrays implies equality of the 
   maximum values and sizes *)
val auxiliary_lemma_4 : 
  ha:heap -> hb:heap -> 
  a:bigint{ inHeap ha a } -> 
  b:bigint{ inHeap hb b } -> 
  Lemma
    (requires (Seq.Eq (sel ha (Bigint63.data a)) (sel hb (Bigint63.data b))))
    (ensures (maxSize ha a = maxSize hb b /\ maxValue ha a = maxValue hb b))
let auxiliary_lemma_4 ha hb a b = ()

#reset-options

(* Lemma : extends the "eval" property to the total length if apporpriate *)
assume val auxiliary_lemma_5: 
  h0:heap -> h1:heap -> 
  a:bigint{ inHeap h0 a } ->
  b:bigint{ (inHeap h1 b) 
	    /\ (getLength h1 b = getLength h0 a)
	    /\ (Bigint63.t a = Bigint63.t b) } ->
  c:int ->
  len:nat{ len <= getLength h1 b } ->
  len2:nat{ len2 >= len /\ len2 <= getLength h1 b } ->
  Lemma
    (requires ( (eval h1 b len = eval h0 a len + c)
		/\ (forall (i:nat). (i < len2 /\ i >= len)
		    ==> getValue h1 b i = getValue h0 a i)))
    (ensures ( (eval h1 b len2 = eval h0 a len2 + c)))
(*
let rec auxiliary_lemma_5 h0 h1 a b c len len2 =
  match len2 - len with
  | 0 -> ()
  | _ ->
     let t = Bigint63.t a in
     auxiliary_lemma_5 h0 h1 a b c len (len2-1);
     cut (True /\ eval h1 b (len2-1) = eval h0 a (len2-1) + c);
     cut (True /\ eval h1 b len2 = eval h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * getValue h1 b (len2-1));
     cut (True /\ eval h1 b len2 = eval h0 a (len2-1) + c + (pow2 (bitweight t (len2-1))) * getValue h0 a (len2-1));
     cut (True /\ eval h1 b len2 = eval h0 a len2 + c)
 *)

(* Same as auxiliary_lemma_4, TODO : remove *)
assume val auxiliary_lemma_6 : ha:heap -> hb:heap -> a:bigint{ inHeap ha a } -> b:bigint{ inHeap hb b } ->
			       Lemma
				 (requires (Seq.Eq (sel ha (Bigint63.data a)) (sel hb (Bigint63.data b))))
				 (ensures (maxSize ha a = maxSize hb b /\ maxValue ha a = maxValue hb b))
(*
let auxiliary_lemma_6 h0 h1 a b = ()
 *)

#reset-options

(* Code : does 1 step of the multiplication (1 scalar multiplication), 
   and infers the appropriate properties on sizes, values and evaluated
   values for the resulting bigint *)
val multiplication_step:
  a:norm_bigint -> b:norm_bigint -> ctr:nat -> c:norm_bigint -> tmp:bigint ->
  ST unit 
     (requires (fun h ->
		(inHeap h a) /\ (inHeap h b) /\ (inHeap h c) /\ (inHeap h tmp)
		/\ (getLength h a = getLength h b)
		/\ (getLength h tmp = getLength h a)
		/\ (getLength h a > 0)
		/\ (getLength h c = 2 * getLength h a - 1)
		/\ (Bigint63.t a = Bigint63.t b)
		/\ (Bigint63.t a = Bigint63.t c)
		/\ (Bigint63.t a = Bigint63.t tmp)
		/\ (Bigint63.data c <> Bigint63.data a)
		/\ (Bigint63.data b <> Bigint63.data c)
		/\ (Bigint63.data tmp <> Bigint63.data a)
		/\ (Bigint63.data tmp <> Bigint63.data b)
		/\ (Bigint63.data tmp <> Bigint63.data c)
		/\ (log (getLength h a) <= wordSize a - 2)
		/\ (maxSize h a <= (wordSize a - log (getLength h a) - 2) / 2)
		/\ (maxSize h b <= (wordSize b - log (getLength h a) - 2) / 2)
		/\ (maxSize h c <= wordSize a - 2)
		/\ (maxValue h c <= ctr * maxValue h a * maxValue h b)
		/\ (ctr < getLength h a)
	       ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a) /\ (inHeap h1 a) /\ (inHeap h0 b) /\ (inHeap h1 b) /\ (inHeap h0 c) /\ (inHeap h1 c)
	       /\ (inHeap h0 tmp) /\ (inHeap h1 tmp)
	       /\ (getLength h0 a = getLength h0 b)
	       /\ (getLength h0 tmp = getLength h0 a)
	       /\ (getLength h1 tmp = getLength h0 tmp)
	       /\ (getLength h0 a > 0)
	       /\ (getLength h1 c = 2 * getLength h0 a - 1)
	       /\ (ctr < getLength h0 a)
	       /\ (Bigint63.t a = Bigint63.t b)
	       /\ (Bigint63.t a = Bigint63.t c)
	       /\ (Bigint63.t a = Bigint63.t tmp)
	       /\ (Bigint63.data c <> Bigint63.data a)
	       /\ (Bigint63.data b <> Bigint63.data c)
	       /\ (Bigint63.data tmp <> Bigint63.data a)
	       /\ (Bigint63.data tmp <> Bigint63.data b)
	       /\ (Bigint63.data tmp <> Bigint63.data c)
	       /\ (modifies !{Bigint63.data c,Bigint63.data tmp} h0 h1)
	       /\ (log (getLength h0 a) <= wordSize a - 2)
	       /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 b <= (wordSize b - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 c <= wordSize a - 2)
	       /\ (maxSize h1 c <= wordSize a - 2)
	       /\ (maxValue h0 c <= ctr * maxValue h0 a * maxValue h0 b)
	       /\ (maxValue h1 c <= (ctr+1) * maxValue h0 a * maxValue h0 b)
	       /\ (eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * getValue h0 b ctr * pow2 (bitweight (Bigint63.t a) ctr) + eval h0 c (getLength h0 c))
     ))
   
let multiplication_step a b ctr c tmp =
  let h0 = 
    erase (ST.get()) in
  let n = 
    erase (getSize h0 b ctr) in
  let s = Bigint.get b ctr in
  let tmp_seq = 
    erase (Array.to_seq (Bigint63.data tmp)) in
	  (*
  erase (
      max_size_lemma h0 a ((wordSize a - 2)/2);
      cut ((forall (n:nat). n < getLength h0 a ==> getSize h0 a n <= (wordSize a) / 2))
    );
	   *)
  let len = get_length a in
  scalar_multiplication_tr tmp tmp_seq a 0 n s len 0;
  let h1 = 
    erase (ST.get()) in	 
  erase 
    ( 
      (* Infer additional information on values and sizes of tmp *)
      scalar_multiplication_max_value_lemma h0 h1 tmp a n s;
      scalar_multiplication_max_size_lemma h0 h1 tmp a n s;
      cut (True /\ maxSize h1 tmp <= wordSize a - 2);
      cut (True /\ maxValue h1 tmp = maxValue h0 a * abs s );
      auxiliary_lemma_4 h0 h1 c c;
      cut (True /\ maxSize h1 c <= wordSize a - 2);
      cut (True /\ maxValue h1 c = maxValue h0 c)
    );
  addition_tr (erase (Array.to_seq (Bigint63.data c))) c ctr tmp 0 len 0;
  let h2 = 
    erase (ST.get()) in
  erase 
    (
      (* Infer additional information on values and sizes of c *)
      (* Timeout important required ( > 200 ) *)
      addition_max_value_lemma_extended h1 h2 c tmp c ctr len;
      cut (True /\ maxValue h2 c <= maxValue h1 c + maxValue h0 a * abs s);

      auxiliary_lemma_6 h0 h1 c c;
      mul_incr_lemma (maxValue h0 a) (abs s) (maxValue h0 b);
      cut (True /\ maxValue h2 c <= maxValue h0 c + maxValue h0 a * maxValue h0 b);

      cut (True /\ maxValue h2 c <= ctr * maxValue h0 a * maxValue h0 b + maxValue h0 a * maxValue h0 b);

      paren_mul_right ctr (maxValue h0 a) (maxValue h0 b);
      helper_lemma_1 (maxValue h0 a * maxValue h0 b);
      distributivity_add_left ctr 1 (maxValue h0 a * maxValue h0 b);
      
      cut (True /\ maxValue h2 c <= (ctr+1) * (maxValue h0 a * maxValue h0 b));
      
      (* Prove the eval property *)

      cut (inHeap h1 c /\ inHeap h1 tmp /\ inHeap h2 c);
      cut (Bigint63.t c = Bigint63.t tmp /\ True);
      cut (getLength h1 tmp >= len /\ getLength h1 c >= len + ctr);
      cut (getLength h1 c = getLength h2 c /\ True);
      cut ( forall (i:nat). 
	      ((i < len ==> getValue h2 c (i+ctr) = getValue h1 c (i+ctr) + getValue h1 tmp i)
	       /\ ((i < ctr) ==> getValue h2 c i = getValue h1 c i)));
      multiplication_step_lemma h1 h2 c tmp c ctr len;

      cut (True /\ eval h2 c (len+ctr) = eval h1 c (len+ctr) + pow2 (bitweight (Bigint63.t a) ctr) * eval h1 tmp len);
  
      cut (inHeap h1 c /\ inHeap h2 c);
      cut (getLength h1 c = getLength h2 c /\ True);
      cut ( len+ctr <= getLength h1 c /\ True);
      
      cut (forall (i:nat). (i >= len+ctr /\ i < getLength h2 c)
	   ==> getValue h1 c i = getValue h2 c i);
      
      auxiliary_lemma_5 h1 h2 c c (pow2 (bitweight (Bigint63.t a) ctr) * eval h1 tmp len) (ctr+len) (getLength h1 c);

      cut (True /\ eval h2 c (getLength h1 c) = eval h1 c (getLength h1 c) + pow2 (bitweight (Bigint63.t a) ctr) * eval h1 tmp len);
      
      (* Resize the resulting array appropriatly, according to the bound computed on its maximum value *)
      cut (inHeap h2 a /\ inHeap h2 b /\ inHeap h2 c);
      cut (getLength h2 a > 0 /\ True);
      auxiliary_lemma_6 h0 h2 a a;
      auxiliary_lemma_6 h0 h2 b b;
      
      multiplication_step_resize a b (ctr+1) c;
      (* Verified up to this ponit *)
      
      
      let h3 = ST.get() in
      admit () ) (*
      cut (inHeap h3 a /\ inHeap h3 b /\ inHeap h3 c /\ inHeap h3 tmp);
      cut (getLength h0 a = getLength h3 a /\ True);
      cut (getLength h0 b = getLength h3 b /\ True);
      cut (getLength h0 c = getLength h3 c /\ True);
      cut (modifies !{Bigint63.data c, Bigint63.data tmp} h0 h3);
            
      auxiliary_lemma_6 h2 h3 c c;
      eval_eq_lemma h2 h3 c c (getLength h3 c);
      admit () ) (*
      cut (maxValue h3 c <= (ctr+1) * (maxValue h0 a * maxValue h0 b) /\ True);
      cut (eval h3 c (getLength h3 c) = eval h0 a (getLength h0 a) * getValue h0 b ctr * pow2 (bitweight (Bigint63.t a) ctr) + eval h0 c (getLength h0 c) /\ True);
            
      ()
    );
  ()


(*

(* Lemma : factorizes "eval" equation *)
assume val multiplication_step_lemma_2:
  h0:heap ->
  h1:heap ->
  a:norm_bigint{ (inHeap h0 a)
		 /\ (getLength h0 a > 0) } -> 
  b:norm_bigint{ (inHeap h0 b)
		 /\ (SameFormat h0 h0 a b) } ->
  ctr:pos{ (ctr <= getLength h0 a) } ->
  c:norm_bigint{ (inHeap h1 c)
		 /\ (getLength h1 c = 2 * getLength h0 a - 1)
		 /\ (Bigint63.t c = Bigint63.t a) } ->
  Lemma
    (requires (eval h1 c (getLength h1 c) = (eval h0 a (getLength h0 a) * getValue h0 b (getLength h0 a - ctr)) * pow2 (bitweight (Bigint63.t a) (getLength h0 a - ctr)) + eval h0 a (getLength h0 a) * eval h0 b (getLength h0 b - ctr) ))
    (ensures ( eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * eval h0 b (getLength h0 a - ctr + 1)))
(*
let multiplication_step_lemma_2 h0 h1 a b ctr c =
  let t = Bigint63.t a in
  let len_a = getLength h0 a in
  paren_mul_left (eval h0 a len_a) (getValue h0 b (len_a - ctr)) (pow2 (bitweight t (len_a - ctr)));
  cut (True /\ eval h1 c (getLength h1 c) = eval h0 a len_a * getValue h0 b (len_a - ctr) * pow2 (bitweight t (len_a - ctr)) + eval h0 a len_a * eval h0 b (len_a - ctr) );
  swap_mul (getValue h0 b (len_a - ctr)) (pow2 (bitweight t (len_a - ctr)));
  cut (True /\ eval h1 c (getLength h1 c) = eval h0 a len_a * pow2 (bitweight t (len_a - ctr)) * getValue h0 b (len_a - ctr) + eval h0 a len_a * eval h0 b (len_a - ctr) ) ;
  (* Verified up to this point *)
  distributivity_add_right (eval h0 a len_a) (pow2 (bitweight t (len_a - ctr)) * getValue h0 b (len_a - ctr)) (eval h0 b (len_a - ctr));
  cut (True /\ eval h1 c (getLength h1 c) = eval h0 a len_a * (pow2 (bitweight t (len_a - ctr)) * getValue h0 b (len_a - ctr) + eval h0 b (len_a - ctr))) ;
  () 
 *)

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_7: a:int -> b:int -> c:int -> Lemma (ensures (a-(b-c)=a-b+c))
let auxiliary_lemma_7 a b c = ()

(* Code : tail recursive calls to run the multiplication *)
assume val multiplication_aux:
  a:norm_bigint -> b:norm_bigint -> ctr:nat -> c:norm_bigint -> tmp:norm_bigint ->
  ST unit
     (requires (fun h -> 
		(inHeap h a) /\ (inHeap h b) /\ (inHeap h c) /\ (inHeap h tmp)
		/\ (getLength h a = getLength h b)
		/\ (getLength h tmp = getLength h a)
		/\ (getLength h a > 0)
		/\ (getLength h c = 2 * getLength h a - 1)
		/\ (Bigint63.t a = Bigint63.t b) 
		/\ (Bigint63.t a = Bigint63.t c) 
		/\ (Bigint63.t tmp = Bigint63.t a)
		/\ (Bigint63.data c <> Bigint63.data a)	
		/\ (Bigint63.data b <> Bigint63.data c)
		/\ (Bigint63.data tmp <> Bigint63.data a) 
		/\ (Bigint63.data tmp <> Bigint63.data b) 
		/\ (Bigint63.data tmp <> Bigint63.data c)
		/\ (log (getLength h a) <= wordSize a - 2)
		/\ (maxSize h a <= (wordSize a - log (getLength h a) - 2) / 2)
		/\ (maxSize h b <= (wordSize b - log (getLength h a) - 2) / 2)
		/\ (ctr <= getLength h a)
		/\ (maxSize h c <= wordSize a - 2)
		/\ (maxValue h c <= (getLength h a - ctr) * (maxValue h a * maxValue h b))
		/\ (eval h c (getLength h c) = eval h a (getLength h a) * eval h b (getLength h a - ctr))
     ))
     (ensures (fun h0 u h1 -> 
	       (inHeap h0 a) /\ (inHeap h1 a)
	       /\ (inHeap h0 b) /\ (inHeap h1 b)
	       /\ (inHeap h0 c) /\ (inHeap h1 c)
	       /\ (getLength h0 a = getLength h0 b)
	       /\ (getLength h0 a > 0)
	       /\ (getLength h1 c = 2 * getLength h0 a - 1)
	       /\ (ctr <= getLength h0 a)
	       /\ (Bigint63.t a = Bigint63.t b)
	       /\ (Bigint63.t a = Bigint63.t c)
	       /\ (Bigint63.t tmp = Bigint63.t a)
	       /\ (Bigint63.data c <> Bigint63.data a)
	       /\ (Bigint63.data b <> Bigint63.data c)
	       /\ (Bigint63.data tmp <> Bigint63.data a)
	       /\ (Bigint63.data tmp <> Bigint63.data b)
	       /\ (Bigint63.data tmp <> Bigint63.data c)	
	       /\ (modifies !{Bigint63.data c, Bigint63.data tmp} h0 h1)
	       /\ (log (getLength h0 a) <= wordSize a - 2)
	       /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 b <= (wordSize b - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h1 c <= wordSize a - 2)
	       /\ (eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * eval h0 b (getLength h0 b))
     ))
(*
let rec multiplication_aux a b ctr c tmp = 
  match ctr with
  | 0 -> ()
  | _ -> 
     let h0 = 
       erase (ST.get()) in
     multiplication_step a b (get_length a - ctr) c tmp;
     let h1 = 
       erase (ST.get()) in
     erase (
	 eval_eq_lemma h0 h1 a a (getLength h0 a);
	 eval_eq_lemma h0 h1 b b (getLength h0 a);
	 auxiliary_lemma_6 h0 h1 a a;
	 auxiliary_lemma_6 h0 h1 b b;

	 cut (SameFormat h1 h1 a b);
	 cut (getLength h1 c = getLength h0 c /\ True);
														   cut ( True /\ eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * getValue h0 b (getLength h0 a - ctr) * pow2 (bitweight (Bigint63.t a) (getLength h0 a - ctr)) + eval h0 c (getLength h0 c) );
														   paren_mul_left (eval h0 a (getLength h0 a)) (getValue h0 b (getLength h0 a - ctr)) (pow2 (bitweight (Bigint63.t a) (getLength h0 a - ctr)));
	 
	 multiplication_step_lemma_2 h0 h1 a b ctr c;
	 parenSub (getLength h0 a) ctr 1;
	 
	 cut (inHeap h1 a 
           /\ inHeap h1 b 
           /\ inHeap h1 c 
           /\ inHeap h1 tmp);
         cut (getLength h1 a = getLength h1 b 
           /\ getLength h1 tmp = getLength h1 a 
           /\ getLength h1 a > 0 
           /\ getLength h1 c = 2 * getLength h1 a - 1 );
	 cut (  (Bigint63.t a = Bigint63.t b) 
		/\ (Bigint63.t a = Bigint63.t c) 
		/\ (Bigint63.t tmp = Bigint63.t a)
		/\ (Bigint63.data c <> Bigint63.data a)	
		/\ (Bigint63.data b <> Bigint63.data c)
		/\ (Bigint63.data tmp <> Bigint63.data a) 
		/\ (Bigint63.data tmp <> Bigint63.data b) 
		/\ (Bigint63.data tmp <> Bigint63.data c) );
	 cut (log (getLength h1 a) <= wordSize a - 2 /\ True);
	 cut (maxSize h1 a <= (wordSize a - log (getLength h1 a) - 2) / 2 
           /\ maxSize h1 b <= (wordSize a - log (getLength h1 a) - 2) / 2 );
	 cut (ctr - 1 <= getLength h1 a /\ True);
	 cut (maxSize h1 c <= wordSize a - 2 /\ True);
	 
	 auxiliary_lemma_7 (getLength h1 a) ctr 1;
	 auxiliary_lemma_7 (getLength h0 a) ctr 1;

	 cut (maxValue h1 c <= (getLength h1 a - (ctr - 1)) * (maxValue h1 a * maxValue h1 b) /\ True);
	 cut (eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * eval h0 b (getLength h0 a - ctr + 1) /\ True);
	 
	 eval_eq_lemma h0 h1 a a (getLength h1 a);
	 eval_eq_lemma h0 h1 b b (getLength h1 a - ctr + 1);

	 cut (eval h1 c (getLength h1 c) = eval h1 a (getLength h1 a) * eval h1 b (getLength h1 a - (ctr - 1)) /\ True)
	     
       );
     multiplication_aux a b (ctr-1) c tmp
 *)


(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_8: 
  unit -> Lemma (ensures (forall a b. a = 0 ==> (a * b = 0 /\ b * a = 0)))
let auxiliary_lemma_8 () = ()

(* Helper lemma, ensures clause is self explainatory *)
val auxiliary_lemma_9 : a:int -> Lemma (ensures (a - a = 0))
let auxiliary_lemma_9 a = ()

(* Code : core multiplication function *)
(* NB : the temporary allocated array is not freed *)
val multiplication:
  c:norm_bigint -> a:norm_bigint -> b:norm_bigint -> 
  ST unit
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h b)
		/\ (inHeap h c)
		/\ (getLength h a = getLength h b)
		/\ (getLength h a > 0)
		/\ (getLength h c = 2 * getLength h a - 1)
		/\ (maxSize h c <= wordSize a - 2)
		/\ (IsNull h c)
		/\ (Bigint63.t a = Bigint63.t b)
		/\ (Bigint63.t a = Bigint63.t c)
		/\ (Bigint63.data c <> Bigint63.data a)
		/\ (Bigint63.data b <> Bigint63.data c)
                /\ (wordSize a  - 2 >= log (getLength h a))
		/\ (maxSize h a <= (wordSize a - log (getLength h a) - 2) / 2)
		/\ (maxSize h b <= (wordSize b - log (getLength h a) - 2) / 2)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a) /\ (inHeap h1 a)
	       /\ (inHeap h0 b) /\ (inHeap h1 b)
	       /\ (inHeap h0 c) /\ (inHeap h1 c)
	       /\ (getLength h0 a = getLength h0 b)
	       /\ (getLength h0 a > 0)
	       /\ (getLength h1 c = 2 * getLength h0 a - 1)
	       /\ (IsNull h0 c)
	       /\ (Bigint63.t a = Bigint63.t b)
	       /\ (Bigint63.t a = Bigint63.t c)
	       /\ (Bigint63.data c <> Bigint63.data a)
	       /\ (Bigint63.data b <> Bigint63.data c)
	       /\ (modifies !{Bigint63.data c} h0 h1)
               /\ (wordSize a  - 2 >= log (getLength h0 a))
	       /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 b <= (wordSize b - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 c <= wordSize a - 2)
	       /\ (maxSize h1 c <= wordSize a - 2)
	       /\ (eval h1 c (getLength h1 c) = eval h0 a (getLength h0 a) * eval h0 b (getLength h0 b))
     ))
let multiplication c a b =
  //let tmp = get_from_pool (get_length a) in
  let h0 = 
    erase (ST.get()) in
  let tmp = Array.create (get_length a) zero_tint in
  let tmp2 = Bigint63 tmp (Bigint63.t a) in
  let h1 = 
    erase (ST.get()) in
  
  eval_null h1 c (getLength h1 c);
  max_value_of_null_lemma h1 c;
  auxiliary_lemma_8 ();
  auxiliary_lemma_9 (getLength h1 a);
  
  cut (eval h1 c (getLength h1 c) = 0 /\ True);
  cut (eval h1 a (getLength h1 a) * eval h1 b (getLength h1 a - (getLength h1 a)) = 0 /\ True);
  cut (eval h1 c (getLength h1 c) = eval h1 a (getLength h1 a) * eval h1 b (getLength h1 a - (getLength h1 a)) /\ True);
  cut (maxValue h1 c = 0 /\ True);
  cut ((getLength h1 a - (getLength h1 a)) * (maxValue h1 a * maxValue h1 b) = 0 /\ True);
  cut (maxValue h1 c <= (getLength h1 a - (getLength h1 a)) * (maxValue h1 a * maxValue h1 b) /\ True);
  cut (inHeap h1 a /\ inHeap h1 b /\ inHeap h1 c /\ inHeap h1 tmp2);
  cut (getLength h1 a = getLength h1 b /\ getLength h1 tmp2 = getLength h1 a);
  cut (getLength h1 a > 0 /\ getLength h1 c = 2 * getLength h1 a - 1);
  let len = get_length a in
  cut (getLength h1 a = len /\ True);
  cut ( (Bigint63.t a = Bigint63.t b) 
	/\ (Bigint63.t a = Bigint63.t c) 
	/\ (Bigint63.t tmp2 = Bigint63.t a)
	/\ (Bigint63.data c <> Bigint63.data a)	
	/\ (Bigint63.data b <> Bigint63.data c)
	/\ (Bigint63.data tmp2 <> Bigint63.data a) 
	/\ (Bigint63.data tmp2 <> Bigint63.data b) 
	/\ (Bigint63.data tmp2 <> Bigint63.data c) );
  cut ( log (getLength h1 a) <= wordSize a - 2 /\ True);
  cut ( maxSize h1 a <= (wordSize a - log (getLength h1 a) - 2) / 2
			/\ maxSize h1 b <= (wordSize b - log (getLength h1 a) - 2) / 2);
  cut (len <= getLength h1 a /\ True);
  cut (maxSize h1 c <= wordSize a - 2 /\ True);
  cut (maxValue h1 c <= (getLength h1 a - len) * (maxValue h1 a * maxValue h1 b) /\ True);
  cut (eval h1 c (getLength h1 c) = eval h1 a (getLength h1 a) * eval h1 b (getLength h1 a - len) /\ True);
  
  multiplication_aux a b len c tmp2;
  let h2 = 
    erase (ST.get() ) in
  //cut (modifies !{Bigint63.data c} h0 h2);
  
  cut ((inHeap h0 a) /\ (inHeap h2 a)
	       /\ (inHeap h0 b) /\ (inHeap h2 b)
	       /\ (inHeap h0 c) /\ (inHeap h2 c) );
  cut (getLength h0 a = getLength h0 b    /\ (getLength h0 a > 0) /\ (getLength h2 c = 2 * getLength h0 a - 1));
  cut (IsNull h0 c  /\ (Bigint63.t a = Bigint63.t b)
	       /\ (Bigint63.t a = Bigint63.t c)
	       /\ (Bigint63.data c <> Bigint63.data a)
	       /\ (Bigint63.data b <> Bigint63.data c) );

  cut ( (wordSize a  - 2 >= log (getLength h0 a))
	       /\ (maxSize h0 a <= (wordSize a - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 b <= (wordSize b - log (getLength h0 a) - 2) / 2)
	       /\ (maxSize h0 c <= wordSize a - 2)
	       /\ (maxSize h2 c <= wordSize a - 2) );

  eval_eq_lemma h0 h1 a a (getLength h0 a);
  eval_eq_lemma h0 h1 b b (getLength h0 b);
  
  cut ( eval h2 c (getLength h2 c) = eval h0 a (getLength h0 a) * eval h0 b (getLength h0 b) /\ True);

  cut ( modifies !{Bigint63.data c} h0 h2 );
  //return_to_pool (Bigint63.data tmp2);
  ()


