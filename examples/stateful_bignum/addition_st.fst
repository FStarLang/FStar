(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Addition --z3timeout 150;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst eval_st.fst;
  --*)

module Addition

open IntLib
open Limb
open FStar.Seq
open Eval
open Axiomatic
open FStar.ST
open FStar.Heap
open FStar.Ghost
open Bigint

(* 
   Auxiliary addition function. 
   Takes two input arrays, the current index for the computation and the temporary result 
 *)

(* Auxiliary addition function putting the result in the first operand *)
(* Code, not tailrecursive, proof without witness *)
val addition:
  a:bigint -> a_idx:nat ->  b:bigint -> b_idx:nat -> len:nat ->
  ST unit
    (requires (fun h -> 
      (inHeap h a)
      /\ (inHeap h b)
      /\ (Bigint63.data a <> Bigint63.data b)
      /\ (getLength h a >= a_idx + len)
      /\ (getLength h b >= b_idx + len)
      /\ (maxSize h a <= wordSize a - 2)
      /\ (maxSize h b <= wordSize a - 2)
    ))
    (ensures (fun h0 u h1 -> 
	      (inHeap h1 a)
	      /\ (inHeap h1 b)
	      /\ (inHeap h0 a)
	      /\ (inHeap h0 b)
	      /\ (Bigint63.data a <> Bigint63.data b)

	      /\ (modifies !{Bigint63.data a} h0 h1)
		 
	      /\ (maxSize h0 a <= wordSize a - 2)
	      /\ (maxSize h0 b <= wordSize a - 2)
	      /\ (getLength h1 a = getLength h0 a)
	      /\ (getLength h1 b  = getLength h0 b)
	      /\ (getLength h0 a >= a_idx + len)
	      /\ (getLength h0 b >= b_idx + len)

	      /\ (forall (i:nat).
		  i < len ==> 
		    getValue h1 a (i+a_idx) = getValue h0 a (i+a_idx) + getValue h0 b (i+b_idx)) 
		 
	      /\ (forall (i:nat).
		  (i < getLength h1 a /\ (i < a_idx \/ i >= a_idx + len)) ==> 
		    getValue h1 a i = getValue h0 a i)
		 
	      /\ (forall (i:nat).
		  i < len ==> 
		    getSize h1 a (i+a_idx) = max (getSize h0 a (i+a_idx)) (getSize h0 b (i+b_idx)) + 1)
		 
	      /\ (forall (i:nat).
		  (i < getLength h1 a /\ (i < a_idx \/ i >= a_idx + len)) ==> 
		    getSize h1 a i = getSize h0 a i)
 
))
let rec addition a a_idx b b_idx len =
  match len with
  | 0 -> ()
  |  _ -> 
      let h0 = ST.get() in
      addition a a_idx b b_idx (len-1);
      let h1 =
	(ST.get ()) in
      let ai = Bigint.get a (a_idx+len-1) in
      let size_ai =
	(getSize h1 a (a_idx+len-1)) in
      let bi = Bigint.get b (b_idx+len-1) in
      let size_bi = 
	(getSize h1 b (b_idx+len-1)) in
      let v = Limb.add size_ai ai size_bi bi in
      order_n_bits v (max size_ai size_bi + 1) (wordSize a - 1);
      let (t:tint (wordSize a)) = mk_tint a ((max size_ai size_bi + 1))  v in
      let h1 = ST.get() in
      updateBigint a (a_idx+len-1) t

(* Code *)
(* Tail recursive version of the addition *)
val addition_tr:
  ghost_a:seq (tint ocaml63) -> a:bigint -> a_idx:nat ->  b:bigint -> b_idx:nat -> len:nat -> ctr:nat ->
  ST unit
    (requires (fun h -> 
	       (inHeap h a) 
	       /\ (inHeap h b)
	       /\ (Bigint63.data a <> Bigint63.data b)
	       /\ (getLength h a >= a_idx + len) 
	       /\ (getLength h b >= b_idx + len)
	       /\ (Seq.length ghost_a = getLength h a)
	       /\ (ctr <= len)
	       /\ (forall (i:nat). i < Seq.length ghost_a
		   ==> dfst (Seq.index ghost_a i) <= wordSize a - 2)
	       /\ (maxSize h b <= wordSize a - 2)
	       /\ (forall (i:nat). i < ctr
		   ==> (
		      (getValue h a (a_idx+i) = dsnd (Seq.index ghost_a (a_idx+i)) + getValue h b (b_idx+i))
		      /\ (getSize h a (a_idx+i) = max (dfst (Seq.index ghost_a (a_idx+i))) (getSize h b (b_idx+i)) + 1)))
	       /\ (forall (i:nat). ( i < getLength h a /\ (i < a_idx \/ i >= a_idx + ctr))
		   ==> (getValue h a i = dsnd (Seq.index ghost_a i) /\ getSize h a i = dfst (Seq.index ghost_a i)))
    ))
    (ensures (fun h0 u h1 -> 
	      (inHeap h1 a) 
	      /\ (inHeap h1 b) 
	      /\ (inHeap h0 a) 
	      /\ (inHeap h0 b)
	      /\ (Bigint63.data a <> Bigint63.data b)
		 
	      /\ (modifies !{Bigint63.data a} h0 h1)
		 
	      /\ (forall (i:nat). i < Seq.length ghost_a
		  ==> dfst (Seq.index ghost_a i) <= wordSize a - 2)
	      /\ (maxSize h0 b <= wordSize a - 2)
	      /\ (getLength h1 a = getLength h0 a)
	      /\ (getLength h1 b  = getLength h0 b)
	      /\ (getLength h0 a >= a_idx + len)
	      /\ (getLength h0 b >= b_idx + len)
	      /\ (ctr <= len)
	      /\ (Seq.length ghost_a = getLength h0 a)
		 
	      /\ (forall (i:nat). i < len 
		  ==> ((getValue h1 a (i+a_idx) = dsnd (Seq.index ghost_a (a_idx+i)) + getValue h0 b (i+b_idx)) 
		       /\ (getSize h1 a (i+a_idx) = max (dfst (Seq.index ghost_a (a_idx+i))) (getSize h0 b (i+b_idx)) + 1)))
		 
	      /\ (forall (i:nat). (i < getLength h1 a /\ (i < a_idx \/ i >= a_idx + len)) 
		  ==> (getValue h1 a i = dsnd (Seq.index ghost_a i) /\ getSize h1 a i = dfst (Seq.index ghost_a i)))
   
))

let rec addition_tr ghost_a a a_idx b b_idx len ctr =
  match len - ctr with
  | 0 -> ()
  | _ -> 
      let i = ctr in
      let h1 =
	(ST.get ()) in
      let ai = Bigint.get a (a_idx+i) in
      let size_ai =
	(getSize h1 a (a_idx+i)) in
      let bi = Bigint.get b (b_idx+i) in
      let size_bi = 
	(getSize h1 b (b_idx+i)) in
      let v = Limb.add size_ai ai size_bi bi in
      let (t:tint (wordSize a)) = mk_tint a ((max size_ai size_bi + 1))  v in
      updateBigint a (a_idx+i) t;
      addition_tr ghost_a a a_idx b b_idx len (ctr+1);
      ()


val addition_lemma_aux:
  h0:heap ->
  h1:heap ->
  a:bigint{ (inHeap h0 a) 
	    /\ (inHeap h1 a)
	    /\ (maxSize h0 a <= wordSize a - 2) } -> 
  b:bigint{ (inHeap h0 b)
	    /\ (maxSize h0 b <= wordSize a - 2)
	    /\ (Bigint63.t b = Bigint63.t a) } ->
  len:pos{ (len <= getLength h0 a)
	   /\ (len <= getLength h0 b)
	   /\ (len <= getLength h1 a)
	   /\ (forall (i:nat). i < len 
	       ==> getValue h1 a i = getValue h0 a i + getValue h0 b i) } ->
  Lemma
    (requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
		/\ (getValue h1 a (len-1) = getValue h0 a (len-1) + getValue h0 b (len-1)) ) )
    (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let addition_lemma_aux h0 h1 a b len =
  (
      distributivity_add_right (pow2 (bitweight (Bigint63.t a) (len-1))) (getValue h0 a (len-1))  (getValue h0 b (len-1))
    )

val addition_lemma:
  h0:heap ->
  h1:heap ->
  a:bigint{ (inHeap h0 a) 
	    /\ (inHeap h1 a)
	    /\ (maxSize h0 a <= wordSize a - 2) } -> 
  b:bigint{ (inHeap h0 b)
	    /\ (maxSize h0 b <= wordSize a - 2)
	    /\ (Bigint63.t b = Bigint63.t a) } ->
  len:nat{ (len <= getLength h0 a)
	   /\ (len <= getLength h0 b)
	   /\ (len <= getLength h1 a)
	   /\ (forall (i:nat). i < len 
	       ==> getValue h1 a i = getValue h0 a i + getValue h0 b i) } ->
  Lemma
    (requires (True))
    (ensures ( eval h0 a len + eval h0 b len = eval h1 a len ))
let rec addition_lemma h0 h1 a b len =
  (
      match len with
      | 0 -> ()
      | _ -> addition_lemma h0 h1 a b (len-1);
	     addition_lemma_aux h0 h1 a b len
    )

val addition_max_value_lemma:
  h0:heap -> 
  h1:heap -> 
  a:bigint{ (inHeap h0 a)
	    /\ (maxSize h0 a <= wordSize a - 2) } -> 
  b:bigint{ (inHeap h0 b)
	    /\ (maxSize h0 b <= wordSize a - 2)
	    /\ (getLength h0 a = getLength h0 b) } ->
  c:bigint{ (inHeap h1 c)
	    /\ (getLength h1 c = getLength h0 a)
	    /\ (forall (i:nat). i < getLength h1 c 
		==> getValue h1 c i = getValue h0 a i + getValue h0 b i) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
let addition_max_value_lemma h0 h1 a b c = ()
  
val addition_max_size_lemma:
  h0:heap -> 
  h1:heap -> 
  a:bigint{ (inHeap h0 a) } -> 
  b:bigint{ (inHeap h0 b)
	    /\ (getLength h0 a = getLength h0 b) } ->
  c:bigint{ (inHeap h1 c)
	    /\ (getLength h1 c = getLength h0 a)
	    /\ (forall (i:nat). i < getLength h1 c 
		==> getSize h1 c i = max (getSize h0 a i) (getSize h0 b i) + 1) } ->
  Lemma
    (requires (True))
    (ensures (maxSize h1 c <= max (maxSize h0 a) (maxSize h0 b) + 1))
let addition_max_size_lemma h0 h1 a b c = ()

val max_value_lemma: h:heap -> a:bigint{ inHeap h a } -> m:nat ->
		     Lemma 
		       (requires (forall (n:nat). n < getLength h a ==> abs (getValue h a n) <= m))
		       (ensures (maxValue h a <= m))
let max_value_lemma h a m = ()

val abs_lemma: unit -> Lemma (ensures (forall a b. abs (a + b) <= abs a + abs b))
let abs_lemma () = () 

assume val addition_max_value_lemma_extended:
  h0:heap -> 
  h1:heap -> 
  a:bigint{ (inHeap h0 a) } -> 
  b:bigint{ (inHeap h0 b) } ->
  c:bigint{ (inHeap h1 c)
	    /\ (getLength h0 a = getLength h1 c) } ->
  idx:nat ->
  len:nat{ len + idx <= getLength h0 a /\ len <= getLength h0 b } ->
  Lemma
    (requires ((forall (i:nat). i < len 
		==> getValue h1 c (i+idx) = getValue h0 a (i+idx) + getValue h0 b i)
	       /\ (forall (i:nat). ( i < getLength h1 c /\ (i < idx \/ i >= idx + len))
		   ==> getValue h1 c i = getValue h0 a i)))
    (ensures (maxValue h1 c <= maxValue h0 a + maxValue h0 b))
(*
let addition_max_value_lemma_extended h0 h1 a b c idx len = 
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len))
	==> (getValue h1 c i = getValue h0 a i /\ abs (getValue h1 c i) <= maxValue h0 a + maxValue h0 b));
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len)) 
  	==> abs (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  abs_lemma ();
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ((getValue h1 c i = getValue h0 a i + getValue h0 b (i-idx)) 
	     /\ (abs (getValue h1 c i) <= abs (getValue h0 a i) + abs (getValue h0 b (i-idx)))) );
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ( abs (getValue h0 a i) <= maxValue h0 a /\ abs (getValue h0 b (i-idx)) <= maxValue h0 b));
  cut ( forall (i:nat). (i >= idx /\ i < idx + len)
	==> abs (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  cut ( forall (i:nat). i < getLength h1 c 
	==> abs (getValue h1 c i) <= maxValue h0 a + maxValue h0 b);
  max_value_lemma h1 c (maxValue h0 a + maxValue h0 b);
  ()
 *)


val addition_max_size_lemma_extended:
  h0:heap -> 
  h1:heap -> 
  a:bigint{ (inHeap h0 a) } -> 
  b:bigint{ (inHeap h0 b) } ->
  c:bigint{ (inHeap h1 c)
	    /\ (getLength h0 a = getLength h1 c) } ->
  idx:nat ->
  len:nat{ len + idx <= getLength h0 a /\ len <= getLength h0 b } ->
  Lemma
    (requires ((forall (i:nat). i < len 
		==> getSize h1 c (i+idx) = max (getSize h0 a (i+idx)) (getSize h0 b i) + 1)
	       /\ (forall (i:nat). ( i < getLength h1 c /\ (i < idx \/ i >= idx + len))
		   ==> getSize h1 c i = getSize h0 a i)))
    (ensures (maxSize h1 c <= max (maxSize h0 a) (maxSize h0 b) + 1))
let addition_max_size_lemma_extended h0 h1 a b c idx len = 
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len))
	==> (getSize h1 c i = getSize h0 a i /\ getSize h1 c i <= max (maxSize h0 a) (maxSize h0 b) + 1) );
  cut ( forall (i:nat). (i < getLength h1 c /\ (i < idx \/ i >= idx + len)) 
  	==> getSize h1 c i <= max (maxSize h0 a) (maxSize h0 b) + 1 );
  
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ((getSize h1 c i = max (getSize h0 a i) (getSize h0 b (i-idx)) + 1) 
	     /\ (getSize h1 c i <= max (getSize h0 a i) (getSize h0 b (i-idx)) + 1 )) );
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ( getSize h0 a i <= maxSize h0 a /\ getSize h0 b (i-idx) <= maxSize h0 b));
  cut ( forall (i:nat). (i >= idx /\ i < idx + len)
	==> getSize h1 c i <= max (maxSize h0 a) (maxSize h0 b) + 1 );
  cut ( forall (i:nat). i < getLength h1 c 
	==> getSize h1 c i <= max (maxSize h0 a) (maxSize h0 b) + 1 );
  ()

val addition_with_lemma:
  a:bigint -> b:bigint -> len:nat ->
  ST unit
    (requires (fun h -> 
      (inHeap h a)
      /\ (inHeap h b)
      /\ (Bigint63.data a <> Bigint63.data b)
      /\ (Bigint63.t a = Bigint63.t b)
      /\ (Seq.length (sel h (Bigint63.data a)) >= len)
      /\ (Seq.length (sel h (Bigint63.data b)) >= len)
      /\ (maxSize h a <= wordSize a - 2)
      /\ (maxSize h b <= wordSize a - 2)
    ))
    (ensures (fun h0 u h1 -> 
      (inHeap h1 a)
      /\ (inHeap h1 b)
      /\ (inHeap h0 a)
      /\ (inHeap h0 b)
      /\ (modifies !{Bigint63.data a} h0 h1)
      /\ (maxSize h0 a <= wordSize a - 2)
      /\ (maxSize h0 b <= wordSize a - 2)
      /\ (Bigint63.t a = Bigint63.t b)
      /\ (Bigint63.data a <> Bigint63.data b)
      /\ (Seq.length (sel h1 (Bigint63.data a)) = Seq.length (sel h0 (Bigint63.data a)))
      /\ (Seq.length (sel h1 (Bigint63.data b)) = Seq.length (sel h0 (Bigint63.data b)))
      /\ (Seq.length (sel h1 (Bigint63.data a)) >= len)
      /\ (Seq.length (sel h1 (Bigint63.data b)) >= len)
      /\ (eval h1 a len = eval h0 a len + eval h0 b len)
      /\ (maxSize h1 a <= max (maxSize h0 a) (maxSize h0 b) + 1)
      /\ (maxValue h1 a <= maxValue h0 a + maxValue h0 b)
    ))
let addition_with_lemma a b len =
  let h0 =
    (ST.get()) in
  addition_tr ((Array.to_seq (Bigint63.data a))) a 0 b 0 len 0;
  (
      let h1 = ST.get() in
      addition_lemma h0 h1 a b len;
      addition_max_value_lemma_extended h0 h1 a b a 0 len;
      addition_max_size_lemma_extended h0 h1 a b a 0 len
    )
