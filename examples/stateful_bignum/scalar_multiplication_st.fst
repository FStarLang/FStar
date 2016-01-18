(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module ScalarMultiplication --z3timeout 150;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst eval_st.fst;
  --*)

module ScalarMultiplication

open IntLib
open Limb
open FStar.Heap
open FStar.ST
open Bigint
open FStar.Seq
open Eval
open Axiomatic

(* Lemma *)
val scalar_multiplication_lemma_aux:
  h0:heap ->
  h1:heap ->
  a:bigint{ (inHeap h0 a) } ->
  b:bigint{ (inHeap h1 b) 
	    /\ (Bigint63.t b = Bigint63.t a) } ->
  s:int ->
  len:pos{ (len <= getLength h0 a)
	   /\ (len <= getLength h1 b) } ->
  Lemma
    (requires ( (eval h0 a (len-1) * s = eval h1 b (len-1))
		/\ (getValue h0 a (len-1) * s = getValue h1 b (len-1))))
    (ensures ( eval h0 a len * s = eval h1 b len ))
let scalar_multiplication_lemma_aux h0 h1 a b s len =
  (
      paren_mul_left (pow2 (bitweight (Bigint63.t a) (len-1))) (getValue h0 a (len-1)) s;
      distributivity_add_left ((pow2 (bitweight (Bigint63.t a) (len-1))) * (getValue h0 a (len-1))) (eval h0 a (len-1)) s
    )

(* Lemma *)
val scalar_multiplication_lemma:
  h0:heap ->
  h1:heap ->
  a:bigint{ (inHeap h0 a) } ->
  b:bigint{ (inHeap h1 b)
	    /\ (Bigint63.t b = Bigint63.t a) } ->
  s:int ->
  len:nat{ (len <= getLength h0 a)
	   /\ (len <= getLength h1 b) } ->
  Lemma
    (requires ( forall (i:nat). i < len ==> getValue h0 a i * s = getValue h1 b i ))
    (ensures ( eval h0 a len * s = eval h1 b len ))
let rec scalar_multiplication_lemma h0 h1 a b s len =
  (
      match len with
      | 0 -> ()
      | _ -> scalar_multiplication_lemma h0 h1 a b s (len-1); scalar_multiplication_lemma_aux h0 h1 a b s len
    )

(* Code *)
(* Scalar multiplication, puts result in the first argument *)
(* Non tailrecursive version, straightforward proof, less efficient code *)
val scalar_multiplication:
  res:bigint -> a:bigint -> a_idx:nat -> n:nat -> s:lint n -> len:nat -> 
  ST unit
     (requires (fun h -> (inHeap h res)
			 /\ (inHeap h a)
			 /\ (Bigint63.data res <> Bigint63.data a)
			 /\ (getLength h a >= a_idx + len)
			 /\ (getLength h res = getLength h a)
			 /\ (maxSize h a <= (wordSize a - 1) / 2)
			 /\ (n <= (wordSize a - 1) / 2)))
     (ensures (fun h0 u h1 -> (inHeap h0 res)
			      /\ (inHeap h1 res)
			      /\ (inHeap h0 a)
			      /\ (inHeap h1 a)
			      /\ (Bigint63.data res <> Bigint63.data a)
			      /\ (modifies !{Bigint63.data res} h0 h1)
			      /\ (getLength h0 a >= a_idx + len)
			      /\ (maxSize h0 a <= (wordSize a - 1) / 2)
			      /\ (maxSize h1 a <= (wordSize a - 1) / 2)
			      /\ (n <= (wordSize a - 1) / 2)
			      /\ (getLength h0 res = getLength h0 a)
			      /\ (getLength h1 res = getLength h0 res)
			      /\ (forall (i:nat). i < len 
				  ==> (getValue h1 res (a_idx + i) = getValue h0 a (a_idx + i) * s)
				      /\ (getSize h1 res (a_idx + i) = getSize h0 a (a_idx + i) + n))
			      /\ (forall (i:nat). (i < getLength h1 res /\ (i < a_idx \/ i >= a_idx + len))
				  ==> (getValue h1 res i = getValue h0 res i /\ getSize h1 res i = getSize h0 res i))
 
     ))

let rec scalar_multiplication res a a_idx n s len =
  match len with
  | 0 -> ()
  |  _ -> 
     let h0 = 
       (ST.get()) in
     scalar_multiplication res a a_idx n s (len-1);
     let h1 = 
       (ST.get ()) in
     let i = len-1 in
     let ai = get a (a_idx + i) in
     let size_ai = 
       (getSize h1 a (a_idx +i)) in
     let v = Limb.mul size_ai ai n s in
     
       ( order_n_bits v (size_ai+n) (wordSize a - 1));
     let (t:tint (wordSize a)) = mk_tint res ((size_ai + n)) v in     
     updateBigint res (a_idx+i) t


(* Code *)
(* Tail recursive version of the scalar multiplication *)
val scalar_multiplication_tr:
  res:bigint -> ghost_res:seq (tint ocaml63) -> a:bigint -> a_idx:nat -> n:nat -> s:lint n -> len:nat -> ctr:nat -> 
  ST unit
     (requires (fun h -> 
		(inHeap h res)
		/\ (inHeap h a)
		/\ (Bigint63.data res <> Bigint63.data a)
		/\ (getLength h a >= a_idx + len)
		/\ (getLength h res = getLength h a)
		/\ (Seq.length ghost_res = getLength h res)
		/\ (ctr <= len)
		/\ (maxSize h a <= (wordSize a - 1) / 2)
		/\ (n <= (wordSize a - 1) / 2)
		/\ (forall (i:nat). i < ctr 
		    ==> ((getValue h res (a_idx + i) = getValue h a (a_idx + i) * s)
				 /\ (getSize h res (a_idx + i) = getSize h a (a_idx + i) + n)))
		/\ (forall (i:nat). (i < getLength h res /\ (i < a_idx \/ i >= a_idx + ctr))
		    ==> (getValue h res i = dsnd (Seq.index ghost_res i) /\ getSize h res i = dfst (Seq.index ghost_res i)))
		   
     ))
     (ensures (fun h0 u h1 -> 
	       (inHeap h0 res)
	       /\ (inHeap h1 res)
	       /\ (inHeap h0 a)
	       /\ (inHeap h1 a)
	       /\ (Bigint63.data res <> Bigint63.data a)
	       /\ (modifies !{Bigint63.data res} h0 h1)
	       /\ (getLength h0 a >= a_idx + len)
	       /\ (maxSize h0 a <= (wordSize a - 1) / 2)
	       /\ (maxSize h1 a <= (wordSize a - 1) / 2)
	       /\ (n <= (wordSize a - 1) / 2)
	       /\ (getLength h0 res = getLength h0 a)
	       /\ (getLength h1 res = getLength h0 res)
	       /\ (Seq.length ghost_res = getLength h0 res)
	       /\ (ctr <= len)
	       /\ (forall (i:nat). i < len 
		   ==> (getValue h1 res (a_idx + i) = getValue h0 a (a_idx + i) * s)
		       /\ (getSize h1 res (a_idx + i) = getSize h0 a (a_idx + i) + n))
	       /\ (forall (i:nat). (i < getLength h1 res /\ (i < a_idx \/ i >= a_idx + len))
		   ==> (getValue h1 res i = getValue h0 res i /\ getSize h1 res i = getSize h0 res i))
 
     ))
let rec scalar_multiplication_tr res ghost_res a a_idx n s len ctr =
  match len - ctr with
  | 0 -> ()
  |  _ -> 
     let h1 = 
       (ST.get ()) in
     let i = ctr in
     let ai = get a (a_idx + i) in
     let size_ai = 
       (getSize h1 a (a_idx +i)) in
     let v = Limb.mul size_ai ai n s in
     let (t:tint (wordSize a)) = mk_tint res ((size_ai + n)) v in     
     updateBigint res (a_idx+i) t;
     let h2 = (ST.get()) in
     scalar_multiplication_tr res ghost_res a a_idx n s len (ctr+1)
		      

(* Lemma *)   	 
val theorem_scalar_multiplication: 
  h0:heap ->
  h1:heap ->
  a:bigint{ (inHeap h0 a)
	    /\ (maxSize h0 a <= (wordSize a - 1) / 2) } ->
  n:nat{ n <= (wordSize a - 1) / 2 } ->
  s:lint n ->
  len:nat{len <= getLength h0 a} ->
  b:bigint{ (inHeap h1 b)
	    /\ (getLength h0 a = getLength h1 b) 
	    /\ (Bigint63.t a = Bigint63.t b)} ->
  Lemma 
    (requires ((forall (i:nat). i < len 
		==> (getValue h1 b i = getValue h0 a i * s)
		    /\ (getSize h1 b i = getSize h0 a i + n))))
    ( ensures ( (eval h1 b len) = (eval h0 a len) * s ) )
let theorem_scalar_multiplication h0 h1 a n s len b = 
  (
      scalar_multiplication_lemma h0 h1 a b s len; ()
    )
	
val scalar_multiplication_with_lemma:
  res:bigint -> a:bigint -> n:nat -> s:lint n -> len:nat -> 
  ST unit
     (requires (fun h -> (inHeap h res)
			 /\ (inHeap h a)
			 /\ (Bigint63.data res <> Bigint63.data a)
			 /\ (Bigint63.t res = Bigint63.t a)
			 /\ (getLength h a >= len)
			 /\ (getLength h res = getLength h a)
			 /\ (maxSize h a <= (wordSize a - 1) / 2)
			 /\ (n <= (wordSize a - 1) / 2)))
     (ensures (fun h0 u h1 -> (inHeap h0 res)
			      /\ (inHeap h1 res)
			      /\ (inHeap h0 a)
			      /\ (inHeap h1 a)
			      /\ (Bigint63.data res <> Bigint63.data a)
			      /\ (modifies !{Bigint63.data res} h0 h1)
			      /\ (getLength h0 a >= len)
			      /\ (maxSize h0 a <= (wordSize a - 1) / 2)
			      /\ (maxSize h1 a <= (wordSize a - 1) / 2)
			      /\ (n <= (wordSize a - 1) / 2)
			      /\ (getLength h0 res = getLength h0 a)
			      /\ (getLength h1 res = getLength h0 res)
			      /\ (eval h1 res len = eval h0 a len * s) 
     ))
let scalar_multiplication_with_lemma res a n s len =
  let h0 = 
    (ST.get()) in
  scalar_multiplication_tr res ((Array.to_seq (Bigint63.data res))) a 0 n s len 0;
  (
      let h1 = ST.get() in
      theorem_scalar_multiplication h0 h1 a n s len res
    )

val helper_lemma:
  unit -> Lemma
	    (requires (True))
	    (ensures ( (forall a b. abs ( a * b ) = abs a * abs b) ))
let helper_lemma () = ()

val helper_lemma_2:
  unit -> Lemma
	    (requires (True))
	    (ensures (forall a b c. abs a * abs c <= abs b * abs c ==> abs a <= abs b ))
let helper_lemma_2 () = 
  (ineq_axiom ())

val scalar_multiplication_max_value_lemma:
  h0:heap -> 
  h1:heap -> 
  res:bigint{ inHeap h1 res } -> 
  a:bigint{ (inHeap h0 a)
	    /\ (getLength h0 a = getLength h1 res) } -> 
  n:nat -> s:lint n{
	       (forall (i:nat). 
		i < getLength h1 res ==>  getValue h1 res i = getValue h0 a i * s) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 res = maxValue h0 a * abs s))
let scalar_multiplication_max_value_lemma h0 h1 res a n s = 
  ( helper_lemma () ; ineq_axiom () )

val scalar_multiplication_max_size_lemma:
  h0:heap -> 
  h1:heap -> 
  res:bigint{ inHeap h1 res } -> 
  a:bigint{ (inHeap h0 a)
	    /\ (getLength h0 a = getLength h1 res) } -> 
  n:nat -> s:lint n{
	       (forall (i:nat). 
		i < getLength h1 res ==>  getSize h1 res i = getSize h0 a i + n) } ->
  Lemma
    (requires (True))
    (ensures (maxSize h1 res = maxSize h0 a + n))
let scalar_multiplication_max_size_lemma h0 h1 res a n s = ()

	       
