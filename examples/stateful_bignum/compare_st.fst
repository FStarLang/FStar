(*--build-config
  options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Compare --z3timeout 150;
  other-files:classical.fst ext.fst set.fsi seq.fsi seqproperties.fst heap.fst st.fst all.fst arr.fst ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst eval_st.fst;
  --*)

module Compare

open FStar.Heap
open FStar.ST
open Bigint
open Eval

(* Bitwize operations *)
(*
assume val xor_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> x = y })
assume val and_op: x:int -> y:int -> Tot (z:int{ z = 0 <==> (x = 0 /\ y = 0)})
*)
  
(* Comparison function /!\ returns 0 if equal, and 1 if different *)
val compare_aux: a:bigint -> b:bigint -> tmp:int -> ctr:nat -> len:nat ->
		 ST nat
		    (requires (fun h ->
			       (inHeap h a)
			       /\ (inHeap h b)
			       /\ (ctr <= len)
			       /\ (len <= getLength h a)
			       /\ (len <= getLength h b)
			       /\ (tmp = 0 <==> (forall (i:nat). (i < len /\ i >= ctr)
						 ==> getValue h a i = getValue h b i))
		    ))
		    (ensures (fun h0 n h1 ->
			      (inHeap h0 a)
			       /\ (inHeap h0 b)
			       /\ (ctr <= len)
			       /\ (len <= getLength h0 a)
			       /\ (len <= getLength h0 b)
			       /\ (modifies !{} h0 h1)
			       /\ (n = 0 <==> (forall (i:nat). i < len
					       ==> getValue h0 a i = getValue h0 b i))
		    ))
let rec compare_aux a b tmp ctr len =
  match ctr with
  | 0 -> if tmp = 0 then 0 else 1 (* Can be replace with some constant bitwize operation *)
  | _ ->
     let h0 =
       (ST.get()) in
     let i = ctr - 1 in
     let ai = get a i in
     let bi = get b i in
     let tmp' = IntLib.and_op tmp (IntLib.xor_op ai bi) in
     compare_aux a b tmp' (ctr-1) len

val compare: a:bigint -> b:bigint -> 
	     ST nat
		(requires (fun h -> 
			   (inHeap h a)
			   /\ (inHeap h b)
			   /\ (SameFormat h h a b)
		))
		(ensures (fun h0 r h1 ->
			  (inHeap h0 a)
			  /\ (inHeap h0 b)
			  /\ (SameFormat h0 h0 a b)
			  /\ (modifies !{} h0 h1)
			  /\ ( r = 0 <==> (forall (i:nat). i < getLength h0 b
					   ==> getValue h0 b i = getValue h0 a i)
			     )
			  /\ (r = 0 ==> eval h0 a (getLength h0 a) = eval h0 b (getLength h0 b))
		))
let compare a b =
  let h0 = (ST.get()) in
  let r = compare_aux a b 0 (get_length a) (get_length a) in
  (
      if r = 0 then eval_eq_lemma h0 h0 a b (get_length a)
    );
  r
  
(* This is supposed to be a constant time comparison operation, returning -1 if a < b, 0 if a == b and 1 if a > b *)
(* TODO : Not verified *)
val compare2_aux:
  a:bigint -> b:bigint -> len:nat -> tmp:int ->
  ST nat
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h b)
		/\ (SameFormat h h a b)
		/\ (Normalized h a)
		/\ (Normalized h b)
		/\ (len <= getLength h a)
     ))
     (ensures (fun h0 n h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (SameFormat h0 h0 a b)
	       /\ (Normalized h0 a)
	       /\ (Normalized h0 b)
	       /\ (n = 0 <==> (forall (i:nat). i < getLength h0 b
			       ==> getValue h0 b i = getValue h0 a i))
	       /\ (n = 0 <==> eval h0 a (getLength h0 a) = eval h0 b (getLength h0 b))
     ))
let rec compare2_aux a b len tmp =
  match len with
  | 0 -> tmp
  | _ -> 
     let i = get_length a - len in
     let ai = get a i in
     let bi = get b i in
     let c = IntLib.compare ai bi in
     let minus_one = -1 in
     let tmp = 
       match c with
       | 0 -> tmp
       | minus_one -> -1
       | 1 -> 1
     in
     compare2_aux a b (len+1) tmp
     

val compare2: a:bigint -> b:bigint ->
	      ST nat
		 (requires (fun h -> 
			    (inHeap h a)
			    /\ (inHeap h b)
			    /\ (SameFormat h h a b)
		 ))
		 (ensures (fun h0 r h1 ->
			   (inHeap h0 a)
			   /\ (inHeap h0 b)
			   /\ (getLength h0 a = getLength h0 b)
			   /\ (modifies !{} h0 h1)
			   /\ (r = 0 \/ r = -1 \/ r = 1)
			   /\ (r = 0 <==> (forall (i:nat). i < getLength h0 b
					   ==> getValue h0 b i = getValue h0 a i))
			   /\ (r = 0 <==> eval h0 a (getLength h0 a) = eval h0 b (getLength h0 b))
			   /\ (r < 0 <==> eval h0 a (getLength h0 a) < eval h0 b (getLength h0 b))
			   /\ (r > 0 <==> eval h0 a (getLength h0 a) > eval h0 b (getLength h0 b))
		 ))
let compare2 a b =
  compare2_aux a b (get_length a) 0
