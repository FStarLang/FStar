(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Carry --z3timeout 120 --max_fuel 15 --max_ifuel 15 --initial_fuel 5 --initial_ifuel 5;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Array.fst FStar.Ghost.fst axiomatic.fst intlib.fst limb.fst bigint_st.fst eval_st.fst
  --*)
(* STATUS : lax type checks but not verified, work in progress *)

module Carry

open FStar.Heap 
open FStar.ST
open Limb
open Bigint
open IntLib
open FStar.Seq
open Axiomatic
open Eval
open FStar.Array


opaque val compute_size_aux :
  t:template -> bw_p_max:nat -> n:nat -> bwn:nat{ bwn = bitweight t n /\ bwn < bw_p_max } -> 
  Tot (n:pos{ bitweight t n >= bw_p_max })
    (decreases (bw_p_max - bwn))
let rec compute_size_aux t bw_p_max n bwn =
  let bwnp1 = bwn + t n in
  cut ( True /\ bwnp1 = bitweight t (n+1) );
  if bwnp1 >= bw_p_max then (n+1)
  else (
    compute_size_aux t bw_p_max (n+1) bwnp1
  )

#reset-options

(* Compute the required array length to store the carried result *)
opaque val compute_size :
  a:bigint -> 
  ST pos
    (requires (fun h -> 
      (inHeap h a)
      /\ (getLength h a > 0)
     ))
    (ensures (fun h0 n h1 -> 
      (inHeap h1 a)
      /\ (h0==h1)
      /\ (getLength h1 a > 0)
      /\ (bitweight (Bigint63.t a) n >= bitweight (Bigint63.t a) (getLength h1 a - 1) + wordSize a)
     ))
let compute_size a =
  let t = Bigint63.t a in
  let n = get_length a - 1 in
  let bwn = bitweight t n in
  let max = wordSize a in
  let bw_p_max = bwn + max in
  compute_size_aux t bw_p_max n bwn

#reset-options

opaque val carry_aux :
  a:bigint -> i:nat -> 
  ST unit
     (requires (fun h -> 
      (inHeap h a)
       /\ (getLength h a > 0)
       /\ (i < getLength h a)
       /\ (forall (j:nat). j < i
	   ==> getSize h a j <= (Bigint63.t a) j)
       /\ (i < getLength h a - 1 ==> getSize h a (getLength h a - 1) < Bigint63.t a (getLength h a - 1))
       /\ (i = getLength h a - 1 ==> getSize h a (getLength h a - 1) <= Bigint63.t a (getLength h a -1))
       /\ (forall (j:nat). (j > i /\ j < getLength h a)
	   ==> getSize h a j < wordSize a - 1)
	
      ))
    (ensures (fun h0 u h1 -> 
      (inHeap h0 a)
      /\ (inHeap h1 a)
      /\ (getLength h1 a = getLength h0 a)
      /\ (eval h0 a (getLength h0 a) = eval h1 a (getLength h1 a))
      /\ (Normalized h1 a)
      /\ (modifies !{getData a} h0 h1)
     ))

let rec carry_aux a i =
  match get_length a - i - 1 with
  | 0 -> 
     ()
  | _ -> 
     (* Original heap *)
     let h0 = (ST.get()) in
     
     (* Compute new values *)
     let ai = get a i in
     let t = Bigint63.t a in
     let ti = t i in
     let moduli = pow2 ti in
     let carry = div_non_eucl ai moduli in
     let v = signed_modulo ai moduli in
     let aip1 = get a (i+1) in

     (* Size of the carry, the trimmed cell and the upper cell *)
     (
       order_n_bits ai (getSize h0 a i) (wordSize a - 1);
       size_of_div_non_eucl_by_pow2 (wordSize a - 1) ai ti;
       size_of_signed_modulo_by_pow2 ai ti
     );
     let size_carry = (wordSize a - ti - 1) in
     let size_v = ti in
     let size_aip1 = getSize h0 a (i+1) in

     let tl = Bigint.mk_tint a size_v v in
     let vh = Limb.add size_carry carry size_aip1 aip1 in

     order_n_bits vh ((max size_carry size_aip1) + 1) (wordSize a - 1);
     let th = Bigint.mk_tint a ((wordSize a - 1)) vh in
     updateBigint a i tl;
     updateBigint a (i+1) th;

     (* Heap before iterating *)
     let h1 = ST.get() in
     
     cut (True /\ (i+1) < getLength h1 a);
     cut (True /\ inHeap h1 a);
     cut (True /\ getLength h1 a > 0);
     cut (True /\ (forall (j:nat). j < (i+1)
	     ==> getSize h1 a j <= (Bigint63.t a) j));
     cut (True /\ (i+1) < getLength h1 a - 1 ==> getSize h1 a (getLength h1 a - 1) < Bigint63.t a (getLength h1 a - 1));
     cut (True /\ (forall (j:nat). (j > (i+1) /\ j < getLength h1 a)
		      ==> getSize h1 a j < wordSize a - 1));
     
     (* TODO : prove the admited properties *)
     admitP (True /\ eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a));
     admitP (True /\ i+1 = getLength h1 a - 1 ==> getSize h1 a (getLength h1 a -1) <= Bigint63.t a (getLength h1 a - 1));

     carry_aux a (i+1)


#reset-options

(* Perform a carry operations : the array is normalized but cells can have different sizes *)
val carry : 
  a:bigint -> 
  ST bigint
     (requires (fun h -> 
       (inHeap h a)
       /\ (getLength h a > 0)
       /\ (maxSize h a < wordSize a - 1)
     ))
     (ensures (fun h0 b h1 ->
       (inHeap h0 a)
       /\ (inHeap h1 b)
       /\ (getLength h0 a > 0)
       /\ (getLength h1 b > 0)
       /\ (modifies !{} h0 h1)
       /\ (Normalized h1 b)
       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
let carry a = 
  (* Initial heap *)
  let h0 = ST.get() in

  let size = compute_size a in
  let len = get_length a in
  admitP (True /\ len < size);

  (* This is not working in OCaml because an array is not a reference *)
  (* 
     let new_array = Array.create size zero_tint in
     Array.blit (getData a) 0 new_array 0 (get_length a);
     getData a := !new_array; 
  *)
  let len = get_length a in

  let b = Bigint.extend a size in
  
  (* Intermediate heap *)
  let h1 = ST.get() in

  cut (modifies !{} h0 h1);
  
  cut (True /\ inHeap h1 b);
  cut (True /\ getLength h1 b > 0);
  cut (True /\ 0 < getLength h1 b - 1 ==> getSize h1 b (getLength h1 b - 1) < Bigint63.t b (getLength h1 b - 1));
  cut (True /\ 0 = getLength h1 b - 1 ==> getSize h1 b (getLength h1 b - 1) <= Bigint63.t b (getLength h1 b -1));

  (* TODO : prove the admitted properties *)
  admitP (True /\ eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a));
  admitP (True /\ (forall (j:nat). (j > 0 /\ j < getLength h1 b)
	  ==> getSize h1 b j < wordSize b - 1));

  carry_aux b 0;
  
  let h2 = ST.get() in
  
  cut (modifies !{getData b} h1 h2);
  cut (True /\ getData b <> getData a);

  (* TODO : understand why this does not go through *)  
  admitP (modifies !{} h0 h2);
  b
  

(* STATUS : proof only up to this point
 * The normalized_carry function is very likely provable for functional correctness
 * Constant timeness would come from bitwise operations and smart masking
 *)
  
(*
val one_pass_carry_aux :
  a:bigint -> len:nat -> 
  ST unit
     (requires (fun h -> True))
     (ensures (fun h0 u h1 -> True))
let rec one_pass_carry_aux a len =
  match len with
  | 0 -> ()
  | _ ->
     let h0 =
       (ST.get()) in
     let i = len - 1 in
     let t = getTemplate a in
     let ai = get a i in
     let size_ai = 
       (getSize h0 a i) in
     let size_aip =
       (getSize h0 a (i+1)) in
     let high = arithmetic_shift_right ai (t i) in
     (* Not constant time *)
     let low = signed_modulo ai (pow2 (t i)) in
     let aip1 = get a (i+1) in
     let aip1 = Limb.add (t i) high (t (i+1)) aip1 in
     let th = mk_tint a ((max size_aip (wordSize a - t i) + 1)) aip1 in
     let tl = mk_tint a (((min size_ai (t i)))) low in
     updateBigint a (i+1) th;
     updateBigint a i tl;
     one_pass_carry_aux a (len-1)
		 
(* One pass of carry starting from top to bottom after adding additional cell to the array *) 
val one_pass_carry:
  a:bigint -> 
  ST unit
     (requires (fun h -> 
		(inHeap h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{getData a} h0 h1)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
	       /\ (getLength h1 a = getLength h0 a + 1)
	       /\ (getSize h1 a 0 <= getTemplate a 0)
	       /\ (forall (i:pos). i < getLength h1 a - 1
		   ==> getSize h1 a i <= max (getSize h0 a (i-1) - getTemplate a (i-1)) (getTemplate a i) + 1)
     ))
let one_pass_carry a =
  let len = get_length a in
  let array = Array.create (len + 1) zero_tint in
  Array.blit (getData a) 0 array 0 len;
  let last = get a (len-1) in
  let t_last = getTemplate a (len-1) in
  let high = arithmetic_shift_right last t_last in
  let low = signed_modulo last (pow2 t_last) in
  let th = mk_tint a (wordSize a - t_last) high in
  let tl = mk_tint a t_last low in
  updateBigint a len th;
  updateBigint a (len-1) tl;
  one_pass_carry_aux a (len-1)
*)

(* Fully normal form for a big int : all cells have the same sign *)
type FullyNormalized (h:heap) (b:bigint) =
  (inHeap h b) 
  /\ (forall (i:nat). i < getLength h b ==> getSize h b i <= getTemplate b i)
  /\ ((exists (i:nat). (i < getLength h b /\ getValue h b i < 0))
      ==> (forall (j:nat). j < getLength h b ==> getValue h b j <= 0))
  /\ ((exists (i:nat). (i < getLength h b /\ getValue h b i > 0))
      ==> (forall (j:nat). j < getLength h b ==> getValue h b j >= 0))

(* Returns the sign of a bigint *)
(* Not constant time *)
val get_sign: a:bigint -> len:nat ->
	      ST int
		 (requires (fun h ->
			    (inHeap h a)
			    /\ (Normalized h a)
			    /\ (len <= getLength h a)
		 ))
		 (ensures (fun h0 s h1 ->
			   (inHeap h0 a)
			   /\ (Normalized h0 a)
			   /\ (len <= getLength h0 a)
			   /\ (modifies !{} h0 h1)
			   /\ (s = 0 \/ s = 1 \/ s = -1)
			   /\ (s = 0 <==> eval h1 a (getLength h1 a) = 0)
			   /\ (s = 1 <==> eval h1 a (getLength h1 a) > 0)
			   /\ (s = -1 <==> eval h1 a (getLength h1 a) < 0)
		 ))
let rec get_sign a len =
  // TODO : PROOF
  admit();
  match len with
  | 0 -> 0
  | _ -> 
     let i = len - 1 in
     let ai = get a i in
     let s = IntLib.compare ai zero in
     if s = 0 then get_sign a i else s

(* Returns a fully normalized big int (all cells of the same sign) *)
(* Not constant time *)
val normalized_carry_aux :
  a:bigint -> len:nat -> s:int ->
  ST unit
     (requires (fun h -> 
	        (inHeap h a)
		/\ (Normalized h a)
		/\ (s = 0 \/ s = 1 \/ s = -1)
		/\ (s = 0 <==> eval h a (getLength h a) = 0)
		/\ (s = 1 <==> eval h a (getLength h a) > 0)
		/\ (s = -1 <==> eval h a (getLength h a) < 0)
		/\ (len <= getLength h a)
		/\ (forall (i:nat).
		    ((i < getLength h a /\ i >= len /\ s = 1) ==> getValue h a i >= 0)
		    /\ ((i < getLength h a /\ i >= len /\ s = -1) ==> getValue h a i <= 0))
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h1 a)
	       /\ (Normalized h0 a)
	       /\ (modifies !{getData a} h0 h1)
	       /\ (getLength h1 a = getLength h0 a)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
	       /\ (s = 0 \/ s = 1 \/ s = -1)
	       /\ (s = 0 <==> eval h0 a (getLength h0 a) = 0)
	       /\ (s = 1 <==> eval h0 a (getLength h0 a) > 0)
	       /\ (s = -1 <==> eval h0 a (getLength h0 a) < 0)
	       /\ (len <= getLength h0 a)
	       /\ (FullyNormalized h1 a)
     ))
let rec normalized_carry_aux a len sign =
  // TODO : PROOF
  admit();  
  let minus_one = -1 in
  match len with
  | 0 -> ()
  | _ ->
     let i = len - 1 in
     let ai = get a i in
     match IntLib.compare ai zero with
     | 0 -> 
	(* The limb is zero, so we have to check that the cell bellow has the right sign *)
	(* Otherwise, we swap is and change this limb value *)
	if i = 0 then () (* least significant limb, nothing to do *)
	else (
	  let aim1 = get a (i-1) in
	  let sm1 = IntLib.compare aim1 zero in
	  if sign * sm1 >= 0 then () (* The adjacent lower cell has the right sign, all good *)
	  else (
	    (* Bad sign, change it *)
	    if sign = 1 then (
	      let ai = pow2 (getTemplate a i) - 1 in
	      let ai = Bigint.mk_tint a (getTemplate a i) ai in
	      let aim1 = aim1 + pow2 (getTemplate a (i-1)) in
	      let aim1 = Bigint.mk_tint a (getTemplate a (i-1)) aim1 in
	      Bigint.updateBigint a i ai;
	      Bigint.updateBigint a (i-1) aim1)
	    else (
	      let ai = - (pow2 (getTemplate a i)) + 1 in
	      let ai = Bigint.mk_tint a (getTemplate a i) ai in
	      let aim1 = aim1 - pow2 (getTemplate a (i-1)) in
	      let aim1 = Bigint.mk_tint a (getTemplate a (i-1)) aim1 in
	      Bigint.updateBigint a i ai;
	      Bigint.updateBigint a (i-1) aim1))
	);
	(* Iterate *)
	normalized_carry_aux a i sign
	
     | 1 -> 
	if sign = 1 then ()
	else (
	  let aip1 = get a len in
	  let aip1 = Bigint.mk_tint a (getTemplate a len) (aip1 + 1) in
	  let ai = Bigint.mk_tint a (getTemplate a i) (ai - pow2 (getTemplate a i)) in
	  Bigint.updateBigint a len aip1;
	  Bigint.updateBigint a i ai);
	normalized_carry_aux a i sign

     | minus_one -> 
	if sign = -1 then ()
	else (
	  let aip1 = get a len in
	  let aip1 = Bigint.mk_tint a (getTemplate a len) (aip1 - 1) in
	  let ai = Bigint.mk_tint a (getTemplate a i) (ai + pow2 (getTemplate a i)) in
	  Bigint.updateBigint a len aip1; 
	  Bigint.updateBigint a i ai);
	normalized_carry_aux a i sign


(* Returns a fully normalized big int (all cells of the same sign) *)
(* Not constant time *)
val normalized_carry:
  a:bigint -> 
  ST unit
     (requires (fun h -> 
       (inHeap h a)
       /\ (Normalized h a)
     ))
     (ensures (fun h0 u h1 ->
		 (inHeap h0 a)
		 /\ (inHeap h1 a)
		 /\ (Normalized h0 a)
		 /\ (modifies !{getData a} h0 h1)
		 /\ (FullyNormalized h1 a)
     ))
let normalized_carry a =
  let sign = get_sign a (get_length a) in
  normalized_carry_aux a (get_length a) sign
