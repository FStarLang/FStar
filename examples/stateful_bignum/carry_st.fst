(* STATUS : lax type checks but not verified, work in progress *)

module Carry

open Heap 
open ST
open Limb
open Bigint
open IntLib
open Seq
open Axiomatic
open Eval
open Array

val aux :
  t:template -> bw_p_max:nat -> n:nat -> bwn:nat -> 
  Tot nat
let rec aux t bw_p_max n bwn =
  if bwn >= bw_p_max then n
  else aux t bw_p_max (n+1) (bwn + t n)

(* Compute the required array length to store the carried result *)
val compute_size :
  a:bigint -> ST nat
		 (requires (fun h -> True))
		 (ensures (fun h0 n h1 -> True))
let compute_size a =
  let bw = bitweight (Bigint63.t a) (get_length a) in
  let max = wordSize a in
  let bw_p_max = bw + max in
  aux (Bigint63.t a) bw_p_max (get_length a) bw

val carry_aux :
  a:bigint -> i:nat -> 
  ST unit
     (requires (fun h -> True))
     (ensures (fun h0 u h1 -> True))
let rec carry_aux a i =
  match get_length a - i - 1 with
  | 0 -> ()
  | _ -> 
     let ai = get a i in
     let t = Bigint63.t a in
     let moduli = pow2 (t i) in
     let v = div ai moduli in
     let carry = signed_modulo ai moduli in
     let size_v = erase (wordSize a - t i) in
     let size_carry = erase (t i) in
     let tl = Bigint.mk_tint a size_v v in
     let th = Bigint.mk_tint a (wordSize a - 1) (carry + get a (i+1)) in
     updateBigint a i tl;
     updateBigint a (i+1) th;
     carry_aux a (i+1)		  

(* Perform a carry operations : the array is normalized but cells can have different sizes *)
val carry : 
  a:bigint -> 
  ST unit
     (requires (fun h -> 
		(inHeap h a)
		/\ (maxSize h a < wordSize a - 1)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h1 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (Normalized h1 a)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
     ))
let carry a = 
  let size = compute_size a in
  let new_array = Array.create size zero_tint in
  Array.blit (Bigint63.data a) 0 new_array 0 (get_length a);
  Bigint63.data a := !new_array;
  carry_aux a 0

(* Carry modulo value *)	    
assume val carry_mod:
  a:bigint -> m:bigint -> 
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h m)
		/\ (eval h m (getLength h m) > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (inHeap h0 m)
	       /\ (eval h0 m (getLength h0 m) > 0)
	       /\ (Bigint63.t b = Bigint63.t a)
	       /\ (getLength h1 b > 0)
	       /\ (bitweight (Bigint63.t b) (getLength h1 b) > eval h0 m (getLength h0 m))
	       /\ (bitweight (Bigint63.t b) (getLength h1 b - 1) <= eval h0 m (getLength h0 m))
	       /\ (forall (i:nat). i < getLength h1 b 
		   ==> getValue h1 b i >= 0)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a) % eval h0 m (getLength h0 m))
     ))

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
       erase (ST.get()) in
     let i = len - 1 in
     let t = Bigint63.t a in
     let ai = get a i in
     let size_ai = 
       erase (getSize h0 a i) in
     let size_aip =
       erase (getSize h0 a (i+1)) in
     let high = arithmetic_shift_right ai (t i) in
     (* Not constant time *)
     let low = signed_modulo ai (pow2 (t i)) in
     let aip1 = get a (i+1) in
     let aip1 = Limb.add (t i) high (t (i+1)) aip1 in
     let th = mk_tint a (max size_aip (wordSize a - t i) + 1) aip1 in
     let tl = mk_tint a (min size_ai (t i)) low in
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
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (eval h1 a (getLength h1 a) = eval h0 a (getLength h0 a))
	       /\ (getLength h1 a = getLength h0 a + 1)
	       /\ (getSize h1 a 0 <= Bigint63.t a 0)
	       /\ (forall (i:pos). i < getLength h1 a - 1
		   ==> getSize h1 a i <= max (getSize h0 a (i-1) - Bigint63.t a (i-1)) (Bigint63.t a i) + 1)
     ))
let one_pass_carry a =
  let len = get_length a in
  let array = Array.create (len + 1) zero_tint in
  Array.blit (Bigint63.data a) 0 array 0 len;
  let last = get a (len-1) in
  let t_last = Bigint63.t a (len-1) in
  let high = arithmetic_shift_right last t_last in
  let low = signed_modulo last (pow2 t_last) in
  let th = mk_tint a (wordSize a - t_last) high in
  let tl = mk_tint a t_last low in
  updateBigint a len th;
  updateBigint a (len-1) tl;
  one_pass_carry_aux a (len-1)

(* Fully normal form for a big int : all cells have the same sign *)
type FullyNormalized (h:heap) (b:bigint) =
  (inHeap h b) 
  /\ (forall (i:nat). i < getLength h b ==> getSize h b i <= Bigint63.t b i)
  /\ ((exists (i:nat). (i < getLength h b /\ getValue h b i < 0))
      ==> (forall (j:nat). j < getLength h b ==> getValue h b j <= 0))
  /\ ((exists (i:nat). (i < getLength h b /\ getValue h b i > 0))
      ==> (forall (j:nat). j < getLength h b ==> getValue h b j >= 0))

(* Returns the sign of a bigint *)
(* Not constant time *)
val get_sign: a:bigint -> len:nat ->
	      ST int
		 (requires (fun h ->
			    (Normalized h a)
			    /\ (len <= getLength h a)
		 ))
		 (ensures (fun h0 s h1 ->
			   (Normalized h0 a)
			   /\ (len <= getLength h0 a)
			   /\ (modifies !{} h0 h1)
			   /\ (s = 0 \/ s = 1 \/ s = -1)
			   /\ (s = 0 <==> eval h1 a (getLength h1 a) = 0)
			   /\ (s = 1 <==> eval h1 a (getLength h1 a) > 0)
			   /\ (s = -1 <==> eval h1 a (getLength h1 a) < 0)
		 ))
let rec get_sign a len =
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
  a:bigint -> len:nat -> s:nat ->
  ST unit
     (requires (fun h -> 
		(Normalized h a)
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
	       (Normalized h0 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
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
	      let ai = pow2 (Bigint63.t a i) - 1 in
	      let ai = Bigint.mk_tint a (Bigint63.t a i) ai in
	      let aim1 = aim1 + pow2 (Bigint63.t a (i-1)) in
	      let aim1 = Bigint.mk_tint a (Bigint63.t a (i-1)) aim1 in
	      Bigint.updateBigint a i ai;
	      Bigint.updateBigint a (i-1) aim1)
	    else (
	      let ai = - (pow2 (Bigint63.t a i)) + 1 in
	      let ai = Bigint.mk_tint a (Bigint63.t a i) ai in
	      let aim1 = aim1 - pow2 (Bigint63.t a (i-1)) in
	      let aim1 = Bigint.mk_tint a (Bigint63.t a (i-1)) aim1 in
	      Bigint.updateBigint a i ai;
	      Bigint.updateBigint a (i-1) aim1))
	);
	(* Iterate *)
	normalized_carry_aux a i sign
	
     | 1 -> 
	if sign = 1 then ()
	else (
	  let aip1 = get a len in
	  let aip1 = Bigint.mk_tint a (Bigint63.t a len) (aip1 + 1) in
	  let ai = Bigint.mk_tint a (Bigint63.t a i) (ai - pow2 (Bigint63.t a i)) in
	  Bigint.updateBigint a len aip1;
	  Bigint.updateBigint a i ai);
	normalized_carry_aux a i sign

     | minus_one -> 
	if sign = 1 then ()
	else (
	  let aip1 = get a len in
	  let aip1 = Bigint.mk_tint a (Bigint63.t a len) (aip1 - 1) in
	  let ai = Bigint.mk_tint a (Bigint63.t a i) (ai + pow2 (Bigint63.t a i)) in
	  Bigint.updateBigint a len aip1; 
	  Bigint.updateBigint a i ai);
	normalized_carry_aux a i sign


(* Returns a fully normalized big int (all cells of the same sign) *)
(* Not constant time *)
val normalized_carry:
  a:bigint -> 
  ST unit
     (requires (fun h -> (Normalized h a)
     ))
     (ensures (fun h0 u h1 ->
	       (Normalized h0 a)
	       /\ (modifies !{Bigint63.data a} h0 h1)
	       /\ (FullyNormalized h1 a)
     ))
let normalized_carry a =
  let sign = get_sign a (get_length a) in
  normalized_carry_aux a (get_length a) sign
