module Shift


open Heap
open ST
open IntLib
open Bigint
open Eval

type norm_bigint = a:bigint{ forall (i:nat). Bigint63.t a i = Bigint63.t a 0 }

val shift:
  a:bigint -> offset:nat ->
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (modifies !{} h0 h1)
	       /\ (getLength h1 b = getLength h0 a + offset)
	       /\ (forall (i:nat).
		   (i < getLength h0 a ==> (getValue h1 b (i+offset) = getValue h0 a i
                                         /\ getSize h1 b (i+offset) = getSize h0 a i))
		   /\ (i < offset ==> (getValue h1 b i = 0 /\ getSize h1 b i = 0)))
	       /\ (eval h1 b (getLength h1 b) = pow2 (offset * (Bigint63.t a 0)) * eval h0 a (getLength h0 a))
     ))
let shift a offset =
  let res = Bigint.mk_zero_bigint (get_length a + offset) in
  Array.blit a 0 res offset (get_length a);
  Bigint63.data a := res

(* How to make it constant time ? *)
val shift_by_bits_aux:
  a:bigint -> bits:nat -> b:bigint -> len:nat ->
  ST unit
     (requires (fun h ->
		(inHeap h a)
		/\ (inHeap h b)
		/\ (SameFormat h h a b)
		/\ (len <= getLength h0 a)
		/\ (forall (i:nat). (i >= len /\ i < getLength h0 a)
		    ==> (getSize h0 b i = getSize h0 a i + bits 
                        /\ getValue h0 b i = pow2 bits * getValue h0 a i))
		/\ (forall (i:nat). i < len
		    ==> getSize a i <= wordSize a - bits)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (SameFormat h0 h0 a b)
	       /\ (modifies !{Bigint63.data b} h0 h1)
	       /\ (SameFormat h0 h1 b b)
	       /\ (forall (i:nat). i < getLength h0 a 
		   ==> (getSize h0 b i = getSize h0 a i + bits 
		       /\ getValue h0 b i = pow2 bits * getValue h0 a i))
     ))
let rec shift_by_bits_aux a bits b len =
  match len with
  | 0 -> ()
  | _ ->
     let i = len - 1 in
     let h0 = 
       erase (ST.get()) in
     let v = Bigint.mk_tint b (getSize h0 a i + bits) (shift_left (get a i)) in
     Bigint.updateBigint b i v;
     shift_by_bits_aux a bits b (len-1)

val shift_by_bits : 
  a:bigint -> bits:nat -> 
  ST bigint
     (requires (fun h -> 
		(inHeap h a)
		/\ (maxSize h a < wordSize a - bits)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h1 b)
	       /\ (modifies !{} h0 h1)
	       /\ (eval h1 b (getLength h1 b) = pow2 bits * eval h0 a (getLength h0 a))
	       /\ (forall (i:nat). i < getLength h1 b
		   ==> (getValue h1 b = pow2 bits * getValue h0 a /\ getSize h1 b = bits + getSize h0 a))
     ))
let shift_by_bits a bits =
  let b = Bigint63.data (Bigint.mk_zero_bigint (get_length a)) (Bigint63.t a) in
  shift_by_bits_aux a bits b (get_length a)
	
val shift_over_by_bits_aux :
  a:norm_bigint -> bits:nat -> b:norm_bigint -> len:nat -> 
  ST norm_bigint 
     (requires (fun h -> 
		(inHeap h a)
		/\ (inHeap h b)
		/\ (Normalized h a)
		/\ (Normalized h b)
		/\ (getLength h b = getLength h a + 1)
		/\ (forall (i:nat). i < getLength h a 
		    ==> bits < Bigint63.t a i)
		/\ (eval h b (i+1) = pow2 bits * eval h a i)
     ))
     (ensures (fun h0 u h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (modifies !{Bigint63.data b} h0 h1)
	       /\ (getLength h0 b = getLength h0 a + 1)
	       /\ (getLength h1 b = getLength h0 b)
	       /\ (forall (i:nat). i < getLength h0 a 
		   ==> bits < Bigint63.t a i)
	       /\ (eval h1 b (getLength h1 b) = pow2 bits * eval h0 a (getLength h0 a))
	       /\ (Normalized h1 b)
     ))
let shift_over_by_bits_aux a bits b len =
  match get_length a - len with
  | 0 -> ()
  | _ ->
     let i = len in
     let ai = get a i in
     let modulus = (Bigint63.t a i - pow2 bits)
     let carry = div ai modulus in (* Redundant recursives calls, put in variable *)
     let remainder = shift_left (signed_modulo a modulus) bits in
     let carry = Bigint.mk_tint a (Bigint63.t a i) carry in
     let remainder = Bigint.mk_tint a (Bigint63.t a i) remainder in
     Bigint.updateBigint b (i+1) carry;
     Bigint.updateBigint b i remainder;
     shift_over_by_bits_aux a bits b (i+1)
     
val shift_over_by_bits :
  a:norm_bigint -> bits:nat ->
  ST norm_bigint 
     (requires (fun h -> 
		(inHeap h a)
		/\ (Normalized h a)
		/\ (forall (i:nat). i < getLength h a 
		    ==> bits < Bigint63.t a i)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h0 a)
	       /\ (inHeap h1 b)
	       /\ (modifies !{} h0 h1)
	       /\ (forall (i:nat). i < getLength h0 a 
		   ==> bits < Bigint63.t a i)
	       /\ (eval h1 b (getLength h1 b) = pow2 bits * eval h0 a (getLength h0 a))
	       /\ (Normalized h1 b)
     ))
let shift_over_by_bits a bits =
  let b = Bigint63.data (Bigint.mk_zero_bigint (get_length a + 1)) (Bigint63.t a) in
  shift_over_by_bits_aux a bits b (get_length a)
		       
