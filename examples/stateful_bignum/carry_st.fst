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

let compute_size a =
  let bw = bitweight (Bigint63.t a) (get_length a) in
  let max = wordSize a in
  let bw_p_max = bw + max in
  let rec aux t bw_p_max n bwn =
    if bwn >= bw_p_max then n
    else aux t bw_p_max (n+1) (bwn + t n) in
  aux (Bigint63.t a) bw_p_max (get_length a) bwn

let carry_aux a i =
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
  let new_array = Bigint.mk_zero_bigint size in
  Array.blit (Bigint63.data a) 0 new_array 0 (get_length a);
  Bigint63.data a := new_array;
  carry_aux a 0

	       
val carry_mod:
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

let one_pass_carry_aux a len =
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
     let high = shift_right ai (t i) in
     (* Not constant time *)
     let low = signed_modulo ai (pow2 (t i)) in
     let th = mk_tint a (max size_aip (wordSize a - t i) + 1) (Limb.add high (get a (i+1))) in
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
  let array = Bigint.mk_zero_bigint (len + 1) in
  Array.blit (Bigint63.data a) 0 array 0 len;
  let last = get a (len-1) in
  let t_last = Bigint63.t a (len-1)  
  let high = shift_right last t_last in
  let low = signed_modulo last (pow2 t_last) in
  let th = mk_tint a (wordSize a - t_last) high in
  let tl = mk_tint a t_last low in
  updateBigint a len th;
  updateBigint a (len-1) tl;
  one_pass_carry_aux a (len-1)
