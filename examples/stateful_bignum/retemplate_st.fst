module Retemplate 

open Heap
open ST
open Eval
open Bigint

(* TODO : not verified *)
val fill_array : b:bigint -> tb:template -> v:int -> tsize:nat -> bw:nat -> len:nat -> 
		 ST unit
		    (requires (fun h -> True))
		    (ensures (fun h0 u h1 -> True))
let rec fill_array b tb v tsize bw len =
  match (get_length b - len) with
  | 0 -> ()
  | _ ->
     let bw2 = bitweight tb len in
     let tsize2 = tb len in
     if bw + tsize > bw2 && bw2 + tsize2 > bw then
       let v2 = 
	 if bw < bw2 then div v (pow2 (bw2 - bw))
	 else pow2 (bw - bw2) * v in
       let v2 = signed_modulo v2 tsize2 in
       let v2 = v2 + get b len in
       let t2 = mk_tint b (erase (tsize2)) v2 in
       updateBigint b len t2
     else ();
     fill_array b tb v tsize bw (len+1)

(* TODO : not verified *)
val compute_size_aux : a:bigint -> t:template -> n:nat -> tn:nat -> wa:nat ->
		       ST nat
			  (requires (fun h -> True))
			  (ensures (fun h0 n h1 -> True))
let compute_size_aux a t n tn wa =
  if tn >= wa then n+1
  else compute_size_aux a t (n+1) (tn + t (n+1)) wa

(* TODO : not verified *)
val compute_size : a:bigint -> t:template ->
		   ST nat
		      (requires (fun h -> True))
		      (ensures (fun h0 n h1 -> True))
val compute_size : 
  a:bigint -> t:template ->
  ST nat
     (requires (fun h ->
		(inHeap h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 n h1 ->
	       (inHeap h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{} h0 h1)
	       /\ (t n >= bitweight (Bigint63.t a) (getLength h0 a))
	       /\ (t (n-1) < bitweight (Bigint63.t a) (getLength h0 a))
     ))
let compute_size a t =
  let n = 0 in
  let tn = t 0 in
  let weight_a = bitweight (Bigint63.t a) (get_length a) in
  compute_size_aux a t tn tnp wa

(* TODO : not verified *)
val retemplate_aux : a:bigint -> ta:template -> b:bigint -> tb:template -> len:nat ->
		     ST unit
			(requires (fun h -> True))
			(ensures (fun h0 u h1 -> True))
let retemplate_aux a ta b tb len =
  match get_length a - len with
  | 0 -> ()
  | _ ->
     let v = get a len in
     let tsize = ta len in
     let bw = bitweight ta len in
     fill_array b tb v tsize bw 0;
     retemplate_aux a (len+1)

(* TODO : not verified *)
val retemplate:
  a:bigint -> t:template ->
  ST bigint
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (modifies !{} h0 h1)
	       /\ not(contains h0 (Bigint63.data b))
	       /\ (Bigint63.t b = t)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
let retemplate a t =
  let new_size = comupte_size a t in
  let b = Bigint63 (Bigint.mk_zero_bigint new_size) t in
  retemplate_aux a (Bigint63.t a) b t 0

