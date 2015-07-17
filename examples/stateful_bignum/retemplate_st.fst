module Retemplate 

open IntLib
open Heap
open ST
open Eval
open Bigint

(* TODO : not verified *)
val fill_array : 
  b:bigint -> tb:template -> v:int -> tsize:nat -> bw:nat -> len:nat -> 
  ST unit
     (requires (fun h -> 
		(inHeap h b)
		/\ (Normalized h b)
		/\ (tb = Bigint63.t b)
     ))
     (ensures (fun h0 u h1 -> 
	       (inHeap h0 b)
	       /\ (inHeap h1 b)
	       /\ (Normalized h0 b)
	       /\ (tb = Bigint63.t b)
	       /\ (getLength h1 b = getLength h0 b)
	       /\ (eval h1 b (getLength h1 b) = eval h0 b (getLength h0 b) + pow2 bw * v)
     ))
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

(* Verified *)
val compute_size_aux : 
  t:template -> 
  n:nat -> 
  tn:nat{tn = bitweight t n} -> 
  wa:nat{ tn < wa } ->
  Tot (size:pos{ bitweight t size >= wa /\ bitweight t (size-1) < wa })
      (decreases (wa - tn))
let rec compute_size_aux t n tn wa =
  (* Compute bitweight t (n+1) *)
  let bwnp1 = tn + t n in
  (* Test if against the total bitweight of a, if smaller iterate *)
  if bwnp1 >= wa then n+1
  else compute_size_aux t (n+1) bwnp1 wa

(* Compute the required size for the new template, verified *)
val compute_size : 
  a:bigint -> t:template ->
  ST pos
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 n h1 ->
	       (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{} h0 h1)
	       /\ (bitweight t n >= bitweight (Bigint63.t a) (getLength h0 a))
	       /\ (n > 0)
	       /\ (bitweight t (n-1) < bitweight (Bigint63.t a) (getLength h0 a))
     ))
let compute_size a t =
  let n = 0 in
  let tn = 0 in
  let weight_a = bitweight (Bigint63.t a) (get_length a) in
  compute_size_aux t n tn weight_a

val retemplate_aux : 
  a:bigint -> ta:template -> b:bigint -> tb:template -> len:nat ->
  ST unit
     (requires (fun h -> 
		(inHeap h a)
		/\ (Normalized h a)
		/\ (inHeap h b)
		/\ (Normalized h b)
     ))
     (ensures (fun h0 u h1 -> 
	       (inHeap h0 a)
	       /\ (inHeap h0 b)
	       /\ (inHeap h1 b)
	       /\ (Normalized h0 a)
	       /\ (Normalized h0 b)
	       /\ (Normalized h1 b)
	       /\ (modifies !{Bigint63.data b} h0 h1)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
let rec retemplate_aux a ta b tb len =
  match get_length a - len with
  | 0 -> ()
  | _ ->
     let v = get a len in
     let tsize = ta len in
     let bw = bitweight ta len in
     fill_array b tb v tsize bw 0;
     retemplate_aux a ta b tb (len+1)

val retemplate:
  a:bigint -> t:template ->
  ST bigint
     (requires (fun h ->
		(inHeap h a)
		/\ (Normalized h a)
		/\ (getLength h a > 0)
     ))
     (ensures (fun h0 b h1 ->
	       (inHeap h1 b)
	       /\ (inHeap h0 a)
	       /\ (Normalized h0 a)
	       /\ (getLength h0 a > 0)
	       /\ (modifies !{} h0 h1)
	       /\ (Bigint63.t b = t)
	       /\ (getLength h1 b > 0)
	       /\ (eval h1 b (getLength h1 b) = eval h0 a (getLength h0 a))
     ))
let retemplate a t =
  (* Compute the size of the new array *)
  let new_size = compute_size a t in
  let b = Bigint.mk_zero_bigint new_size t in
  retemplate_aux a (Bigint63.t a) b t 0;
  b

