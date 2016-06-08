module Bignum.Fscalar

open FStar.Heap
open FStar.Ghost
open IntLib
open SInt
open SBuffer
open SInt.UInt64
open Bignum.Parameters
open Bignum.Bigint

#set-options "--lax"

val scalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b} -> s:limb -> len:nat{len <= length a /\ len <= length b} ->
  Lemma
    (requires (forall (i:nat). {:pattern (v (get h1 b i))} i < len ==> v (get h0 a i) * v s = v (get h1 b i)))
    (ensures (eval h0 a len * v s = eval h1 b len)) 
let rec scalar_multiplication_lemma h0 h1 a b s len =
  match len with
  | 0 -> () 
  | _ -> 
    scalar_multiplication_lemma h0 h1 a b s (len-1); 
    cut (True /\ eval h1 b len = pow2 (bitweight templ (len-1)) * v (get h1 b (len-1)) + eval h1 b (len-1)); 
    cut (True /\ eval h1 b len = pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)) * v s + eval h0 a (len-1) * v s); 
    cut (True /\ eval h0 a len = pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)) + eval h0 a (len-1)); 
    distributivity_add_left (pow2 (bitweight templ (len-1)) * v (get h0 a (len-1))) (eval h0 a (len-1)) (v s);
    paren_mul_left (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1))) (v s)

abstract let scalarProduct (h0:heap) (h1:heap) (ctr:nat) (a:bigint) (s:limb) (res:bigint_wide) =
  live h0 a /\ live h1 res /\ ctr <= norm_length
  /\ (forall (i:nat). {:pattern (v (get h1 res i))} i < ctr ==> v (get h1 res i) = v (get h0 a i) * v s)

val scalar_multiplication_aux: res:bigint_wide -> a:bigint{disjoint res a} -> s:limb -> ctr:nat -> ST unit
  (requires (fun h -> live h res /\ live h a /\ ctr <= norm_length
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < ctr ==> v (get h a i) * v s < pow2 platform_wide) ))
  (ensures (fun h0 _ h1 -> scalarProduct h0 h1 ctr a s res 
    /\ modifies_buf (only res) h0 h1 /\ equal h0 a h1 a /\ equalSub h0 res ctr h1 res ctr (length res - ctr)))
let rec scalar_multiplication_aux res a s ctr =
  admit();
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> let i = ctr - 1 in 
         let ai = index a i in
	 gcut (fun _ -> v (get h0 a i) * v s < pow2 63);
	 let resi = ai ^*^ s in
	 upd res i resi; 
	 let h1 = ST.get() in
	 eq_lemma h0 h1 a (only res);
	 scalar_multiplication_aux res a s i; 
	 let h2 = ST.get() in
	 gcut (fun _ -> modifies_buf (only res) h0 h1); gcut (fun _ -> equal h0 a h2 a); 	 
	 cut (forall (i:nat). {:pattern (v (get h2 res (ctr+i-1)))} i < length res - ctr + 1 ==> v (get h2 res (ctr-1 + i)) = v (get h1 res (ctr-1+i)));  
	 cut (forall (i:nat). {:pattern (v (get h2 res (ctr+(i-1))))} i < length res - ctr + 1 ==> v (get h2 res (ctr+i-1)) = v (get h1 res (ctr+i-1)));  
	 cut (forall (i:nat). {:pattern (get h2 res (ctr+i))} i < length res - ctr ==> v (get h2 res (ctr-1+(i+1))) = v (get h1 res (ctr-1+i+1)));  
	 gcut (fun _ -> equalSub h1 res ctr h2 res ctr (length res - ctr)); 
	 cut (forall (i:nat). {:pattern (v (get h2 res i))} i < ctr - 1 ==> v (get h2 res i) = v (get h1 a i) * v s); 
	 cut (forall (i:nat). {:pattern (v (get h1 res i))} (i < length res /\ i <> ctr-1) ==> v (get h1 res i) = v (get h0 res i)); 
	 gcut (fun _ -> v (get h2 res (ctr-1+0)) = v (get h0 a (ctr-1)) * v s); 
	 cut (forall (i:nat). i < ctr ==> v (get h2 res i) = v (get h0 a i) * v s); 
	 gcut (fun _ -> scalarProduct h0 h2 ctr a s res); 
	 gcut (fun _ -> equal h0 a h2 a); 
	 gcut (fun _ -> equalSub h0 res ctr h1 res ctr (length res - ctr))

val scalar_multiplication: res:bigint_wide -> a:bigint{disjoint res a} -> s:limb -> ST unit
  (requires (fun h -> live h res /\ live h a
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < norm_length ==> v (get h a i) * v s < pow2 platform_wide) ))
  (ensures (fun h0 _ h1 -> scalarProduct h0 h1 norm_length a s res 
    /\ modifies_buf (only res) h0 h1 /\ equal h0 a h1 a 
    /\ equalSub h0 res norm_length h1 res norm_length (length res - norm_length)
    /\ eval h1 res norm_length = eval h0 a norm_length * v s))
let scalar_multiplication res a s =
  let h0 = ST.get() in
  scalar_multiplication_aux res a s norm_length;
  let h1 = ST.get() in
  scalar_multiplication_lemma h0 h1 a res s norm_length
