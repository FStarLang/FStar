module Bignum.FsumWide

open FStar.Heap
open FStar.Ghost
open IntLib
open Sint
open SBuffer
open FStar.UInt64
open Bignum.Parameters
open Bignum.Bigint

opaque type WillNotOverflow (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) (b:bigint_wide) =
  Live h a /\ length a >= a_idx+len /\ Live h b /\ length b >= b_idx+len
  /\ (forall (i:nat). {:pattern (v (get h a (i+a_idx)))} (i >= ctr /\ i < len) ==>
	(v (get h a (i+a_idx)) + v (get h b (i+b_idx)) < pow2 platform_wide))

opaque type IsNotModified (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) = 
  Live h0 a /\ Live h1 a /\ a_idx+len <= length a 
  /\  (forall (i:nat). {:pattern (v (get h1 a i))} ((i<ctr+a_idx \/ i >= len+a_idx) /\ i < length a) ==>
	       v (get h1 a i) == v (get h0 a i))

opaque type IsSum (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) (b:bigint_wide) =
  Live h0 a /\ Live h1 a /\ a_idx+len <= length a /\ Live h0 b /\ b_idx+len <= length b
  /\ (forall (i:nat). {:pattern (v (get h1 a (i+a_idx)))} (i>= ctr /\ i<len) ==> 
	v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)))

#reset-options

val fsum_index: a:bigint_wide -> a_idx:nat -> b:bigint_wide{Disjoint a b} -> b_idx:nat -> len:nat -> 
  ctr:nat{ctr<=len} -> ST unit
    (requires (fun h -> Live h a /\ Live h b /\ a_idx+len <= length a /\ b_idx+len <= length b
	/\ WillNotOverflow h a_idx b_idx len ctr a b))
    (ensures (fun h0 _ h1 -> Live h0 a /\ Live h0 b /\ Live h1 a /\ Live h1 b
      /\ a_idx+len <= length a /\ b_idx+len <= length b /\ Modifies (only a) h0 h1
      /\ IsNotModified h0 h1 a_idx len ctr a
      /\ IsSum h0 h1 a_idx b_idx len ctr a b))
let rec fsum_index a a_idx b b_idx len ctr =
//  admit();
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> () 
  | _ -> 
      let i = ctr in
      let ai = index a (i+a_idx) in 
      let bi = index b (i+b_idx) in 
      cut(b2t(v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)) < pow2 platform_wide));
      let z = ai ^^+ bi in 
      upd a (a_idx+i) z; 
      let h1 = ST.get() in
      eq_lemma h0 h1 b (only a); 
      fsum_index a a_idx b b_idx len (ctr+1)
      
#reset-options

opaque val gaddition_lemma: h0:heap -> h1:heap -> a:bigint_wide{Live h0 a /\ Live h1 a} -> b:bigint_wide{Live h0 b} ->
  len:nat{len <= length a /\ len <= length b /\ 
	 (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> 
	    v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->
  GLemma unit (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len)) []
let rec gaddition_lemma h0 h1 a b len =
//  admit();
  match len with
  | 0 -> ()
  | _ -> gaddition_lemma h0 h1 a b (len-1); 
    distributivity_add_right (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1)))  (v (get h0 b (len-1)))

val addition_lemma: h0:heap -> h1:heap -> a:bigint_wide{Live h0 a /\ Live h1 a} -> b:bigint_wide{Live h0 b} ->
  len:nat{len <= length a /\ len <= length b /\ 
	 (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> 
	    v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->
  Lemma (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let addition_lemma h0 h1 a b len =
  coerce (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
	 (fun _ -> gaddition_lemma h0 h1 a b len)

let vmax = templ 0

// TODO
val fsum': a:bigint_wide -> b:bigint_wide{Disjoint a b} -> ST unit
    (requires (fun h -> Norm h a /\ Norm h b))
    (ensures (fun h0 u h1 -> Norm h0 a /\ Norm h0 b /\ Live h1 a /\ Modifies (only a) h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      /\ IsNotModified h0 h1 0 norm_length 0 a
      /\ IsSum h0 h1 0 0 norm_length 0 a b))
let fsum' a b =
  admit();
  let h0 = ST.get() in 
  fsum_index a 0 b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0)));
  cut (forall (i:nat). (i >= norm_length /\ i < length a) ==> v (get h1 a (i+0)) = v (get h0 a (i+0)));
  addition_lemma h0 h1 a b norm_length
