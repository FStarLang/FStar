module Bignum.FsumWide

open FStar.Heap
open FStar.Ghost
open IntLib
open SInt
open SBuffer
open SInt.UInt64
open Bignum.Parameters
open Bignum.Bigint

#set-options "--lax"

abstract let willNotOverflow (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) (b:bigint_wide) =
  live h a /\ length a >= a_idx+len /\ live h b /\ length b >= b_idx+len
  /\ (forall (i:nat). {:pattern (v (get h a (i+a_idx)))} (i >= ctr /\ i < len) ==>
	(v (get h a (i+a_idx)) + v (get h b (i+b_idx)) < pow2 platform_wide))

abstract let isNotModified (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) = 
  live h0 a /\ live h1 a /\ a_idx+len <= length a 
  /\  (forall (i:nat). {:pattern (v (get h1 a i))} ((i<ctr+a_idx \/ i >= len+a_idx) /\ i < length a) ==>
	       v (get h1 a i) == v (get h0 a i))

abstract let isSum (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint_wide) (b:bigint_wide) =
  live h0 a /\ live h1 a /\ a_idx+len <= length a /\ live h0 b /\ b_idx+len <= length b
  /\ (forall (i:nat). {:pattern (v (get h1 a (i+a_idx)))} (i>= ctr /\ i<len) ==> 
	v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)))

val fsum_index: a:bigint_wide -> a_idx:nat -> b:bigint_wide{disjoint a b} -> b_idx:nat -> len:nat -> 
  ctr:nat{ctr<=len} -> ST unit
    (requires (fun h -> live h a /\ live h b /\ a_idx+len <= length a /\ b_idx+len <= length b
	/\ willNotOverflow h a_idx b_idx len ctr a b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ live h1 b
      /\ a_idx+len <= length a /\ b_idx+len <= length b /\ modifies_buf (only a) h0 h1
      /\ isNotModified h0 h1 a_idx len ctr a
      /\ isSum h0 h1 a_idx b_idx len ctr a b))
let rec fsum_index a a_idx b b_idx len ctr =
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> () 
  | _ -> 
      let i = ctr in
      let ai = index a (i+a_idx) in 
      let bi = index b (i+b_idx) in 
      cut(v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)) < pow2 platform_wide);
      let z = ai ^^+ bi in 
      upd a (a_idx+i) z; 
      let h1 = ST.get() in
      eq_lemma h0 h1 b (only a); 
      fsum_index a a_idx b b_idx len (ctr+1)

val addition_lemma: h0:heap -> h1:heap -> a:bigint_wide{live h0 a /\ live h1 a} -> b:bigint_wide{live h0 b} ->
  len:nat{len <= length a /\ len <= length b /\ 
	 (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> 
	    v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->
  Lemma (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let rec addition_lemma h0 h1 a b len =
  match len with
  | 0 -> ()
  | _ -> addition_lemma h0 h1 a b (len-1); 
    distributivity_add_right (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1)))  (v (get h0 b (len-1)))

let vmax = templ 0

// TODO
val fsum': a:bigint_wide -> b:bigint_wide{disjoint a b} -> ST unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 a /\ modifies_buf (only a) h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      /\ isNotModified h0 h1 0 norm_length 0 a
      /\ isSum h0 h1 0 0 norm_length 0 a b))
let fsum' a b =
  let h0 = ST.get() in 
  fsum_index a 0 b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0)));
  cut (forall (i:nat). (i >= norm_length /\ i < length a) ==> v (get h1 a (i+0)) = v (get h0 a (i+0)));
  addition_lemma h0 h1 a b norm_length
