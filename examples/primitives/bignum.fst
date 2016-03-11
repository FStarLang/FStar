(*--build-config
  options:--admit_fsi FStar.Set --verify_module Bignum1305 --z3timeout 10;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst /home/jkz/dev/FStar/contrib/Platform/fst/Bytes.fst axioms.fst intlib.fst lemmas.fst sint.fst FStar.UInt8.fst FStar.UInt63.fst sbuffer.fst parameters1305.fst bigint.fst;
  --*)

module Bignum

open FStar.Heap
open FStar.Ghost
open IntLib
open Sint
open FStar.UInt63
open SBuffer
open Bigint
open Parameters

(* Prime value *)
opaque val prime: p:erased pos{reveal p = pow2 130 - 5}
let prime = admit()

type Live (h:heap) (b:bigint) = Live h #63 b /\ length b >= norm_length

val distributivity_add_right: a:int -> b:int -> c:int -> Lemma (a*(b+c) = a * b + a * c)
let distributivity_add_right a b c = ()
val distributivity_add_left: a:int -> b:int -> c:int -> Lemma ((a+b)*c = a * c + b * c)
let distributivity_add_left a b c = ()
val paren_mul_left: a:int -> b:int -> c:int -> Lemma (a * b * c = ( a * b ) * c)
let paren_mul_left a b c = ()
val paren_mul_right: a:int -> b:int -> c:int -> Lemma (a * b * c = a * (b * c))
let paren_mul_right a b c = ()
val paren_add_left: a:int -> b:int -> c:int -> Lemma (a + b + c = ( a + b ) + c)
let paren_add_left a b c = ()
val paren_add_right: a:int -> b:int -> c:int -> Lemma (a + b + c = a + (b + c))
let paren_add_right a b c = ()

#reset-options

(*** Finalization ***)

(** TODO: proof **)
val finalize: b:bigint -> ST unit
  (requires (fun h -> Norm h b))
  (ensures (fun h0 _ h1 -> Norm h0 b /\ Norm h1 b
    /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime))
let finalize b =
  admit();
  let mask_26 = (FStar.UInt63.one ^<< 26) ^- FStar.UInt63.one in
  let mask2_26m5 = mask_26 ^- (FStar.UInt63.one ^<< 2) in
  let b0 = index b 0 in
  let b1 = index b 1 in
  let b2 = index b 2 in
  let b3 = index b 3 in
  let b4 = index b 4 in
  let mask = FStar.UInt63.eq b4 mask_26 in
  let mask = FStar.UInt63.eq b3 mask_26 ^& mask in 
  let mask = FStar.UInt63.eq b2 mask_26 ^& mask in 
  let mask = FStar.UInt63.eq b1 mask_26 ^& mask in 
  let mask = FStar.UInt63.gte b0 mask2_26m5 ^& mask in 
  upd b 0 (b0 ^- (mask ^& mask2_26m5));
  upd b 1 (b1 ^& mask);
  upd b 2 (b2 ^& mask);
  upd b 3 (b3 ^& mask);
  upd b 4 (b4 ^& mask);
  ()

(*** Addition ***)

opaque type WillNotOverflow (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint) =
  Live h a /\ length a >= a_idx+len /\ Live h b /\ length b >= b_idx+len
  /\ (forall (i:nat). {:pattern (v (get h a (i+a_idx)))} (i >= ctr /\ i < len) ==>
	(v (get h a (i+a_idx)) + v (get h b (i+b_idx)) < pow2 63))

opaque type IsNotModified (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) (a:bigint) = 
  Live h0 a /\ Live h1 a /\ a_idx+len <= length a 
  /\  (forall (i:nat). {:pattern (v (get h1 a i))} ((i<ctr+a_idx \/ i >= len+a_idx) /\ i < length a) ==>
	       v (get h1 a i) == v (get h0 a i))

opaque type IsSum (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint) =
  Live h0 a /\ Live h1 a /\ a_idx+len <= length a /\ Live h0 b /\ b_idx+len <= length b
  /\ (forall (i:nat). {:pattern (v (get h1 a (i+a_idx)))} (i>= ctr /\ i<len) ==> 
	v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)))

#reset-options

val fsum_index: a:bigint -> a_idx:nat -> b:bigint{Disjoint a b} -> b_idx:nat -> len:nat -> 
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
      cut(b2t(v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)) < pow2 63));
      let z = ai ^+ bi in 
      upd a (a_idx+i) z; 
      let h1 = ST.get() in
      eq_lemma h0 h1 b (only a); 
      fsum_index a a_idx b b_idx len (ctr+1);
      ()
      
#reset-options

opaque val gaddition_lemma: h0:heap -> h1:heap -> a:bigint{Live h0 a /\ Live h1 a} -> b:bigint{Live h0 b} ->
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

val addition_lemma: h0:heap -> h1:heap -> a:bigint{Live h0 a /\ Live h1 a} -> b:bigint{Live h0 b} ->
  len:nat{len <= length a /\ len <= length b /\ 
	 (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> 
	    v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->
  Lemma (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let addition_lemma h0 h1 a b len =
  coerce (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
	 (fun _ -> gaddition_lemma h0 h1 a b len)

val fsum': a:bigint -> b:bigint{Disjoint a b} -> ST unit
    (requires (fun h -> Norm h a /\ Norm h b))
    (ensures (fun h0 u h1 -> Norm h0 a /\ Norm h0 b /\ Live h1 a /\ Modifies (only a) h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      /\ IsNotModified h0 h1 0 norm_length 0 a
      /\ IsSum h0 h1 0 0 norm_length 0 a b))
let fsum' a b =
//  admit();
  cut (True /\ pow2 26 + pow2 26 <= pow2 27); 
  IntLibLemmas.pow2_increases 63 27;
  let h0 = ST.get() in
  fsum_index a 0 b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0)));
  cut (forall (i:nat). (i >= norm_length /\ i < length a) ==> v (get h1 a (i+0)) = v (get h0 a (i+0)));
  addition_lemma h0 h1 a b norm_length;
  ()

#reset-options

(*** Scalar multiplication ***)

opaque val gscalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{Live h0 a} -> 
  b:bigint{Live h1 b} -> s:uint63 -> len:nat{len <= length a /\ len <= length b} ->
  GLemma unit
    (requires (forall (i:nat). {:pattern (v (get h1 b i))} i < len ==> v (get h0 a i) * v s = v (get h1 b i)))
    (ensures (eval h0 a len * v s = eval h1 b len)) []
let rec gscalar_multiplication_lemma h0 h1 a b s len =
//  admit();
  match len with
  | 0 -> () 
  | _ -> 
    gscalar_multiplication_lemma h0 h1 a b s (len-1); 
    cut (True /\ eval h1 b len = pow2 (bitweight templ (len-1)) * v (get h1 b (len-1)) + eval h1 b (len-1)); 
    cut (True /\ eval h1 b len = pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)) * v s + eval h0 a (len-1) * v s); 
    cut (True /\ eval h0 a len = pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)) + eval h0 a (len-1)); 
    distributivity_add_left (pow2 (bitweight templ (len-1)) * v (get h0 a (len-1))) (eval h0 a (len-1)) (v s); 
    paren_mul_left (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1))) (v s)

val scalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{Live h0 a} -> 
  b:bigint{Live h1 b} -> s:uint63 -> len:nat{len <= length a /\ len <= length b} ->
  Lemma
    (requires (forall (i:nat). {:pattern (v (get h1 b i))} i < len ==> v (get h0 a i) * v s = v (get h1 b i)))
    (ensures (eval h0 a len * v s = eval h1 b len))
let scalar_multiplication_lemma h0 h1 a b s len = 
  coerce 
    (requires (forall (i:nat). {:pattern (v (get h1 b i))} i < len ==> v (get h0 a i) * v s = v (get h1 b i)))
    (ensures (eval h0 a len * v s = eval h1 b len))
    (fun _ -> gscalar_multiplication_lemma h0 h1 a b s len)

#reset-options

opaque type ScalarProduct (h0:heap) (h1:heap) (ctr:nat) (a:bigint) (s:uint63) (res:bigint) =
  Live h0 a /\ Live h1 res /\ ctr <= norm_length
  /\ (forall (i:nat). {:pattern (v (get h1 res i))} i < ctr ==> v (get h1 res i) = v (get h0 a i) * v s)

val scalar_multiplication_aux: res:bigint -> a:bigint{Disjoint res a} -> s:uint63 -> ctr:nat -> ST unit
  (requires (fun h -> Live h res /\ Live h a /\ ctr <= norm_length
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < ctr ==> v (get h a i) * v s < pow2 63) ))
  (ensures (fun h0 _ h1 -> ScalarProduct h0 h1 ctr a s res 
    /\ Modifies (only res) h0 h1 /\ Eq h0 a h1 a /\ EqSub h0 res ctr h1 res ctr (length res - ctr)))
let rec scalar_multiplication_aux res a s ctr =
//  admit();
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> let i = ctr - 1 in 
         let ai = index a i in
	 cut (True /\ v (get h0 a i) * v s < pow2 63);
	 let resi = ai ^* s in
	 upd res i resi; 
	 let h1 = ST.get() in
	 eq_lemma h0 h1 a (only res);
	 scalar_multiplication_aux res a s i; 
	 let h2 = ST.get() in
	 cut (Modifies (only res) h0 h1); cut (Eq h0 a h2 a); 	 
	 cut (forall (i:nat). {:pattern (v (get h2 res (ctr+i-1)))} i < length res - ctr + 1 ==> v (get h2 res (ctr-1 + i)) = v (get h1 res (ctr-1+i)));  
	 cut (forall (i:nat). {:pattern (v (get h2 res (ctr+(i-1))))} i < length res - ctr + 1 ==> v (get h2 res (ctr+i-1)) = v (get h1 res (ctr+i-1)));  
	 cut (forall (i:nat). {:pattern (get h2 res (ctr+i))} i < length res - ctr ==> v (get h2 res (ctr-1+(i+1))) = v (get h1 res (ctr-1+i+1)));  
	 cut (EqSub h1 res ctr h2 res ctr (length res - ctr)); 
	 cut (forall (i:nat). {:pattern (v (get h2 res i))} i < ctr - 1 ==> v (get h2 res i) = v (get h1 a i) * v s); 
	 cut (forall (i:nat). {:pattern (v (get h1 res i))} (i < length res /\ i <> ctr-1) ==> v (get h1 res i) = v (get h0 res i)); 
	 cut (True /\ v (get h2 res (ctr-1+0)) = v (get h0 a (ctr-1)) * v s); 
	 cut (forall (i:nat). i < ctr ==> v (get h2 res i) = v (get h0 a i) * v s); 
	 cut (ScalarProduct h0 h2 ctr a s res); 
	 cut (Eq h0 a h2 a); 
	 cut (EqSub h0 res ctr h1 res ctr (length res - ctr));
	 ()

val scalar_multiplication: res:bigint -> a:bigint{Disjoint res a} -> s:uint63 -> ST unit
  (requires (fun h -> Live h res /\ Live h a
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < norm_length ==> v (get h a i) * v s < pow2 63) ))
  (ensures (fun h0 _ h1 -> ScalarProduct h0 h1 norm_length a s res 
    /\ Modifies (only res) h0 h1 /\ Eq h0 a h1 a 
    /\ EqSub h0 res norm_length h1 res norm_length (length res - norm_length)
    /\ eval h1 res norm_length = eval h0 a norm_length * v s))
let scalar_multiplication res a s =
  let h0 = ST.get() in
  scalar_multiplication_aux res a s norm_length;
  let h1 = ST.get() in
  scalar_multiplication_lemma h0 h1 a res s norm_length;
  ()

#reset-options

(*** Multiplication ***)

val bitweight_lemma_1: i:nat -> Lemma (bitweight templ i = i * templ 0)
let rec bitweight_lemma_1 i = 
  match i with | 0 -> () | _ -> bitweight_lemma_1 (i-1)

val bitweight_lemma_0: i:nat -> j:nat -> 
  Lemma (bitweight templ (i+j) = bitweight templ i + bitweight templ j)
let rec bitweight_lemma_0 i j =
  bitweight_lemma_1 (i+j); bitweight_lemma_1 i; bitweight_lemma_1 j

opaque val gauxiliary_lemma_1: a:nat -> b:nat -> 
  GLemma unit 
    (requires (True))
    (ensures (pow2 (bitweight templ (a+b)) = pow2 (bitweight templ a) * pow2 (bitweight templ b))) []
let gauxiliary_lemma_1 a b =
  bitweight_lemma_0 a b;
  IntLibLemmas.pow2_exp (bitweight templ a) (bitweight templ b)

val auxiliary_lemma_1: a:nat -> b:nat -> 
  Lemma (pow2 (bitweight templ (a+b)) = pow2 (bitweight templ a) * pow2 (bitweight templ b))
let auxiliary_lemma_1 a b = 
  coerce (requires (True)) (ensures (pow2 (bitweight templ (a+b)) = pow2 (bitweight templ a) * pow2 (bitweight templ b))) (fun _ -> gauxiliary_lemma_1 a b)

#reset-options

opaque type PartialEquality (ha:heap) (a:bigint) (hb:heap) (b:bigint) (len:nat) =
  Live ha a /\ Live hb b /\ len <= length a /\ len <= length b	      
  /\ (forall (i:nat). {:pattern (v (get ha a i))} i < len ==> v (get ha a i) = v (get hb b i))

opaque type StoresSum (hc:heap) (c:bigint) (ha:heap) (a:bigint) (hb:heap) (b:bigint)
		      (a_idx:nat) (len:nat) =
  Live ha a /\ Live hb b /\ Live hc c /\ a_idx+len <= length a /\ len <= length b /\ a_idx+len <= length c
  /\  (forall (i:nat). {:pattern (v (get hc c (i+a_idx)))}
	(i < len ==> v (get hc c (i+a_idx)) = v (get ha a (i+a_idx)) + v (get hb b i)))

#reset-options

opaque val gmultiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b} -> c:bigint{Live h1 c} ->
  idx:nat -> len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} ->
  GLemma unit
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight templ idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight templ idx) * eval h0 b (len-1) +
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)))) []
let gmultiplication_step_lemma_1 h0 h1 a b c idx len =
//  admit();
  let t = templ in
  cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1)) /\ True); 
  cut (True /\ eval h1 c (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)) + eval h1 c (len+idx-1)); 
  cut (eval h1 c (len+idx) = eval h1 c (len+idx-1) + pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)) /\ True ); 
  cut (eval h1 c (len+idx-1) = eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1) /\ True); 
  cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1)) /\ True); 
  cut (eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ pow2 (bitweight t (len-1+idx)) * (v (get h0 a (len+idx-1)) + v (get h0 b (len-1))) /\ True);
  distributivity_add_right (pow2 (bitweight t (len-1+idx))) (v (get h0 a (len+idx-1))) (v (get h0 b (len-1))); 
  cut (True /\ eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)))); 
  cut (True /\ eval h1 c (len+idx) = 
	eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)
	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)))); 
  cut (True /\ eval h1 c (len+idx) = eval h0 a (len+idx-1) + pow2 (bitweight t idx) * eval h0 b (len-1)  +
	  pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) +    	        
          pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))); 
  cut (True /\ eval h1 c (len+idx) = 
	pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1) + 
          pow2 (bitweight t idx) * eval h0 b (len-1)  +	        
          pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))); 
  cut (True /\ eval h0 a (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1)); 
  cut (True /\ eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight t idx) * eval h0 b (len-1)  
		+ pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)))

#reset-options

val multiplication_step_lemma_1: h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b} -> 
  c:bigint{Live h1 c} -> idx:nat -> len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma 
    (requires (
      StoresSum h1 c h0 a h0 b idx len
      /\ PartialEquality h1 c h0 a idx
      /\ eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight templ idx) * eval h0 b (len-1)))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1))))
let multiplication_step_lemma_1 h0 h1 a b c idx len = 
  coerce
    (requires (
      (StoresSum h1 c h0 a h0 b idx len)
      /\ (PartialEquality h1 c h0 a idx)    
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight templ idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1))))
    (fun _ -> gmultiplication_step_lemma_1 h0 h1 a b c idx len)
    
#reset-options

opaque val gmultiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b} -> c:bigint{Live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> GLemma unit
    (requires ( eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
    []
let gmultiplication_step_lemma_2 h0 h1 a b c idx len = 
//  admit();
  auxiliary_lemma_1 idx (len-1); 
  cut (True /\ pow2 (bitweight templ (len-1+idx)) = pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) ); 
  paren_mul_left (pow2 (bitweight templ idx)) (pow2 (bitweight templ (len-1))) (v (get h0 b (len-1))); 
  cut (eval h1 c (len+idx) = eval h0 a (len+idx) 
			     + pow2 (bitweight templ idx) * eval h0 b (len-1)
			     + pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)) /\ True); 
  distributivity_add_right (pow2 (bitweight templ idx)) (eval h0 b (len-1)) (pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)));  
  cut (True /\ eval h0 b len = eval h0 b (len-1) + (pow2 (bitweight templ (len-1))) * v (get h0 b (len-1)) ); 
  cut (True /\ pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) =
        pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) * v (get h0 b (len-1))); 
  cut ( True /\ eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len) 

#reset-options

val multiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b} -> c:bigint{Live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma 
    (requires (eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let multiplication_step_lemma_2 h0 h1 a b c idx len = 
  coerce
    (requires (
	 eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1))
    ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
    (fun _ -> gmultiplication_step_lemma_2 h0 h1 a b c idx len)

#reset-options

val multiplication_step_lemma:
  h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b} -> c:bigint{Live h1 c} -> idx:nat ->
  len:nat{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires (StoresSum h1 c h0 a h0 b idx len /\ PartialEquality h1 c h0 a idx))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let rec multiplication_step_lemma h0 h1 a b c idx len =
//  admit();
  match len with
  | 0 ->
    cut (forall (i:nat). {:pattern (v (get h1 c i))} i < idx ==> v (get h1 c i) = v (get h0 a i)); 
    eval_eq_lemma h0 h1 a c idx
  | _ -> multiplication_step_lemma h0 h1 a b c idx (len-1); 
     multiplication_step_lemma_1 h0 h1 a b c idx len; 
     multiplication_step_lemma_2 h0 h1 a b c idx len

#reset-options

opaque type PartialEquality2 (ha:heap) (a:bigint{Live ha a}) (hb:heap) (b:bigint{Live hb b}) 
			    (len:nat) (len2:nat{len2 >= len /\ len2 <= length a /\ len2 <= length b}) =
  (forall (i:nat). {:pattern (v (get ha a i))}  (i < len2 /\ i >= len) ==> v (get ha a i) = v (get hb b i))

opaque val gauxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint{Live h0 a} -> 
  b:bigint{Live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  GLemma unit
    (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
    (ensures (eval h1 b len2 = eval h0 a len2 + c)) []
let rec gauxiliary_lemma_5 h0 h1 a b c len len2 =
//  admit();
  match len2 - len with
  | 0 -> ()
  | _ -> 
     let t = templ in
     gauxiliary_lemma_5 h0 h1 a b c len (len2-1); 
     cut (True /\ eval h1 b (len2-1) = eval h0 a (len2-1) + c); 
     cut (True /\ eval h1 b len2 = eval h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * v (get h1 b (len2-1))); 
     cut (v (get h1 b (len2-1)) = v (get h0 a (len2-1)) /\ True); 
     cut (True /\ eval h1 b len2 = (eval h0 a (len2-1) + c) + (pow2 (bitweight t (len2-1))) * v (get h0 a (len2-1)));  
     cut (True /\ eval h1 b len2 = eval h0 a len2 + c)

opaque val auxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint{Live h0 a} -> 
  b:bigint{Live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  Lemma (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
        (ensures (eval h1 b len2 = eval h0 a len2 + c))
let auxiliary_lemma_5 h0 h1 a b c len len2 =
  coerce (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
         (ensures (eval h1 b len2 = eval h0 a len2 + c))
	 (fun _ -> gauxiliary_lemma_5 h0 h1 a b c len len2)

#reset-options

opaque type Bound27 (h:heap) (b:bigint) = 
  Live h b /\ length b >= norm_length
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 27)

val multiplication_step_0: a:bigint -> b:bigint -> ctr:nat{ctr<norm_length} -> 
  c:bigint{Disjoint a c /\ Disjoint b c} -> tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  ST unit 
     (requires (fun h -> Bound27 h a /\ Norm h b /\ Live h c /\ Live h tmp /\ length c >= 2*norm_length -1
       /\ maxValue h c (length c) <= ctr * pow2 53 ))
     (ensures (fun h0 _ h1 ->
       Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h0 tmp /\ length c >= 2*norm_length-1
       /\ Modifies (only tmp) h0 h1 /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
       /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr) ))
let multiplication_step_0 a b ctr c tmp = 
//  admit();
  let h0 = ST.get() in
  let s = index b ctr in 
  cut (forall (n:nat). {:pattern (v (get h0 b n))} n < norm_length ==> v (get h0 b n) < pow2 27); 
  cut (True /\ 0 <= v s /\ v s < pow2 26);  
  IntLibLemmas.pow2_exp 27 26;
  IntLibLemmas.pow2_increases 63 53; 
  cut (forall (a:nat) (b:nat) (c:pos) (d:pos). (a < c /\ b < d) ==> (a * b < c * d)); 
  cut (forall (i:nat). i < norm_length ==> v (get h0 a i) * v s < pow2 27 * pow2 26);  
  scalar_multiplication tmp a s; 
  let h1 = ST.get() in 
  cut(True /\ v s = v (get h0 b ctr)); 
  assert(ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp);
  ()

val norm_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint{Disjoint a tmp} -> Lemma
    (requires (Norm h0 a /\ Live h0 tmp /\ Modifies (only tmp) h0 h1))
    (ensures (Norm h1 a))
let norm_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

val bound27_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint{Disjoint a tmp} -> Lemma
    (requires (Bound27 h0 a /\ Live h0 tmp /\ Modifies (only tmp) h0 h1))
    (ensures (Bound27 h1 a))
let bound27_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

#reset-options

val aux_lemma_4: unit -> Lemma (pow2 3 = 8)
let aux_lemma_4 () = ()

#reset-options

val aux_lemma_41: b:uint63{v b < pow2 26} -> Lemma (forall (a:uint63). (v a < pow2 27 /\ v b < pow2 26) ==> (v a * v b < pow2 53))
let aux_lemma_41 b = 
//  admit();
  cut (forall (a:uint63). v a < pow2 27 ==> v a * v b < pow2 27 * pow2 26); 
  IntLibLemmas.pow2_exp 27 26

val aux_lemma_42: h:heap -> a:bigint{Bound27 h a} -> z:uint63{v z < pow2 26} -> Lemma (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)
let aux_lemma_42 h a z = 
  cut (forall (i:nat). {:pattern (get h a i)} i < norm_length ==> (v (get h a i) < pow2 27)); 
  aux_lemma_41 z; 
  IntLibLemmas.pow2_exp 27 26;
  cut (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)

#reset-options

val aux_lemma_43: h1:heap -> c:bigint{Live h1 c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{Live h1 tmp} -> ctr:nat{ctr < norm_length} -> Lemma 
  (requires ((forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53)
    /\ (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53) ))
	(ensures (forall (i:nat). {:pattern (v (get h1 c (i+ctr)) + v (get h1 tmp i))} i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * pow2 53))
let aux_lemma_43 h1 c tmp ctr = 
//  admit();
  ()

#reset-options

opaque val gmultiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> 
  GLemma unit
     (requires (
       (Bound27 h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp )) []
let gmultiplication_step_lemma_001 h0 h1 a b ctr c tmp = 
//  admit();
  eq_lemma h0 h1 c (only tmp); 
  cut (True /\ Live h1 c /\ v (get h0 b ctr) < pow2 (templ 0)); 
  cut (forall (i:nat). {:pattern (get h1 c)} i < norm_length ==> i+ctr < length c); 
  cut (forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> (v (get h0 a i) < pow2 27)); 
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  IntLibLemmas.pow2_exp 27 26; 
  aux_lemma_42 h0 a (get h0 b ctr); 
  cut(forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53); 
  maxValue_lemma h1 c;
  cut (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53); 
  aux_lemma_43 h1 c tmp ctr; 
  aux_lemma_4 ();
  cut (True /\ ctr + 1 <= norm_length /\ norm_length = 5 /\ pow2 3 = 8 /\ norm_length < pow2 3); 
  cut(True /\ (ctr+1) * pow2 53 <= pow2 3 * pow2 53); 
  IntLibLemmas.pow2_exp 3 53;
  IntLibLemmas.pow2_increases 63 56;
  cut(True /\ (ctr+1) * pow2 53 < pow2 platform_wide); 
  cut (forall (i:nat). i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) < pow2 63)

val multiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (
       (Bound27 h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp =
  coerce
    (requires ((Bound27 h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
   (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp ))
   (fun _ -> gmultiplication_step_lemma_001 h0 h1 a b ctr c tmp)

#reset-options  

val aux_lemma_5: ctr:nat -> Lemma (ctr * pow2 53 <= (ctr+1) * pow2 53)
let aux_lemma_5 ctr = ()

val aux_lemma_51: ctr:nat -> Lemma (ctr * pow2 53 + pow2 53 = (ctr+1) * pow2 53)
let aux_lemma_51 ctr = ()

#reset-options

opaque val gmax_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> GLemma unit
    (requires (
      Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 )) []
let gmax_value_lemma_1 h0 h1 h2 a b ctr c tmp =
//  admit();
  cut(forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> v (get h0 a i) < pow2 27); 
  cut(forall (i:nat). {:pattern (v (get h0 b i))} i < norm_length ==> v (get h0 b i) < pow2 26); 
  maxValue_lemma h0 c;
  cut (forall (i:nat). {:pattern (v (get h0 c i))} i < length c ==> v (get h0 c i) <= maxValue h0 c (length c)) ;  
  cut (forall (i:nat). {:pattern (v (get h0 c (i+ctr)))} i < norm_length ==> v (get h0 c (i+ctr)) <= maxValue h0 c (length c)); 
  cut (forall (a:nat) (b':nat) (c:nat) (d:nat). {:pattern (v (get h0 b ctr))} (a < c /\ b' < d) ==> a * b' < c * d); 
  aux_lemma_42 h0 a (get h0 b ctr); 
  cut (forall (i:nat). {:pattern (v (get h0 a i) * v (get h0 b ctr))} i < norm_length ==>
    v (get h0 a i) * v (get h0 b ctr) < pow2 53);  
  cut (forall (i:nat). {:pattern (v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr)))} i < norm_length ==> v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr)) <= ctr * pow2 53 + pow2 53); 
  aux_lemma_51 ctr; 
  cut (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))} i < norm_length ==> v (get h2 c (i+ctr)) <= (ctr+1) * pow2 53); 
  cut (forall (i:nat). (i >= ctr /\ i < norm_length + ctr) ==> v (get h2 c (i-ctr+ctr)) <= (ctr+1) * pow2 53); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length+ctr) /\ i < length c) ==> v (get h2 c i) <= ctr * pow2 53); 
  aux_lemma_5 ctr;
  cut (forall (i:nat). i < length c ==> v (get h2 c i) <= (ctr+1) * pow2 53); 
  maxValue_bound_lemma h2 c ((ctr+1) * pow2 53)

val max_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
    (requires (
      Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =       
  coerce  (requires (
      Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
    (fun _ -> gmax_value_lemma_1 h0 h1 h2 a b ctr c tmp)

val max_value_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  Lemma
    (requires (
      Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ maxValue h0 c (length c) <= ctr * pow2 53
      /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
      /\ IsSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ EqSub h1 c 0 h2 c 0 ctr
      /\ EqSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h2 c
       /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
//  admit();
  cut(forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  cut(forall (i:nat). {:pattern (v (get h2 c (i+ctr)))} i < norm_length ==> v (get h2 c (i+ctr)) = v (get h1 c (i+ctr)) + v (get h1 tmp i)); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c (0+i)) = v (get h1 c (0+i)));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < length c - norm_length - ctr ==> v (get h2 c ((norm_length+ctr)+i)) = v (get h1 c ((norm_length+ctr)+i)));
  eq_lemma h0 h1 c (only tmp);
  cut (forall (i:nat). {:pattern (v (get h1 c i))} i < length c ==> v (get h1 c i) = v (get h0 c i)); 
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))}
    i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  cut(forall (i:nat). i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} (i >= norm_length + ctr /\ i < length c) ==> v (get h2 c ((norm_length+ctr)+(i-norm_length-ctr))) = v (get h0 c ((norm_length+ctr)+(i-norm_length-ctr)))); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c (0+i)) = v (get h0 c (0+i)));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} (i >=norm_length + ctr /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c i) = v (get h0 c i));   
  max_value_lemma_1 h0 h1 h2 a b ctr c tmp

val standardized_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint{Disjoint a c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint c tmp} -> Lemma
    (requires (Bound27 h0 a /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Modifies (only tmp) h0 h1
	/\ (Modifies (only c) h1 h2) ))
     (ensures (Bound27 h0 a /\ Bound27 h2 a /\ Live h0 c /\ Live h1 tmp /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h0 h2))
let standardized_lemma h0 h1 h2 a c tmp = 
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)

#reset-options

val standardized_lemma2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint{Disjoint a c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint c tmp} -> Lemma
    (requires (Norm h0 a /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Modifies (only tmp) h0 h1
	/\ (Modifies (only c) h1 h2) ))
     (ensures (Norm h0 a /\ Norm h2 a /\ Live h0 c /\ Live h1 tmp /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h0 h2))
let standardized_lemma2 h0 h1 h2 a c tmp = 
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)
  
#reset-options

val multiplication_step_lemma_02: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Live h0 tmp 
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h0 c (length c) <= ctr * pow2 53
	// After fscalar
	/\ Modifies (only tmp) h0 h1
	/\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
        /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr)
 	// After fsum
	/\ Live h2 c /\ Live h2 tmp /\ Modifies (only c) h1 h2
	/\ IsSum h1 h2 ctr 0 norm_length 0 c tmp
	/\ EqSub h1 c 0 h2 c 0 ctr
	/\ EqSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)))    
     (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h2 c  /\ Live h0 tmp /\ Live h2 tmp
       /\ Bound27 h2 a /\ Norm h2 b
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h2
       /\ (maxValue h2 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr))
     ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
//  admit();
  cut (forall (i:nat). i < ctr ==> v (get h1 c (0+i)) = v (get h2 c (0+i))); 
  cut (forall (i:nat). i < length c - norm_length - ctr ==> v (get h1 c ((norm_length+ctr)+i)) = v (get h2 c ((norm_length+ctr)+i))); 
  eval_partial_eq_lemma h1 h2 c c (norm_length+ctr) (2*norm_length-1); 
  eq_lemma h0 h1 c (only tmp); 
  eval_eq_lemma h0 h1 c c (2*norm_length-1); 
  eval_eq_lemma h0 h1 c c (norm_length+ctr); 
  cut (True /\ eval h2 c (2*norm_length-1) - eval h2 c (norm_length+ctr) = eval h0 c (2*norm_length-1) - eval h0 c (norm_length+ctr)); 
  cut (True /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr)); 
  cut (StoresSum h2 c h1 c h1 tmp ctr norm_length); 
  cut (PartialEquality h2 c h1 c ctr); 
  multiplication_step_lemma h1 h2 c tmp c ctr norm_length; 
  cut (True /\ eval h2 c (norm_length+ctr) = eval h1 c (norm_length+ctr) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  cut (True /\ eval h2 c (norm_length+ctr) = eval h0 c (norm_length+ctr) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  cut (True /\ eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  max_value_lemma h0 h1 h2 a b ctr c tmp; 
  cut (True /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53); 
  standardized_lemma h0 h1 h2 a c tmp; 
  standardized_lemma2 h0 h1 h2 b c tmp
  
#reset-options

val multiplication_step_p1: a:bigint -> b:bigint -> ctr:nat{ctr<norm_length} -> 
  c:bigint{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  ST unit 
     (requires (fun h -> (Bound27 h a) /\ (Norm h b) /\ (Live h c) /\ (Live h tmp)
        /\ (maxValue h c (length c) <= ctr * pow2 53)
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr) ))
     (ensures (fun h0 u h1 -> (Bound27 h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h0 tmp)       
       /\ (Bound27 h1 a) /\ (Norm h1 b) /\ (Live h1 c) /\ (Live h1 tmp) /\ (Modifies (only c ++ tmp) h0 h1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ (maxValue h1 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr)
       /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)) ))
let multiplication_step_p1 a b ctr c tmp =
//  admit();
  let h0 = ST.get() in
  multiplication_step_0 a b ctr c tmp; 
  let h1 = ST.get() in
  multiplication_step_lemma_001 h0 h1 a b ctr c tmp; 
  fsum_index c ctr tmp 0 norm_length 0; 
  let h2 = ST.get() in 
  multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp;
  ()
  
val helper_lemma_6: h0:heap -> h1:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint{Disjoint a c /\ Disjoint b c /\ length c >= 2 * norm_length - 1} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h0 c
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a (norm_length) * v (get h0 b ctr)  = eval h0 a (norm_length) * v (get h0 b ctr) * pow2 (bitweight templ ctr) + eval h0 c (2*norm_length-1) ))
let helper_lemma_6 h0 h1 a b ctr c tmp = 
//  admit();
  ()

val multiplication_step: a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> ST unit  
     (requires (fun h -> Bound27 h a /\ Norm h b /\ Live h c /\ Live h tmp
	/\ maxValue h c (length c) <= ctr * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr  ))
     (ensures (fun h0 u h1 -> Bound27 h0 a /\ Bound27 h1 a /\ Norm h0 b /\ Norm h1 b
       /\ Live h0 c /\ Live h1 c  /\ Live h0 tmp /\ Live h1 tmp /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= ctr * pow2 53
       /\ maxValue h1 c (length c) <= (ctr+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b ctr) * pow2 (bitweight templ ctr) + eval h0 c (2*norm_length-1) ))
let multiplication_step a b ctr c tmp =
  let h0 = ST.get() in
  multiplication_step_p1 a b ctr c tmp;  
  let h1 = ST.get() in
  helper_lemma_6 h0 h1 a b ctr c tmp;
  ()
  
opaque val gmultiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{Norm h0 a} -> 
  b:bigint{Norm h0 b} -> ctr:pos{ctr<=norm_length} -> 
  c:bigint{Live h1 c /\ length c >= 2*norm_length-1} -> GLemma unit
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1))) []
let gmultiplication_step_lemma_03 h0 h1 a b ctr c = 
//  admit();
  let t = templ in 
  paren_mul_left (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * v (get h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ) ; 
  distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr)); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr)))
  
#reset-options

val multiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{Norm h0 a} -> 
  b:bigint{Norm h0 b} -> ctr:pos{ctr<=norm_length} -> 
  c:bigint{Live h1 c /\ length c >= 2*norm_length-1} -> Lemma 
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
let multiplication_step_lemma_03 h0 h1 a b ctr c = 
  coerce (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
	 (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
	 (fun _ -> gmultiplication_step_lemma_03 h0 h1 a b ctr c)

#reset-options

val helper_lemma_12: a:nat -> v:nat -> p:nat -> b:nat -> Lemma (a * v * p + (a * b) = a * (p * v + b))
let helper_lemma_12 a v p b = ()

#reset-options

opaque val gmultiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} ->  c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> GLemma unit
    (requires (Bound27 h0 a /\ Bound27 h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
    []
let gmultiplication_aux_lemma h0 h1 a b ctr c tmp =
//  admit();
  eq_lemma h0 h1 a (only c ++ tmp);
  eq_lemma h0 h1 b (only c ++ tmp);
  eval_eq_lemma h0 h1 a a norm_length;
  eval_eq_lemma h0 h1 b b norm_length;
  eval_eq_lemma h0 h1 b b (norm_length - ctr);
  eval_eq_lemma h0 h1 b b (norm_length - ctr + 1);
  cut((norm_length - ctr)+1 = norm_length - ctr + 1 /\ True); 
  cut(eval h0 a norm_length = eval h1 a norm_length /\ eval h0 b (norm_length-ctr) = eval h1 b (norm_length - ctr) /\ eval h0 b (norm_length - ctr + 1) = eval h1 b (norm_length - ctr + 1) /\ v (get h0 b (norm_length - ctr)) = v (get h1 b (norm_length - ctr))); 
  helper_lemma_12 (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight templ (norm_length - ctr))) (eval h0 b (norm_length - ctr))

val multiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} ->  c:bigint{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
    (requires (Bound27 h0 a /\ Bound27 h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp = 
  coerce 
    (requires (Bound27 h0 a /\ Bound27 h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) )) 
  (fun _ -> gmultiplication_aux_lemma h0 h1 a b ctr c tmp)

#reset-options

val multiplication_aux_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr <= norm_length} -> c:bigint{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
    (requires (Bound27 h0 a /\ Norm h0 b /\ Live h1 c /\ Live h1 tmp
       /\ Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
       /\ Bound27 h2 a /\ Norm h2 b /\ Live h2 c /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h1 h2 /\ Modifies (only c ++ tmp) h0 h1
       /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length) ))
    (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h1 c /\ Bound27 h2 a /\ Norm h2 b /\ Live h2 c
       /\ Modifies (only c ++ tmp) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
//  admit();
  eq_lemma h0 h1 a (only c ++ tmp);
  eq_lemma h0 h1 b (only c ++ tmp);
  eval_eq_lemma h0 h1 a a norm_length; 
  eval_eq_lemma h0 h1 b b norm_length

val multiplication_aux: a:bigint -> b:bigint -> ctr:nat{ctr<=norm_length} -> 
  c:bigint{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> ST unit
     (requires (fun h -> Bound27 h a /\ Norm h b /\ Live h c /\ Live h tmp
	/\ maxValue h c (length c) <= (norm_length - ctr) * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - ctr) ))
     (ensures (fun h0 u h1 -> Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Live h0 tmp
       /\ Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp /\ Modifies (only c ++ tmp) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let rec multiplication_aux a b ctr c tmp = 
//  admit();
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> 
    multiplication_step a b (norm_length - ctr) c tmp; 
    let h1 = ST.get() in    
    multiplication_aux_lemma h0 h1 a b ctr c tmp; 
    multiplication_aux a b (ctr-1) c tmp; 
    let h2 = ST.get() in
    multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp;
    ()

#reset-options

val helper_lemma_13: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (Bound27 h0 a /\ Modifies empty h0 h1))
    (ensures (Bound27 h0 a /\ Bound27 h1 a /\ Live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a =  
//  admit();
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

val helper_lemma_131: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (Norm h0 a /\ Modifies empty h0 h1))
    (ensures (Norm h0 a /\ Norm h1 a /\ Live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_131 h0 h1 a =  
//  admit();
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

opaque val ghelper_lemma_15: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> GLemma unit
    (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
    (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
    []
let ghelper_lemma_15 h0 h1 c =
//  admit();
  eq_lemma h0 h1 c empty;
  eval_null h1 c (2*norm_length - 1); 
  max_value_of_null_lemma h1 c (length c)

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> Lemma
    (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
    (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  coerce (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
	 (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
	 (fun _ -> ghelper_lemma_15 h0 h1 c)

#reset-options

opaque val gmultiplication_lemma_1: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} ->  b:bigint{Disjoint c b} -> GLemma unit
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) )) []
let gmultiplication_lemma_1 h0 h1 c a b =
//  admit();
  helper_lemma_13 h0 h1 a;
  helper_lemma_131 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(True /\ eval h1 b 0 = 0)

val multiplication_lemma_1: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} ->  b:bigint{Disjoint c b} -> Lemma
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) ))
let multiplication_lemma_1 h0 h1 c a b =
  coerce
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) ))
     (fun _ -> gmultiplication_lemma_1 h0 h1 c a b)

#reset-options

val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint -> tmp:bigint{Disjoint c tmp} ->
  Lemma
    (requires (Live h0 c /\ Live h2 c /\ not(contains h0 tmp) /\ Modifies empty h0 h1 /\ Live h1 tmp /\ Modifies (only c ++ tmp) h1 h2))
    (ensures (Modifies (only c) h0 h2))
let helper_lemma_14 h0 h1 h2 c tmp =
//  admit();
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.Live h0 #t b)} 
	 SBuffer.Live h0 #t b ==> DisjointSet b (only tmp)); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.Live h0 #t b)}
	 (SBuffer.Live h0 #t b /\ DisjointSet b (only c ++ tmp)) <==> (SBuffer.Live h0 #t b /\ DisjointSet b (only c))); 
  cut (Modifies (only c ++ tmp) h0 h2); 
  cut (forall (#t:pos) (b:buffer t). (SBuffer.Live h0 b /\ DisjointSet b (only c ++ tmp)) ==> Eq h0 b h2 b); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (DisjointSet b (only c))}
				  (SBuffer.Live h0 b /\ DisjointSet b (only c)) ==> Eq h0 b h2 b)

#reset-options

val multiplication_lemma_2: h0:heap -> h1:heap -> h2:heap -> c:bigint{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} -> b:bigint{Disjoint c b} -> 
  tmp:bigint{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
     (requires (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c
	/\ Modifies empty h0 h1 /\ not(contains h0 tmp) /\ Live h1 tmp
	/\ Bound27 h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)
        /\ Bound27 h2 a /\ Norm h2 b /\ Live h2 c
        /\ Modifies (only c ++ tmp) h1 h2
        /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length)
        /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
     (ensures (Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Bound27 h2 a /\ Norm h2 b /\ Live h2 c
       /\ Modifies (only c) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
//  admit();
  helper_lemma_14 h0 h1 h2 c tmp; 
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

#reset-options

(* Code : core multiplication function *)
val multiplication: c:bigint{length c >= 2*norm_length-1} -> a:bigint{Disjoint c a} -> 
  b:bigint{Disjoint c b} -> ST unit
     (requires (fun h -> Bound27 h a /\ Norm h b /\ Live h c /\ Null h c))
     (ensures (fun h0 u h1 -> Bound27 h0 a /\ Norm h0 b /\ Live h0 c /\ Bound27 h1 a /\ Norm h1 b /\ Live h1 c
       /\ Modifies (only c) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let multiplication c a b =
//  admit();
  let h0 = ST.get() in
  let tmp = create #63 FStar.UInt63.zero norm_length in 
  let h1 = ST.get() in
  multiplication_lemma_1 h0 h1 c a b; 
  multiplication_aux a b norm_length c tmp; 
  let h2 = ST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp;
  ()

(*** Modulo ***)

#reset-options

(*
let op_Bar_Amp  = FStar.UInt63.logand 
let op_Bar_Greater_Greater  = FStar.UInt63.shift_right 
let op_Bar_Less_Less  = FStar.UInt63.shift_left 
let op_Bar_Plus  = FStar.UInt63.add 
let op_Bar_Star  = FStar.UInt63.mul 

let op_Bar_Amp (x:uint63) (y:uint63) : uint63 = FStar.UInt63.logand x y
let op_Bar_Greater_Greater (x:uint63) y : uint63 = FStar.UInt63.shift_right x y
let op_Bar_Less_Less (x:uint63) y : uint63 = FStar.UInt63.shift_left x y
let op_Bar_Plus (x:uint63) (y:uint63) : uint63 = FStar.UInt63.add x y
let op_Bar_Star (x:uint63) (y:uint63) : uint63 = FStar.UInt63.mul x y
*)

val prime_modulo_lemma: unit -> Lemma (pow2 130 % (reveal prime) = 5)
let prime_modulo_lemma () = 
  admitP(b2t(pow2 130 % (reveal prime) = 5));
  ()

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a)) 
  [SMTPat (a % b)]
let modulo_lemma a b = ()

type SatisfiesModuloConstraints (h:heap) (b:bigint) = 
  Live h b /\ length b >= 2*norm_length-1 && maxValue h b (2*norm_length-1) * 6 < pow2 62

val times_5: x:uint63{5 * v x < pow2 63} -> Tot (y:uint63{v y = 5 * v x})
let times_5 x = 
//  admit();
  let z = x ^<< 2 in x ^+ z
  
opaque type Reducible (h:heap) (b:bigint) (ctr:nat{ctr < norm_length-1}) =
  Live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (get h b (i+norm_length))}
      i <= ctr ==> v (get h b i) + 5 * v (get h b (i+norm_length)) < pow2 63)

opaque type Times5 (h0:heap) (h1:heap) (b:bigint) (ctr:nat{ctr < norm_length - 1}) =
  Live h0 b /\ Live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)}
       i <= ctr ==> v (get h1 b i) = v (get h0 b i) + 5 * (v (get h0 b (i+norm_length))))

opaque type Untouched (h0:heap) (h1:heap) (b:bigint) (ctr:nat) = 
  Live h0 b /\ Live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==> 
      v (get h0 b i) = v (get h1 b i))

#reset-options

val pow2_bitweight_lemma_1: ctr:pos -> GLemma unit (requires (True))
    (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)) []
let rec pow2_bitweight_lemma_1 ctr =
//  admit();
  match ctr with
  | 1 -> ()
  | _ -> 
    cut(ctr-1+norm_length = ctr+norm_length-1 /\ ctr+norm_length-1 = (ctr-1) + norm_length
	/\ (ctr+norm_length-1)-1=ctr+norm_length-2); 
    pow2_bitweight_lemma_1 (ctr-1); 
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-2)) = pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    cut (True /\ bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 26); 
    IntLibLemmas.pow2_exp (bitweight templ (ctr+norm_length-2)) 26; 
    cut(True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * pow2 (bitweight templ (ctr+norm_length-2))); 
    cut(True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * (pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)));  
    paren_mul_right (pow2 26) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    IntLibLemmas.pow2_exp 26 (bitweight templ (ctr-2));
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (26 + bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)) 

#reset-options

val bitweight_norm_length_lemma: unit -> Lemma 
  (requires (True)) 
  (ensures (bitweight templ norm_length = 130))
  [SMTPat (bitweight templ norm_length)]
let bitweight_norm_length_lemma () = 
//  admit();
  ()

#reset-options
(* TODO *)
val helper_lemma_5: a:nat -> b:nat -> c:nat -> p:pos -> 
  Lemma (requires (True))
	(ensures ( (a*b+c) % p = ((a % p) * b + c)%p))
let helper_lemma_5 a b c p =
  admitP(b2t( (a*b+c) % p = ((a % p) * b + c)%p));
  ()

val lemma_aux_0: a:int -> b:int -> c:int -> d:int -> Lemma (a * b + c - (a * (b + 5 * d) + c) = - 5 * a * d)
let lemma_aux_0 a b c d = ()

opaque val freduce_degree_lemma_2: h0:heap -> h1:heap -> b:bigint{Live h1 b /\ Live h0 b /\ length b >= 2 * norm_length - 1} -> ctr:pos{ctr < norm_length-1} -> GLemma unit
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
	/\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime))) []
let freduce_degree_lemma_2 h0 h1 b ctr =
//  admit();
  let prime = reveal prime in 
  cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); 
  cut (True /\ eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length)); 
  pow2_bitweight_lemma_1 (ctr+1); 
  cut(True /\ pow2 (bitweight templ (norm_length+ctr)) = pow2 130 * pow2 (bitweight templ ctr)); 
  paren_mul_left (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  paren_mul_right (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  cut (True /\ eval h0 b (norm_length+1+ctr) = (pow2 130 * pow2 (bitweight templ ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)); 
  helper_lemma_5 (pow2 130) (pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) (eval h0 b (norm_length+ctr)) prime; 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = ((pow2 130 % prime) * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  prime_modulo_lemma (); 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  eval_eq_lemma h0 h1 b b ctr; 
  cut (True /\ eval h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval h0 b ctr); 
  cut (True /\ eval h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (get h0 b ctr) + 5 * v (get h0 b (norm_length+ctr))) + eval h0 b ctr); 
  lemma_aux_0 (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (eval h0 b ctr) (v (get h0 b (norm_length+ctr)));
  cut (eval h0 b (ctr+1) - eval h1 b (ctr+1) = - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) /\ True); 
  distributivity_add_right (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (5 * v (get h0 b (norm_length+ctr))); 
  eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr); 
  cut (eval h0 b (norm_length+ctr) - eval h0 b (ctr+1) = eval h1 b (norm_length+ctr) - eval h1 b (ctr+1) /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) + eval h0 b (ctr+1) - eval h1 b (ctr+1)) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (eval h1 b (norm_length+ctr) ) % prime /\ True)

#reset-options

opaque val gfreduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint{Live h1 b /\ Live h0 b /\ length b >= 2 * norm_length - 1} -> 
  ctr:nat{ctr < norm_length-1} -> GLemma unit
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))  []
let gfreduce_degree_lemma h0 h1 b ctr =
//  admit();
  let prime = reveal prime in
  if ctr = 0 then (
    helper_lemma_5 (pow2 130) (v (get h0 b norm_length)) (eval h0 b norm_length) prime;
    prime_modulo_lemma ();
    cut(eval h0 b 1 = v (get h0 b 0) /\ eval h1 b 1 = v (get h0 b 0) + 5 * v (get h0 b norm_length)); 
    eval_partial_eq_lemma h0 h1 b b 1 norm_length;
    cut(True /\ eval h1 b norm_length - eval h1 b 1 = eval h0 b norm_length - eval h0 b 1)
  ) else (
    freduce_degree_lemma_2 h0 h1 b ctr
  )

val freduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint{Live h1 b /\ Live h0 b /\ length b >= 2 * norm_length - 1} -> 
  ctr:nat{ctr < norm_length-1} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime))) 
let freduce_degree_lemma h0 h1 b ctr =
  coerce 
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
    (fun _ -> gfreduce_degree_lemma h0 h1 b ctr)

#reset-options

val freduce_degree': 
  b:bigint -> ctr:nat{ctr < norm_length - 1} -> ST unit 
    (requires (fun h -> Reducible h b ctr)) 
    (ensures (fun h0 _ h1 -> Untouched h0 h1 b ctr /\ Times5 h0 h1 b ctr
      /\ eval h1 b (norm_length) % reveal prime = eval h0 b (norm_length+1+ctr) % reveal prime
      /\ Modifies (only b) h0 h1))
let rec freduce_degree' b ctr' =
//  admit();
  let h0 = ST.get() in
  match ctr' with
  | 0 -> 
    let b5ctr = index b (0+norm_length) in 
    let bctr = index b 0 in
    let b5ctr = times_5 b5ctr in
    let bctr = bctr ^+ b5ctr in 
    upd b 0 bctr;
    let h1 = ST.get() in
    freduce_degree_lemma h0 h1 b 0;
    cut (True /\ eval h0 b (norm_length+1+0) % reveal prime = eval h1 b (norm_length+0) % reveal prime);
    cut (True /\ eval h0 b (norm_length+1) % reveal prime = eval h1 b (norm_length+0) % reveal prime)
  | _ -> 
    let ctr = ctr' in
    let b5ctr = index b (ctr + norm_length) in 
    let bctr = index b ctr in
    let b5ctr = times_5 b5ctr in
    let bctr = bctr ^+ b5ctr in 
    upd b ctr bctr;
    let h1 = ST.get() in
    freduce_degree_lemma h0 h1 b ctr; 
    cut (True /\ eval h0 b (norm_length+1+ctr) % reveal prime = eval h1 b (norm_length+ctr) % reveal prime);
    cut(Reducible h1 b (ctr-1)); 
    freduce_degree' b (ctr-1); 
    let h2 = ST.get() in 
    cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > ctr /\ i < 2*norm_length-1) ==>
	   v (get h1 b i) = v (get h0 b i)); 
    cut(Untouched h0 h2 b ctr);
    cut (Times5 h0 h2 b ctr) ;
    ()

#reset-options

val aux_lemma_4': h:heap -> b:bigint -> Lemma
  (requires (SatisfiesModuloConstraints h b))
  (ensures (Reducible h b (norm_length-2)))
let aux_lemma_4' h b =
//  admit();
  maxValue_lemma_aux h b (2*norm_length-1);
  IntLibLemmas.pow2_increases 63 62

#reset-options

val aux_lemma_5': h0:heap -> h1:heap -> b:bigint -> Lemma
  (requires (Live h0 b /\ SatisfiesModuloConstraints h0 b /\ Times5 h0 h1 b (norm_length-2)
      /\ Untouched h0 h1 b (norm_length-2)))
  (ensures (Live h0 b /\ SatisfiesModuloConstraints h0 b /\ Times5 h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (get h1 b i) < pow2 62)))
let aux_lemma_5' h0 h1 b = 
//  admit();
  maxValue_lemma_aux h0 b (2*norm_length-1)

#reset-options

val freduce_degree: b:bigint -> ST unit 
  (requires (fun h -> Live h b /\ SatisfiesModuloConstraints h b)) 
  (ensures (fun h0 _ h1 -> Live h0 b /\ Live h1 b /\ SatisfiesModuloConstraints h0 b
    /\ Modifies (only b) h0 h1
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> 
	v (get h1 b i) < pow2 62)
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
//  admit();
  let h0 = ST.get() in
  aux_lemma_4' h0 b; 
  freduce_degree' b (norm_length-2); 
  let h1 = ST.get() in
  aux_lemma_5' h0 h1 b

#reset-options

opaque val gpow2_bitweight_lemma: ctr:nat -> GLemma unit 
    (requires (True)) 
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr))) []
let gpow2_bitweight_lemma ctr =
  IntLibLemmas.pow2_exp (bitweight templ ctr) (templ ctr)

val pow2_bitweight_lemma: ctr:nat -> Lemma
    (requires (True)) 
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
let pow2_bitweight_lemma ctr =
  coerce 
    (requires (True)) 
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
    (fun _ -> gpow2_bitweight_lemma ctr)

#reset-options

val helper_lemma_2: pb:nat -> pc:pos -> a0:nat -> b:nat ->
  Lemma  (ensures ((pb*pc) * a0/pc + (pb * (a0 % pc) + b) = pb * a0 + b))
let helper_lemma_2 pb pc a0 b = ()

#reset-options

opaque val geval_carry_lemma: ha:heap -> a:bigint{Live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint{Live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> GLemma unit
    (requires (v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1))) []
let geval_carry_lemma ha a hb b ctr =
//  admit();
  eval_eq_lemma ha hb a b ctr;
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + eval hb b (ctr+1)); 
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (get hb b ctr) + eval hb b ctr));  
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr)); 
  distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (get ha a (ctr+1))) (v (get ha a ctr) / pow2 (templ ctr));
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  pow2_bitweight_lemma ctr; 
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (get ha a ctr)) (eval hb b ctr); 
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (get ha a ctr) + eval hb b ctr));  
  cut(True /\ eval hb b (ctr+2) = eval ha a (ctr+2)); 
  eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1)

#reset-options

val eval_carry_lemma:
  ha:heap -> a:bigint{Live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint{Live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> Lemma
    (requires (v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr = 
  coerce
    (requires (
      v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i))
    ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
    (fun _ -> geval_carry_lemma ha a hb b ctr)

#reset-options

val helper_lemma_4: a:nat -> b:nat -> c:pos -> size:pos{size > c} ->
  Lemma (requires (a < pow2 (size-1) /\ b < pow2 (size-c)))
	(ensures (a + b < pow2 size))
let helper_lemma_4 a b c size = 
//  admit();
  if size-1 > size - c then IntLibLemmas.pow2_increases (size-1) (size-c) else ()

opaque val gauxiliary_lemma_1': bip1:uint63 -> c:uint63 -> GLemma unit
    (requires (v bip1 < pow2 62 /\ v c < pow2 (63 - 26)))
    (ensures (v bip1 + v c < pow2 63))  []
let gauxiliary_lemma_1' bip1 c =
  helper_lemma_4 (v bip1) (v c) 26 63

opaque val auxiliary_lemma_1': bip1:uint63 -> c:uint63 -> 
  Lemma
    (requires (v bip1 < pow2 (63  - 1) /\ v c < pow2 (63 - 26)))
    (ensures (v bip1 + v c < pow2 63))
let auxiliary_lemma_1' bip1 c =
  coerce
    (requires (v bip1 < pow2 (63  - 1) /\ v c < pow2 (63 - 26)))
    (ensures (v bip1 + v c < pow2 63))
    (fun _ -> gauxiliary_lemma_1' bip1 c)

opaque val gauxiliary_lemma_2: bip1:uint63 -> c:uint63 -> GLemma unit
    (requires (v bip1 < pow2 26 /\ v c < pow2 15))
    (ensures (v bip1 + v c < pow2 27))  []
let gauxiliary_lemma_2 bip1 c =
  helper_lemma_4 (v bip1) (v c) 12 27

opaque val auxiliary_lemma_2: bip1:uint63 -> c:uint63 -> 
  Lemma
    (requires (v bip1 < pow2 26 /\ v c < pow2 15))
    (ensures (v bip1 + v c < pow2 27))
let auxiliary_lemma_2 bip1 c =
  coerce
    (requires (v bip1 < pow2 26 /\ v c < pow2 15))
    (ensures (v bip1 + v c < pow2 27)) 
    (fun _ -> gauxiliary_lemma_2 bip1 c)

#reset-options

val mod2_26: a:uint63 -> Tot (b:uint63{v b = v a % pow2 26})
let mod2_26 a = 
//  admit();
  let mask = shift_left one 26 in
  cut (v mask = pow2 26 % pow2 63 /\ pow2 26 >= 1); 
  IntLibLemmas.pow2_increases 63 26; 
  let mask = FStar.UInt63.sub mask one in
  let res = a ^& mask in
  Sint.ulogand_lemma_4 #63 a 26 mask;
  res

opaque type Carriable (h:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) =
  Live h b /\ length b >= norm_length + 1  
  /\ (forall (i:nat). {:pattern (v (get h b i))}
      (i > ctr /\ i <= norm_length) ==> v (get h b i) < pow2 62)

opaque type Carried (h1:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) =
  Live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (get h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h1 b norm_length) < pow2 37)
  
opaque type Carried' (h1:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) =
  Live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= ctr /\ i < norm_length) ==> v (get h1 b i) < pow2 (templ ctr))
  /\ v (get h1 b norm_length) < pow2 37
  
opaque type Untouched_2 (h0:heap) (h1:heap) (b:bigint) (ctr:nat) =
  Live h0 b /\ Live h1 b /\ length b >= norm_length+1 
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (get h0 b i) = v (get h1 b i))

val carry: b:bigint -> ctr:nat{ctr <= norm_length} -> ST unit
    (requires (fun h -> Carriable h b ctr /\ Carried h b ctr))
    (ensures (fun h0 _ h1 -> Carried h1 b norm_length /\ Untouched_2 h0 h1 b ctr
      /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
//      /\ v (get h1 b (norm_length)) = IntLib.div (v (get h0 b (norm_length-1))) (pow2 26)
      /\ Modifies (only b) h0 h1 ))
let rec carry b i =
//  admit();
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in
    let ri = mod2_26 bi in
    assert(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^>> 26) in
    cut (v bi < pow2 63 /\ v c = IntLib.div (v bi) (pow2 26)); 
    IntLibLemmas.pow2_div 63 26;
    (* TODO *)
    admitP (True /\ v c < pow2 (63 - 26)); 
    let bip1 = index b (i+1) in
    assert(v bip1 = v (get h1 b (i+1))); 
    assert(v bip1 < pow2 (63 - 1)); 
    auxiliary_lemma_1' bip1 c; 
    let z = bip1 ^+ c in
    upd b (i+1) z;
    let h2 = ST.get() in
    eval_carry_lemma h0 b h2 b i; 
    carry b (i+1)

val carry_top_to_0: b:bigint -> ST unit
    (requires (fun h -> Carried h b norm_length /\ length b >= 2*norm_length-1
      /\ v (get h b 0) + 5 * v (get h b norm_length) < pow2 62))
    (ensures (fun h0 _ h1 -> Carried h0 b norm_length /\ Carried' h1 b 1
      /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime)
      /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (get h1 b i) = v (get h0 b i))
      /\ Modifies (only b) h0 h1))
let carry_top_to_0 b =
//  admit();
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  let btop_5 = times_5 btop in  
    upd b 0 (b0 ^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0

#reset-options

opaque type Carriable2 (h:heap) (b:bigint) (ctr:pos{ctr<=norm_length}) =
  Live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < ctr ==> v (get h b i) < pow2 26)
  /\ (forall (i:nat). {:pattern (v (get h b i))} (i > ctr /\ i < norm_length) ==> v (get h b i) < pow2 26)
  /\ (ctr < norm_length ==> v (get h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h b norm_length) < 2)
  /\ v (get h b ctr) < pow2 26 + pow2 15
  /\ (v (get h b ctr) >= pow2 26 ==> (
      forall (i:nat). {:pattern (v (get h b i))} ( i < ctr /\ i > 0) ==> v (get h b i) < pow2 15))
  /\ ((ctr = norm_length /\ v (get h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (get h b i))} (i > 0 /\ i < norm_length) ==> v (get h b i) < pow2 15))

val lemma_aux: a:nat -> b:pos -> Lemma (IntLib.div a b > 0 ==> a >= b)
let lemma_aux a b = 
//  admit();
  ()

(* TODO *)
val lemma_aux_2: a:uint63 -> Lemma ((v a < pow2 26+pow2 15 /\ v a >= pow2 26) ==> v a % pow2 26 < pow2 15)
let lemma_aux_2 a = 
  admitP((v a < pow2 26+pow2 15 /\ v a >= pow2 26) ==> v a % pow2 26 < pow2 15);
  ()

#reset-options

val carry2_aux: b:bigint -> ctr:pos{ctr <= norm_length} -> ST unit
  (requires (fun h -> Carriable2 h b ctr))
  (ensures (fun h0 _ h1 -> Carriable2 h0 b ctr /\ Carriable2 h1 b norm_length
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ Modifies (only b) h0 h1 ))
let rec carry2_aux b i = 
//  admit();
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in 
    let ri = mod2_26 bi in
    lemma_aux_2 bi;
    assert(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^>> 26) in
    // In the spec of >>, TODO
    admitP(True /\ v c < 2); 
    let bip1 = index b (i+1) in
    auxiliary_lemma_2 bip1 c; 
    IntLibLemmas.pow2_increases 63 27;
    IntLibLemmas.pow2_doubles 26;
    IntLibLemmas.pow2_increases 26 15;
    let z = bip1 ^+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 26); 
    cut (True /\ v z >= pow2 26 ==> v c = 1); 
    cut (v c > 0 ==> IntLib.div (v (get h0 b i)) (pow2 26) > 0 ==> v (get h0 b i) >= pow2 26); 
    cut (v z >= pow2 26 ==> v (get h1 b i) < pow2 15); 
    upd b (i+1) z;
    let h2 = ST.get() in 
    cut (v z >= pow2 26 ==> v c = 1 /\ True); 
    eval_carry_lemma h0 b h2 b i; 
    carry2_aux b (i+1)

#reset-options

val pow2_3_lemma: unit -> Lemma (pow2 3 = 8)
let pow2_3_lemma () = 
//  admit();
  ()

val carry2: b:bigint -> ST unit
  (requires (fun h -> Carried h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> Carried h0 b norm_length /\ Carriable2 h1 b norm_length 
    /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ Modifies (only b) h0 h1))
let rec carry2 b = 
//  admit();
  let h0 = ST.get() in
  pow2_3_lemma ();
  IntLibLemmas.pow2_exp 3 37;
  IntLibLemmas.pow2_increases 40 37;
  IntLibLemmas.pow2_increases 40 26;
  IntLibLemmas.pow2_doubles 40;
  IntLibLemmas.pow2_increases 62 41;
  carry_top_to_0 b;
  let h1 = ST.get() in
  upd b norm_length FStar.UInt63.zero;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (True /\ eval h2 b (norm_length+1) = eval h1 b (norm_length)); 
  let bi = index b 0 in 
  let ri = mod2_26 bi in
  assert(v ri < pow2 26); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^>> 26) in
  cut (True /\ v bi < pow2 41); 
  // In the spec of >>, TODO
  admitP(True /\ v c < pow2 15); 
  let bip1 = index b 1 in 
  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 63 27;
  IntLibLemmas.pow2_doubles 26;
  IntLibLemmas.pow2_increases 26 15; 
  let z = bip1 ^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut(Carriable2 h4 b 1);
  carry2_aux b 1
  
#reset-options

val last_carry: b:bigint -> ST unit
  (requires (fun h -> Carriable2 h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> Carriable2 h0 b norm_length /\ Norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ Modifies (only b) h0 h1))
let last_carry b =
//  admit();
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  cut (v b0 < pow2 26 /\ v btop < 2); 
  pow2_3_lemma ();
  cut (5 * v btop < pow2 3 /\ True); 
  IntLibLemmas.pow2_increases 26 3;
  IntLibLemmas.pow2_doubles 26;
  IntLibLemmas.pow2_increases 63 27;
  cut(v b0 + 5 * v btop < pow2 27 /\ True); 
  let btop_5 = times_5 btop in  
  upd b 0 (b0 ^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0;
  upd b norm_length FStar.UInt63.zero;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (True /\ eval h2 b (norm_length+1) = eval h1 b norm_length);
  let bi = index b 0 in 
  let ri = mod2_26 bi in
  assert(v ri < pow2 26); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^>> 26) in
  cut (True /\ v bi < pow2 26 + 5); 
  cut (v bi >= pow2 26 ==> v (get h3 b 1) < pow2 15); 
  // In the spec of >>, TODO
  admitP(v bi >= pow2 26 ==> v c = 1); 
  let bip1 = index b 1 in 
  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 63 27;
  IntLibLemmas.pow2_doubles 26;
  IntLibLemmas.pow2_increases 26 15; 
  let z = bip1 ^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (True /\ v (get h4 b 1) < pow2 26); 
  cut (True /\ Norm h4 b)

#reset-options

val modulo: b:bigint -> ST unit
  (requires (fun h -> Live h b /\ SatisfiesModuloConstraints h b))
  (ensures (fun h0 _ h1 -> Live h0 b /\ SatisfiesModuloConstraints h0 b /\ Norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime 
    /\ Modifies (only b) h0 h1))
let modulo b =
//  admit();
  let h0 = ST.get() in
  freduce_degree b; 
  let h1 = ST.get() in
  upd b norm_length FStar.UInt63.zero;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (True /\ eval h2 b (norm_length+1) = eval h1 b norm_length);
  carry b 0; 
  let h3 = ST.get() in
  carry2 b; 
  let h4 = ST.get() in
  last_carry b

#reset-options

val freduce_coefficients: b:bigint -> ST unit
  (requires (fun h -> Live h b  
    /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 62)))
  (ensures (fun h0 _ h1 -> Live h0 b /\ Norm h1 b 
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime
    /\ Modifies (only b) h0 h1))
let freduce_coefficients b = 
//  admit();
  let h0 = ST.get() in
  let tmp = create #63 FStar.UInt63.zero (2*norm_length-1) in
  let h1 = ST.get() in
  eq_lemma h0 h1 b empty; 
  eval_eq_lemma h0 h1 b b norm_length; 
  blit b 0 tmp 0 norm_length;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b tmp norm_length;
  cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp i) = v (get h0 b i)); 
  carry tmp 0; 
  carry2 tmp; 
  last_carry tmp; 
  let h = ST.get() in
  blit tmp 0 b 0 norm_length; 
  let h' = ST.get() in
  eval_eq_lemma h h' tmp b norm_length; 
  cut (forall (i:nat). {:pattern (v (get h tmp i))} i < norm_length ==> v (get h tmp i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h' b i))} i < norm_length ==> v (get h' b (0+i)) = v (get h tmp (0+i)))


(* Inlined version of the multiplication 
val mult: c:array sint -> a:array sint -> b:array sint -> 
  ST unit
    (requires (fun h -> 
      Heap.contains h a /\ Heap.contains h b /\ Heap.contains h c
      /\ Seq.length (sel h a) >= 3 /\ Seq.length (sel h b) >= 3 /\ Seq.length (sel h c) >= 3))
    (ensures (fun h0 _ h1 -> 
      valueOf h1 c = (valueOf h0 a * valueOf h0 b) % p))
let mult c a b =
  (* Multiplication *)
  let c0 = index a 0 |* index b 0 in
  let c1 = (index a 1 |* index b 0) |+ (index a 0 |* index b 1) in
  let c2 = (index a 2 |* index b 0) |+ (index a 1 |* index b 1) |+ (index a 0 |* index b 2) in
  let c3 = ((index a 2 |* index b 1) |+ (index a 1 |* index b 2)) |<< 2 in
  let c4 = (index a 2 |* index b 2) |<< 2 in
  (* Remove the top limbs *)
  let c3_4 = c3 |<< 2 in
  let c0 = c0 |+ c3_4 |+ c3 in
  let c4_4 = c4 |<< 2 in
  let c1 = c1 |+ c4_4 |+ c4 in
  (* First carry pass *)
  let c1 = c1 |+ (c0 |>> 44) in
  let c0 = mod2n c0 44 in
  let c2 = c2 |+ (c1 |>> 44) in
  let c1 = mod2n c1 44 in
  let carry = c2 |>> 42 in
  (* Carry c2 to c0 *)
  let carry_4 = carry |<< 2 in
  let carry = carry |+ carry_4 in
  let c0 = c0 |+ carry in
  (* Snd carry pass *)
  let c1 = c1 |+ (c0 |>> 44) in
  let c0 = mod2n c0 44 in
  let c2 = c2 |+ (c1 |>> 44) in
  let c1 = mod2n c1 44 in
  let carry = c2 |>> 42 in
  let carry_4 = carry |<< 2 in
  let carry = carry |+ carry_4 in
  let c0 = c0 |+ carry in  
  (* Values are now between 0 and 2^130 *)
  let two42m5 = to_sint "4398046511099" in
  let two44m1 = to_sint "17592186044415" in
  let mask = gte_limb c0 two42m5 in
  let mask = mask |& (eq_limb c1 two44m1) in
  let mask = mask |& (eq_limb c2 two44m1) in
  (* Subtract values if output is >= 2^130 - 5, else do nothing, in constant time *)
  let submask1 = mask |& two42m5 in
  let submask2 = mask |& two44m1 in
  upd c 0 (c0 |- submask1);
  upd c 1 (c1 |- submask2);
  upd c 2 (c2 |- submask2)
 *)
