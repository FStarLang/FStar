module Bignum.Fproduct

open FStar.Heap
open FStar.Ghost
open IntLib
open IntLibLemmas
open Sint
open SBuffer
open FStar.UInt64
open Bignum.Parameters
open Bignum.Bigint
open Bignum.Fsum
open Bignum.FsumWide
open Bignum.Fscalar

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

opaque type PartialEquality (ha:heap) (#size:pos) (a:buffer size) (hb:heap) (b:buffer size) (len:nat) =
  Live ha a /\ Live hb b /\ len <= length a /\ len <= length b	      
  /\ (forall (i:nat). {:pattern (v (get ha a i))} i < len ==> v (get ha a i) = v (get hb b i))

opaque type StoresSum (hc:heap) (c:bigint_wide) (ha:heap) (a:bigint_wide) (hb:heap) (b:bigint_wide)
		      (a_idx:nat) (len:nat) =
  Live ha a /\ Live hb b /\ Live hc c /\ a_idx+len <= length a /\ len <= length b /\ a_idx+len <= length c
  /\  (forall (i:nat). {:pattern (v (get hc c (i+a_idx)))}
	(i < len ==> v (get hc c (i+a_idx)) = v (get ha a (i+a_idx)) + v (get hb b i)))

#reset-options

opaque val gmultiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> b:bigint_wide{Live h0 b} -> c:bigint_wide{Live h1 c} ->
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
  admit();
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

val multiplication_step_lemma_1: h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> b:bigint_wide{Live h0 b} -> 
  c:bigint_wide{Live h1 c} -> idx:nat -> len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma 
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
  h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> b:bigint_wide{Live h0 b} -> c:bigint_wide{Live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> GLemma unit
    (requires ( eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
    []
let gmultiplication_step_lemma_2 h0 h1 a b c idx len = 
  admit();
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
  h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> b:bigint_wide{Live h0 b} -> c:bigint_wide{Live h1 c} -> idx:nat ->
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
  h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> b:bigint_wide{Live h0 b} -> c:bigint_wide{Live h1 c} -> idx:nat ->
  len:nat{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires (StoresSum h1 c h0 a h0 b idx len /\ PartialEquality h1 c h0 a idx))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let rec multiplication_step_lemma h0 h1 a b c idx len =
  admit();
  match len with
  | 0 ->
    cut (forall (i:nat). {:pattern (v (get h1 c i))} i < idx ==> v (get h1 c i) = v (get h0 a i)); 
    eval_eq_lemma h0 h1 a c idx
  | _ -> multiplication_step_lemma h0 h1 a b c idx (len-1); 
     multiplication_step_lemma_1 h0 h1 a b c idx len; 
     multiplication_step_lemma_2 h0 h1 a b c idx len

#reset-options

opaque type PartialEquality2 (ha:heap) (#size:pos) (a:buffer size{Live ha a}) (hb:heap) (b:buffer size{Live hb b}) 
			    (len:nat) (len2:nat{len2 >= len /\ len2 <= length a /\ len2 <= length b}) =
  (forall (i:nat). {:pattern (v (get ha a i))}  (i < len2 /\ i >= len) ==> v (get ha a i) = v (get hb b i))

opaque val gauxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> 
  b:bigint_wide{Live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  GLemma unit
    (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
    (ensures (eval h1 b len2 = eval h0 a len2 + c)) []
let rec gauxiliary_lemma_5 h0 h1 a b c len len2 =
  admit();
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

opaque val auxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint_wide{Live h0 a} -> 
  b:bigint_wide{Live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  Lemma (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
        (ensures (eval h1 b len2 = eval h0 a len2 + c))
let auxiliary_lemma_5 h0 h1 a b c len len2 =
  coerce (requires (eval h1 b len = eval h0 a len + c /\ PartialEquality2 h1 b h0 a len len2))
         (ensures (eval h1 b len2 = eval h0 a len2 + c))
	 (fun _ -> gauxiliary_lemma_5 h0 h1 a b c len len2)

#reset-options

// TODO: change with the appropriate value from the parameters
opaque type Bound (h:heap) (b:bigint) = 
  Live h b /\ length b >= norm_length
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 platform_wide)

val multiplication_step_0: a:bigint -> b:bigint -> ctr:nat{ctr<norm_length} -> 
  c:bigint_wide{Disjoint a c /\ Disjoint b c} -> tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  ST unit 
     (requires (fun h -> Bound h a /\ Norm h b /\ Live h c /\ Live h tmp /\ length c >= 2*norm_length -1
       /\ maxValue h c (length c) <= ctr * pow2 53 ))
     (ensures (fun h0 _ h1 ->
       Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h0 tmp /\ length c >= 2*norm_length-1
       /\ Modifies (only tmp) h0 h1 /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
       /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr) ))
let multiplication_step_0 a b ctr c tmp = 
  admit();
  let h0 = ST.get() in
  let s = index b ctr in 
  cut (forall (n:nat). {:pattern (v (get h0 b n))} n < norm_length ==> v (get h0 b n) < pow2 52); 
  cut (True /\ 0 <= v s /\ v s < pow2 26);  
  IntLibLemmas.pow2_exp 52 26;
  IntLibLemmas.pow2_increases 63 53; 
  cut (forall (a:nat) (b:nat) (c:pos) (d:pos). (a < c /\ b < d) ==> (a * b < c * d)); 
  cut (forall (i:nat). i < norm_length ==> v (get h0 a i) * v s < pow2 52 * pow2 26);  
  scalar_multiplication tmp a s; 
  let h1 = ST.get() in 
  cut(True /\ v s = v (get h0 b ctr)); 
  assert(ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp);
  ()

val norm_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{Disjoint a tmp} -> Lemma
    (requires (Norm h0 a /\ Live h0 tmp /\ Modifies (only tmp) h0 h1))
    (ensures (Norm h1 a))
let norm_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

val bound52_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{Disjoint a tmp} -> Lemma
    (requires (Bound h0 a /\ Live h0 tmp /\ Modifies (only tmp) h0 h1))
    (ensures (Bound h1 a))
let bound52_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

#reset-options

val aux_lemma_4: unit -> Lemma (pow2 3 = 8)
let aux_lemma_4 () = ()

#reset-options

val aux_lemma_41: b:limb{v b < pow2 26} -> Lemma (forall (a:limb). (v a < pow2 52 /\ v b < pow2 26) ==> (v a * v b < pow2 53))
let aux_lemma_41 b = 
  admit();
  cut (forall (a:limb). v a < pow2 52 ==> v a * v b < pow2 52 * pow2 26); 
  IntLibLemmas.pow2_exp 52 26

val aux_lemma_42: h:heap -> a:bigint{Bound h a} -> z:limb{v z < pow2 26} -> Lemma (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)
let aux_lemma_42 h a z = 
  admit();
  cut (forall (i:nat). {:pattern (get h a i)} i < norm_length ==> (v (get h a i) < pow2 52)); 
  aux_lemma_41 z; 
  IntLibLemmas.pow2_exp 52 26;
  cut (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)

#reset-options

val aux_lemma_43: h1:heap -> c:bigint_wide{Live h1 c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{Live h1 tmp} -> ctr:nat{ctr < norm_length} -> Lemma 
  (requires ((forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53)
    /\ (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53) ))
	(ensures (forall (i:nat). {:pattern (v (get h1 c (i+ctr)) + v (get h1 tmp i))} i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * pow2 53))
let aux_lemma_43 h1 c tmp ctr = 
  admit();
  ()

#reset-options

opaque val gmultiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> 
  GLemma unit
     (requires (
       (Bound h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp )) []
let gmultiplication_step_lemma_001 h0 h1 a b ctr c tmp = 
  admit();
  eq_lemma h0 h1 c (only tmp); 
  cut (True /\ Live h1 c /\ v (get h0 b ctr) < pow2 (templ 0)); 
  cut (forall (i:nat). {:pattern (get h1 c)} i < norm_length ==> i+ctr < length c); 
  cut (forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> (v (get h0 a i) < pow2 52)); 
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  IntLibLemmas.pow2_exp 52 26; 
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
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (
       (Bound h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp =
  coerce
    (requires ((Bound h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ Modifies (only tmp) h0 h1
       /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
   (ensures ( (Live h1 c) /\ (Live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ WillNotOverflow h1 ctr 0 norm_length 0 c tmp ))
   (fun _ -> gmultiplication_step_lemma_001 h0 h1 a b ctr c tmp)

#reset-options  

val aux_lemma_5: ctr:nat -> Lemma (ctr * pow2 53 <= (ctr+1) * pow2 53)
let aux_lemma_5 ctr = 
  admit();
  ()

val aux_lemma_51: ctr:nat -> Lemma (ctr * pow2 53 + pow2 53 = (ctr+1) * pow2 53)
let aux_lemma_51 ctr = 
  admit();
  ()

#reset-options

opaque val gmax_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> GLemma unit
    (requires (
      Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 )) []
let gmax_value_lemma_1 h0 h1 h2 a b ctr c tmp =
  admit();
  cut(forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> v (get h0 a i) < pow2 52); 
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
  ctr:nat{ctr < norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
    (requires (
      Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =       
  coerce  (requires (
      Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
    (fun _ -> gmax_value_lemma_1 h0 h1 h2 a b ctr c tmp)

val max_value_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  Lemma
    (requires (
      Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h2 c /\ Live h1 c
      /\ Modifies (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ maxValue h0 c (length c) <= ctr * pow2 53
      /\ ScalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
      /\ IsSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ EqSub h1 c 0 h2 c 0 ctr
      /\ EqSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h2 c
       /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
  admit();
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

val standardized_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint_wide{Disjoint a c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint c tmp} -> Lemma
    (requires (Bound h0 a /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Modifies (only tmp) h0 h1
	/\ (Modifies (only c) h1 h2) ))
     (ensures (Bound h0 a /\ Bound h2 a /\ Live h0 c /\ Live h1 tmp /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h0 h2))
let standardized_lemma h0 h1 h2 a c tmp = 
  admit();
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)

#reset-options

val standardized_lemma2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint_wide{Disjoint a c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint c tmp} -> Lemma
    (requires (Norm h0 a /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Modifies (only tmp) h0 h1
	/\ (Modifies (only c) h1 h2) ))
     (ensures (Norm h0 a /\ Norm h2 a /\ Live h0 c /\ Live h1 tmp /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h0 h2))
let standardized_lemma2 h0 h1 h2 a c tmp = 
  admit();
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)
  
#reset-options

val multiplication_step_lemma_02: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h1 tmp /\ Live h1 c /\ Live h0 tmp 
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
     (ensures (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h2 c  /\ Live h0 tmp /\ Live h2 tmp
       /\ Bound h2 a /\ Norm h2 b
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h2
       /\ (maxValue h2 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr))
     ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
  admit();
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
  c:bigint_wide{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} ->  ST unit 
     (requires (fun h -> (Bound h a) /\ (Norm h b) /\ (Live h c) /\ (Live h tmp)
        /\ (maxValue h c (length c) <= ctr * pow2 53)
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr) ))
     (ensures (fun h0 u h1 -> (Bound h0 a) /\ (Norm h0 b) /\ (Live h0 c) /\ (Live h0 tmp)       
       /\ (Bound h1 a) /\ (Norm h1 b) /\ (Live h1 c) /\ (Live h1 tmp) /\ (Modifies (only c ++ tmp) h0 h1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ (maxValue h1 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr)
       /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)) ))
let multiplication_step_p1 a b ctr c tmp =
  admit();
  let h0 = ST.get() in
  multiplication_step_0 a b ctr c tmp; 
  let h1 = ST.get() in
  multiplication_step_lemma_001 h0 h1 a b ctr c tmp; 
  fsum_index c ctr tmp 0 norm_length 0; 
  let h2 = ST.get() in 
  multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp;
  ()
  
val helper_lemma_6: h0:heap -> h1:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Disjoint a c /\ Disjoint b c /\ length c >= 2 * norm_length - 1} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h0 c
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a (norm_length) * v (get h0 b ctr)  = eval h0 a (norm_length) * v (get h0 b ctr) * pow2 (bitweight templ ctr) + eval h0 c (2*norm_length-1) ))
let helper_lemma_6 h0 h1 a b ctr c tmp = 
  admit();
  ()

val multiplication_step: a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> ST unit  
     (requires (fun h -> Bound h a /\ Norm h b /\ Live h c /\ Live h tmp
	/\ maxValue h c (length c) <= ctr * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr  ))
     (ensures (fun h0 u h1 -> Bound h0 a /\ Bound h1 a /\ Norm h0 b /\ Norm h1 b
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
  c:bigint_wide{Live h1 c /\ length c >= 2*norm_length-1} -> GLemma unit
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1))) []
let gmultiplication_step_lemma_03 h0 h1 a b ctr c = 
  admit();
  let t = templ in 
  paren_mul_left (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * v (get h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ) ; 
  distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr)); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr)))
  
#reset-options

val multiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{Norm h0 a} -> 
  b:bigint{Norm h0 b} -> ctr:pos{ctr<=norm_length} -> 
  c:bigint_wide{Live h1 c /\ length c >= 2*norm_length-1} -> Lemma 
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
let multiplication_step_lemma_03 h0 h1 a b ctr c = 
  coerce (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
	 (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
	 (fun _ -> gmultiplication_step_lemma_03 h0 h1 a b ctr c)

#reset-options

val helper_lemma_12: a:nat -> v:nat -> p:nat -> b:nat -> Lemma (a * v * p + (a * b) = a * (p * v + b))
let helper_lemma_12 a v p b = 
  admit();
  ()

#reset-options

opaque val gmultiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} ->  c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> GLemma unit
    (requires (Bound h0 a /\ Bound h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
    []
let gmultiplication_aux_lemma h0 h1 a b ctr c tmp =
  admit();
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
  ctr:pos{ctr <= norm_length} ->  c:bigint_wide{Disjoint a c /\ Disjoint b c} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
    (requires (Bound h0 a /\ Bound h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp = 
  coerce 
    (requires (Bound h0 a /\ Bound h1 a /\ Norm h0 b /\ Norm h1 b 
       /\ Live h0 c /\ Live h1 c /\ Live h0 tmp /\ Live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ Modifies (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) )) 
  (fun _ -> gmultiplication_aux_lemma h0 h1 a b ctr c tmp)

#reset-options

val multiplication_aux_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr <= norm_length} -> c:bigint_wide{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma 
    (requires (Bound h0 a /\ Norm h0 b /\ Live h1 c /\ Live h1 tmp
       /\ Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp
       /\ Bound h2 a /\ Norm h2 b /\ Live h2 c /\ Live h2 tmp
       /\ Modifies (only c ++ tmp) h1 h2 /\ Modifies (only c ++ tmp) h0 h1
       /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length) ))
    (ensures (Bound h0 a /\ Norm h0 b /\ Live h1 c /\ Bound h2 a /\ Norm h2 b /\ Live h2 c
       /\ Modifies (only c ++ tmp) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
  admit();
  eq_lemma h0 h1 a (only c ++ tmp);
  eq_lemma h0 h1 b (only c ++ tmp);
  eval_eq_lemma h0 h1 a a norm_length; 
  eval_eq_lemma h0 h1 b b norm_length

val multiplication_aux: a:bigint -> b:bigint -> ctr:nat{ctr<=norm_length} -> 
  c:bigint_wide{Disjoint a c /\ Disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> ST unit
     (requires (fun h -> Bound h a /\ Norm h b /\ Live h c /\ Live h tmp
	/\ maxValue h c (length c) <= (norm_length - ctr) * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - ctr) ))
     (ensures (fun h0 u h1 -> Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Live h0 tmp
       /\ Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Live h1 tmp /\ Modifies (only c ++ tmp) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let rec multiplication_aux a b ctr c tmp = 
  admit();
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
    (requires (Bound h0 a /\ Modifies empty h0 h1))
    (ensures (Bound h0 a /\ Bound h1 a /\ Live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a =  
  admit();
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

val helper_lemma_131: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (Norm h0 a /\ Modifies empty h0 h1))
    (ensures (Norm h0 a /\ Norm h1 a /\ Live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_131 h0 h1 a =  
  admit();
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

opaque val ghelper_lemma_15: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> GLemma unit
    (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
    (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
    []
let ghelper_lemma_15 h0 h1 c =
  admit();
  eq_lemma h0 h1 c empty;
  eval_null h1 c (2*norm_length - 1); 
  max_value_of_null_lemma h1 c (length c)

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> Lemma
    (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
    (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  coerce (requires (Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
	 (ensures (Live h1 c /\ Null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
	 (fun _ -> ghelper_lemma_15 h0 h1 c)

#reset-options

opaque val gmultiplication_lemma_1: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} ->  b:bigint{Disjoint c b} -> GLemma unit
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) )) []
let gmultiplication_lemma_1 h0 h1 c a b =
  admit();
  helper_lemma_13 h0 h1 a;
  helper_lemma_131 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(True /\ eval h1 b 0 = 0)

val multiplication_lemma_1: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} ->  b:bigint{Disjoint c b} -> Lemma
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) ))
let multiplication_lemma_1 h0 h1 c a b =
  coerce
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c /\ Modifies empty h0 h1))
     (ensures (Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) ))
     (fun _ -> gmultiplication_lemma_1 h0 h1 c a b)

#reset-options

val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide -> tmp:bigint_wide{Disjoint c tmp} ->
  Lemma
    (requires (Live h0 c /\ Live h2 c /\ not(contains h0 tmp) /\ Modifies empty h0 h1 /\ Live h1 tmp /\ Modifies (only c ++ tmp) h1 h2))
    (ensures (Modifies (only c) h0 h2))
let helper_lemma_14 h0 h1 h2 c tmp =
  admit();
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.Live h0 #t b)} 
	 SBuffer.Live h0 #t b ==> DisjointSet b (only tmp)); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.Live h0 #t b)}
	 (SBuffer.Live h0 #t b /\ DisjointSet b (only c ++ tmp)) <==> (SBuffer.Live h0 #t b /\ DisjointSet b (only c))); 
  cut (Modifies (only c ++ tmp) h0 h2); 
  cut (forall (#t:pos) (b:buffer t). (SBuffer.Live h0 b /\ DisjointSet b (only c ++ tmp)) ==> Eq h0 b h2 b); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (DisjointSet b (only c))}
				  (SBuffer.Live h0 b /\ DisjointSet b (only c)) ==> Eq h0 b h2 b)

#reset-options

val multiplication_lemma_2: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> 
  a:bigint{Disjoint c a} -> b:bigint{Disjoint c b} -> 
  tmp:bigint_wide{Disjoint a tmp /\ Disjoint b tmp /\ Disjoint c tmp} -> Lemma
     (requires (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Null h0 c
	/\ Modifies empty h0 h1 /\ not(contains h0 tmp) /\ Live h1 tmp
	/\ Bound h1 a /\ Norm h1 b /\ Live h1 c /\ Null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)
        /\ Bound h2 a /\ Norm h2 b /\ Live h2 c
        /\ Modifies (only c ++ tmp) h1 h2
        /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length)
        /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
     (ensures (Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Bound h2 a /\ Norm h2 b /\ Live h2 c
       /\ Modifies (only c) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
  admit();
  helper_lemma_14 h0 h1 h2 c tmp; 
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

#reset-options

(* Code : core multiplication function *)
val multiplication: c:bigint_wide{length c >= 2*norm_length-1} -> a:bigint{Disjoint c a} -> 
  b:bigint{Disjoint c b} -> ST unit
     (requires (fun h -> Bound h a /\ Norm h b /\ Live h c /\ Null h c))
     (ensures (fun h0 u h1 -> Bound h0 a /\ Norm h0 b /\ Live h0 c /\ Bound h1 a /\ Norm h1 b /\ Live h1 c
       /\ Modifies (only c) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let multiplication c a b =
  admit();
  let h0 = ST.get() in
  let tmp = create #128 zero_wide norm_length in // Hardcoding size
  let h1 = ST.get() in
  multiplication_lemma_1 h0 h1 c a b; 
  multiplication_aux a b norm_length c tmp; 
  let h2 = ST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp;
  ()

