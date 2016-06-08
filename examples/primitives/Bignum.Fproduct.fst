module Bignum.Fproduct

open FStar.Heap
open FStar.Ghost
open IntLib
open IntLibLemmas
open SInt
open SBuffer
open SInt.UInt64
open Bignum.Parameters
open Bignum.Bigint
open Bignum.Fsum
open Bignum.FsumWide
open Bignum.Fscalar

#set-options "--lax"

val bitweight_lemma_1: i:nat -> Lemma (bitweight templ i = i * templ 0)
let rec bitweight_lemma_1 i = 
  match i with | 0 -> () | _ -> bitweight_lemma_1 (i-1)

val bitweight_lemma_0: i:nat -> j:nat -> 
  Lemma (bitweight templ (i+j) = bitweight templ i + bitweight templ j)
let rec bitweight_lemma_0 i j =
  bitweight_lemma_1 (i+j); bitweight_lemma_1 i; bitweight_lemma_1 j

val auxiliary_lemma_1: a:nat -> b:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 (bitweight templ (a+b)) = pow2 (bitweight templ a) * pow2 (bitweight templ b)))
let auxiliary_lemma_1 a b =
  bitweight_lemma_0 a b;
  IntLibLemmas.pow2_exp (bitweight templ a) (bitweight templ b)

abstract let partialEquality (ha:heap) (#size:pos) (a:buffer size) (hb:heap) (b:buffer size) (len:nat) =
  live ha a /\ live hb b /\ len <= length a /\ len <= length b	      
  /\ (forall (i:nat). {:pattern (v (get ha a i))} i < len ==> v (get ha a i) = v (get hb b i))

abstract let storesSum (hc:heap) (c:bigint_wide) (ha:heap) (a:bigint_wide) (hb:heap) (b:bigint_wide)
		      (a_idx:nat) (len:nat) =
  live ha a /\ live hb b /\ live hc c /\ a_idx+len <= length a /\ len <= length b /\ a_idx+len <= length c
  /\  (forall (i:nat). {:pattern (v (get hc c (i+a_idx)))}
	(i < len ==> v (get hc c (i+a_idx)) = v (get ha a (i+a_idx)) + v (get hb b i)))

val multiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} ->
  idx:nat -> len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} ->
  Lemma
    (requires (
      (storesSum h1 c h0 a h0 b idx len)
      /\ (partialEquality h1 c h0 a idx)
      /\ (eval h1 c (len-1+idx) = eval h0 a (len-1+idx) + pow2 (bitweight templ idx) * eval h0 b (len-1))))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) +  
		          pow2 (bitweight templ idx) * eval h0 b (len-1) +
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)))) 
let multiplication_step_lemma_1 h0 h1 a b c idx len =
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
    
val multiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires ( eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let multiplication_step_lemma_2 h0 h1 a b c idx len = 
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

val multiplication_step_lemma:
  h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} -> idx:nat ->
  len:nat{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires (storesSum h1 c h0 a h0 b idx len /\ partialEquality h1 c h0 a idx))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let rec multiplication_step_lemma h0 h1 a b c idx len =
  match len with
  | 0 ->
    cut (forall (i:nat). {:pattern (v (get h1 c i))} i < idx ==> v (get h1 c i) = v (get h0 a i)); 
    eval_eq_lemma h0 h1 a c idx
  | _ -> multiplication_step_lemma h0 h1 a b c idx (len-1); 
     multiplication_step_lemma_1 h0 h1 a b c idx len; 
     multiplication_step_lemma_2 h0 h1 a b c idx len

abstract let partialEquality2 (ha:heap) (#size:pos) (a:buffer size{live ha a}) (hb:heap) (b:buffer size{live hb b}) 
			    (len:nat) (len2:nat{len2 >= len /\ len2 <= length a /\ len2 <= length b}) =
  (forall (i:nat). {:pattern (v (get ha a i))}  (i < len2 /\ i >= len) ==> v (get ha a i) = v (get hb b i))

val auxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> 
  b:bigint_wide{live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  Lemma
    (requires (eval h1 b len = eval h0 a len + c /\ partialEquality2 h1 b h0 a len len2))
    (ensures (eval h1 b len2 = eval h0 a len2 + c))
let rec auxiliary_lemma_5 h0 h1 a b c len len2 =
  match len2 - len with
  | 0 -> ()
  | _ -> 
     let t = templ in
     auxiliary_lemma_5 h0 h1 a b c len (len2-1); 
     cut (True /\ eval h1 b (len2-1) = eval h0 a (len2-1) + c); 
     cut (True /\ eval h1 b len2 = eval h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * v (get h1 b (len2-1))); 
     cut (v (get h1 b (len2-1)) = v (get h0 a (len2-1)) /\ True); 
     cut (True /\ eval h1 b len2 = (eval h0 a (len2-1) + c) + (pow2 (bitweight t (len2-1))) * v (get h0 a (len2-1)));  
     cut (True /\ eval h1 b len2 = eval h0 a len2 + c)

// TODO: change with the appropriate value from the parameters
abstract let bound (h:heap) (b:bigint) = 
  live h b /\ length b >= norm_length
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 platform_wide)

val multiplication_step_0: a:bigint -> b:bigint -> ctr:nat{ctr<norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} -> tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  ST unit 
     (requires (fun h -> bound h a /\ norm h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length -1
       /\ maxValue h c (length c) <= ctr * pow2 53 ))
     (ensures (fun h0 _ h1 ->
       bound h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h0 tmp /\ length c >= 2*norm_length-1
       /\ modifies_buf (only tmp) h0 h1 /\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
       /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr) ))
let multiplication_step_0 a b ctr c tmp = 
  let h0 = ST.get() in
  let s = index b ctr in 
  cut (forall (n:nat). {:pattern (v (get h0 b n))} n < norm_length ==> v (get h0 b n) < pow2 52); 
  cut (0 <= v s /\ v s < pow2 26);  
  IntLibLemmas.pow2_exp 52 26;
  IntLibLemmas.pow2_increases 63 53; 
  cut (forall (a:nat) (b:nat) (c:pos) (d:pos). (a < c /\ b < d) ==> (a * b < c * d)); 
  cut (forall (i:nat). i < norm_length ==> v (get h0 a i) * v s < pow2 52 * pow2 26);  
  scalar_multiplication tmp a s; 
  let h1 = ST.get() in 
  cut(v s = v (get h0 b ctr)); 
  cut(scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp);
  ()

val norm_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{disjoint a tmp} -> Lemma
    (requires (norm h0 a /\ live h0 tmp /\ modifies_buf (only tmp) h0 h1))
    (ensures (norm h1 a))
let norm_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

val bound52_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{disjoint a tmp} -> Lemma
    (requires (bound h0 a /\ live h0 tmp /\ modifies_buf (only tmp) h0 h1))
    (ensures (bound h1 a))
let bound52_lemma h0 h1 a tmp = eq_lemma h0 h1 a (only tmp)

val aux_lemma_4: unit -> Lemma (pow2 3 = 8)
let aux_lemma_4 () = ()

val aux_lemma_41: b:limb{v b < pow2 26} -> Lemma (forall (a:limb). (v a < pow2 52 /\ v b < pow2 26) ==> (v a * v b < pow2 53))
let aux_lemma_41 b = 
  cut (forall (a:limb). v a < pow2 52 ==> v a * v b < pow2 52 * pow2 26); 
  IntLibLemmas.pow2_exp 52 26

val aux_lemma_42: h:heap -> a:bigint{bound h a} -> z:limb{v z < pow2 26} -> Lemma (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)
let aux_lemma_42 h a z = 
  cut (forall (i:nat). {:pattern (get h a i)} i < norm_length ==> (v (get h a i) < pow2 52)); 
  aux_lemma_41 z; 
  IntLibLemmas.pow2_exp 52 26;
  cut (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)

val aux_lemma_43: h1:heap -> c:bigint_wide{live h1 c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{live h1 tmp} -> ctr:nat{ctr < norm_length} -> Lemma 
  (requires ((forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53)
    /\ (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53) ))
	(ensures (forall (i:nat). {:pattern (v (get h1 c (i+ctr)) + v (get h1 tmp i))} i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * pow2 53))
let aux_lemma_43 h1 c tmp ctr = 
  ()

val multiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> 
  Lemma
     (requires (
       (bound h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h1 tmp)
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ modifies_buf (only tmp) h0 h1
       /\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (live h1 c) /\ (live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ willNotOverflow h1 ctr 0 norm_length 0 c tmp ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp = 
  eq_lemma h0 h1 c (only tmp); 
  cut (True /\ live h1 c /\ v (get h0 b ctr) < pow2 (templ 0)); 
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

val aux_lemma_5: ctr:nat -> Lemma (ctr * pow2 53 <= (ctr+1) * pow2 53)
let aux_lemma_5 ctr = 
  ()

val aux_lemma_51: ctr:nat -> Lemma (ctr * pow2 53 + pow2 53 = (ctr+1) * pow2 53)
let aux_lemma_51 ctr = 
  ()

val max_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (
      bound h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c
      /\ modifies_buf (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (bound h0 a /\ norm h0 b /\ live h2 c 
      /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =
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

val max_value_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  Lemma
    (requires (
      bound h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c
      /\ modifies_buf (only tmp) h0 h1 /\ length c >= 2 * norm_length - 1
      /\ maxValue h0 c (length c) <= ctr * pow2 53
      /\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
      /\ isSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ equalSub h1 c 0 h2 c 0 ctr
      /\ equalSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)))
    (ensures (bound h0 a /\ norm h0 b /\ live h2 c
       /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
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

val standardized_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint_wide{disjoint a c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint c tmp} -> Lemma
    (requires (bound h0 a /\ live h0 c /\ live h1 tmp /\ live h1 c /\ modifies_buf (only tmp) h0 h1
	/\ (modifies_buf (only c) h1 h2) ))
     (ensures (bound h0 a /\ bound h2 a /\ live h0 c /\ live h1 tmp /\ live h2 tmp
       /\ modifies_buf (only c ++ tmp) h0 h2))
let standardized_lemma h0 h1 h2 a c tmp = 
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)

val standardized_lemma2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint_wide{disjoint a c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint c tmp} -> Lemma
    (requires (norm h0 a /\ live h0 c /\ live h1 tmp /\ live h1 c /\ modifies_buf (only tmp) h0 h1
	/\ (modifies_buf (only c) h1 h2) ))
     (ensures (norm h0 a /\ norm h2 a /\ live h0 c /\ live h1 tmp /\ live h2 tmp
       /\ modifies_buf (only c ++ tmp) h0 h2))
let standardized_lemma2 h0 h1 h2 a c tmp = 
  eq_lemma h1 h2 tmp (only c);
  eq_lemma h0 h2 a (only c ++ tmp)

val multiplication_step_lemma_02: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
     (requires (bound h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h1 c /\ live h0 tmp 
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h0 c (length c) <= ctr * pow2 53
	// After fscalar
	/\ modifies_buf (only tmp) h0 h1
	/\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
        /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr)
 	// After fsum
	/\ live h2 c /\ live h2 tmp /\ modifies_buf (only c) h1 h2
	/\ isSum h1 h2 ctr 0 norm_length 0 c tmp
	/\ equalSub h1 c 0 h2 c 0 ctr
	/\ equalSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)))    
     (ensures (bound h0 a /\ norm h0 b /\ live h0 c /\ live h2 c  /\ live h0 tmp /\ live h2 tmp
       /\ bound h2 a /\ norm h2 b
       /\ length c >= 2 * norm_length - 1 /\ modifies_buf (only c ++ tmp) h0 h2
       /\ (maxValue h2 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr))
     ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
  cut (forall (i:nat). i < ctr ==> v (get h1 c (0+i)) = v (get h2 c (0+i))); 
  cut (forall (i:nat). i < length c - norm_length - ctr ==> v (get h1 c ((norm_length+ctr)+i)) = v (get h2 c ((norm_length+ctr)+i))); 
  eval_partial_eq_lemma h1 h2 c c (norm_length+ctr) (2*norm_length-1); 
  eq_lemma h0 h1 c (only tmp); 
  eval_eq_lemma h0 h1 c c (2*norm_length-1); 
  eval_eq_lemma h0 h1 c c (norm_length+ctr); 
  cut (eval h2 c (2*norm_length-1) - eval h2 c (norm_length+ctr) = eval h0 c (2*norm_length-1) - eval h0 c (norm_length+ctr)); 
  cut (eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr)); 
  cut (storesSum h2 c h1 c h1 tmp ctr norm_length); 
  cut (partialEquality h2 c h1 c ctr); 
  multiplication_step_lemma h1 h2 c tmp c ctr norm_length; 
  cut (eval h2 c (norm_length+ctr) = eval h1 c (norm_length+ctr) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  cut (eval h2 c (norm_length+ctr) = eval h0 c (norm_length+ctr) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  cut (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)); 
  max_value_lemma h0 h1 h2 a b ctr c tmp; 
  cut (maxValue h2 c (length c) <= (ctr+1) * pow2 53); 
  standardized_lemma h0 h1 h2 a c tmp; 
  standardized_lemma2 h0 h1 h2 b c tmp

val multiplication_step_p1: a:bigint -> b:bigint -> ctr:nat{ctr<norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  ST unit 
     (requires (fun h -> (bound h a) /\ (norm h b) /\ (live h c) /\ (live h tmp)
        /\ (maxValue h c (length c) <= ctr * pow2 53)
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr) ))
     (ensures (fun h0 u h1 -> (bound h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h0 tmp)       
       /\ (bound h1 a) /\ (norm h1 b) /\ (live h1 c) /\ (live h1 tmp) /\ (modifies_buf (only c ++ tmp) h0 h1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ (maxValue h1 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b ctr)
       /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)) ))
let multiplication_step_p1 a b ctr c tmp =
  let h0 = ST.get() in
  multiplication_step_0 a b ctr c tmp; 
  let h1 = ST.get() in
  multiplication_step_lemma_001 h0 h1 a b ctr c tmp; 
  fsum_index c ctr tmp 0 norm_length 0; 
  let h2 = ST.get() in 
  multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp;
  ()
  
val helper_lemma_6: h0:heap -> h1:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c /\ length c >= 2 * norm_length - 1} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
     (requires (bound h0 a /\ norm h0 b /\ live h0 c))
    (ensures (bound h0 a /\ norm h0 b /\ live h0 c
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a (norm_length) * v (get h0 b ctr)  = eval h0 a (norm_length) * v (get h0 b ctr) * pow2 (bitweight templ ctr) + eval h0 c (2*norm_length-1) ))
let helper_lemma_6 h0 h1 a b ctr c tmp = 
  ()

val multiplication_step: a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> ST unit  
     (requires (fun h -> bound h a /\ norm h b /\ live h c /\ live h tmp
	/\ maxValue h c (length c) <= ctr * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b ctr  ))
     (ensures (fun h0 u h1 -> bound h0 a /\ bound h1 a /\ norm h0 b /\ norm h1 b
       /\ live h0 c /\ live h1 c  /\ live h0 tmp /\ live h1 tmp /\ modifies_buf (only c ++ tmp) h0 h1
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
  
val multiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{norm h0 a} -> 
  b:bigint{norm h0 b} -> ctr:pos{ctr<=norm_length} -> 
  c:bigint_wide{live h1 c /\ length c >= 2*norm_length-1} -> Lemma 
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1))) 
let multiplication_step_lemma_03 h0 h1 a b ctr c = 
  let t = templ in 
  paren_mul_left (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * v (get h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ) ; 
  distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr)); 
  cut (True /\ eval h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr)))

val helper_lemma_12: a:nat -> v:nat -> p:nat -> b:nat -> Lemma (a * v * p + (a * b) = a * (p * v + b))
let helper_lemma_12 a v p b = 
  ()

val multiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} ->  c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (bound h0 a /\ bound h1 a /\ norm h0 b /\ norm h1 b 
       /\ live h0 c /\ live h1 c /\ live h0 tmp /\ live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ modifies_buf (only c ++ tmp) h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (bound h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp =
  eq_lemma h0 h1 a (only c ++ tmp);
  eq_lemma h0 h1 b (only c ++ tmp);
  eval_eq_lemma h0 h1 a a norm_length;
  eval_eq_lemma h0 h1 b b norm_length;
  eval_eq_lemma h0 h1 b b (norm_length - ctr);
  eval_eq_lemma h0 h1 b b (norm_length - ctr + 1);
  cut((norm_length - ctr)+1 = norm_length - ctr + 1 /\ True); 
  cut(eval h0 a norm_length = eval h1 a norm_length /\ eval h0 b (norm_length-ctr) = eval h1 b (norm_length - ctr) /\ eval h0 b (norm_length - ctr + 1) = eval h1 b (norm_length - ctr + 1) /\ v (get h0 b (norm_length - ctr)) = v (get h1 b (norm_length - ctr))); 
  helper_lemma_12 (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight templ (norm_length - ctr))) (eval h0 b (norm_length - ctr))

val multiplication_aux_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr <= norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
    (requires (bound h0 a /\ norm h0 b /\ live h1 c /\ live h1 tmp
       /\ bound h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp
       /\ bound h2 a /\ norm h2 b /\ live h2 c /\ live h2 tmp
       /\ modifies_buf (only c ++ tmp) h1 h2 /\ modifies_buf (only c ++ tmp) h0 h1
       /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length) ))
    (ensures (bound h0 a /\ norm h0 b /\ live h1 c /\ bound h2 a /\ norm h2 b /\ live h2 c
       /\ modifies_buf (only c ++ tmp) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
  eq_lemma h0 h1 a (only c ++ tmp);
  eq_lemma h0 h1 b (only c ++ tmp);
  eval_eq_lemma h0 h1 a a norm_length; 
  eval_eq_lemma h0 h1 b b norm_length

val multiplication_aux: a:bigint -> b:bigint -> ctr:nat{ctr<=norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> ST unit
     (requires (fun h -> bound h a /\ norm h b /\ live h c /\ live h tmp
	/\ maxValue h c (length c) <= (norm_length - ctr) * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - ctr) ))
     (ensures (fun h0 u h1 -> bound h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp
       /\ bound h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp /\ modifies_buf (only c ++ tmp) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let rec multiplication_aux a b ctr c tmp = 
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

val helper_lemma_13: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (bound h0 a /\ modifies_buf empty h0 h1))
    (ensures (bound h0 a /\ bound h1 a /\ live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a =  
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

val helper_lemma_131: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (norm h0 a /\ modifies_buf empty h0 h1))
    (ensures (norm h0 a /\ norm h1 a /\ live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_131 h0 h1 a =  
  eq_lemma h0 h1 a empty;   eval_eq_lemma h0 h1 a a norm_length

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> Lemma 
    (requires (live h0 c /\ null h0 c /\ modifies_buf empty h0 h1))
    (ensures (live h1 c /\ null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  eq_lemma h0 h1 c empty;
  eval_null h1 c (2*norm_length - 1); 
  max_value_of_null_lemma h1 c (length c)

val multiplication_lemma_1: h0:heap -> h1:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> 
  a:bigint{disjoint c a} ->  b:bigint{disjoint c b} -> Lemma 
     (requires (bound h0 a /\ norm h0 b /\ live h0 c /\ null h0 c /\ modifies_buf empty h0 h1))
     (ensures (bound h1 a /\ norm h1 b /\ live h1 c /\ null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) ))
let multiplication_lemma_1 h0 h1 c a b =
  helper_lemma_13 h0 h1 a;
  helper_lemma_131 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(True /\ eval h1 b 0 = 0)

val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide -> tmp:bigint_wide{disjoint c tmp} ->
  Lemma
    (requires (live h0 c /\ live h2 c /\ not(contains h0 tmp) /\ modifies_buf empty h0 h1 /\ live h1 tmp /\ modifies_buf (only c ++ tmp) h1 h2))
    (ensures (modifies_buf (only c) h0 h2))
let helper_lemma_14 h0 h1 h2 c tmp =
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.live h0 #t b)} 
	 SBuffer.live h0 #t b ==> disjointSet b (only tmp)); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (SBuffer.live h0 #t b)}
	 (SBuffer.live h0 #t b /\ disjointSet b (only c ++ tmp)) <==> (SBuffer.live h0 #t b /\ disjointSet b (only c))); 
  cut (modifies_buf (only c ++ tmp) h0 h2); 
  cut (forall (#t:pos) (b:buffer t). (SBuffer.live h0 b /\ disjointSet b (only c ++ tmp)) ==> equal h0 b h2 b); 
  cut (forall (#t:pos) (b:buffer t). {:pattern (disjointSet b (only c))}
				  (SBuffer.live h0 b /\ disjointSet b (only c)) ==> equal h0 b h2 b)

val multiplication_lemma_2: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide{length c >= 2*norm_length-1} -> 
  a:bigint{disjoint c a} -> b:bigint{disjoint c b} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
     (requires (bound h0 a /\ norm h0 b /\ live h0 c /\ null h0 c
	/\ modifies_buf empty h0 h1 /\ not(contains h0 tmp) /\ live h1 tmp
	/\ bound h1 a /\ norm h1 b /\ live h1 c /\ null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)
        /\ bound h2 a /\ norm h2 b /\ live h2 c
        /\ modifies_buf (only c ++ tmp) h1 h2
        /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length)
        /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
     (ensures (bound h0 a /\ norm h0 b /\ live h0 c /\ bound h2 a /\ norm h2 b /\ live h2 c
       /\ modifies_buf (only c) h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
  helper_lemma_14 h0 h1 h2 c tmp; 
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

(* Code : core multiplication function *)
val multiplication: c:bigint_wide{length c >= 2*norm_length-1} -> a:bigint{disjoint c a} -> 
  b:bigint{disjoint c b} -> ST unit
     (requires (fun h -> bound h a /\ norm h b /\ live h c /\ null h c))
     (ensures (fun h0 u h1 -> bound h0 a /\ norm h0 b /\ live h0 c /\ bound h1 a /\ norm h1 b /\ live h1 c
       /\ modifies_buf (only c) h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let multiplication c a b =
  let h0 = ST.get() in
  let tmp = create #128 zero_wide norm_length in // Hardcoding size
  let h1 = ST.get() in
  multiplication_lemma_1 h0 h1 c a b; 
  multiplication_aux a b norm_length c tmp; 
  let h2 = ST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp;
  ()
