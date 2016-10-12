module Curve.Fproduct

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt128
open FStar.Buffer
open Math.Lib
open Curve.Parameters
open Curve.Bigint

#set-options "--lax"

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

let w: u32 -> Tot int = U32.v
let vv: u64 -> Tot int = U64.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

(* Lemma : additivity property of the "bitweight" function if the template is normalized *)
val bitweight_lemma_1: t:template{forall (n:nat). t n = t 0} -> i:nat -> Lemma (bitweight t i = i * (t 0))
let rec bitweight_lemma_1 t i = 
  admit(); // OK
  match i with
  | 0 -> ()
  | _ -> 
    (* FproductLemmas.auxiliary_lemma_2 i; *)
    assert(t (i-1) = t 0); 
    assert(bitweight t i = t 0 + bitweight t (i-1));
    bitweight_lemma_1 t (i-1)
    (* FproductLemmas.auxiliary_lemma_3 (t 0) i *)

val bitweight_lemma_0: t:template{ forall (n:nat). t n = t 0 } -> i:nat -> j:nat -> 
  Lemma ( bitweight t (i+j) = bitweight t i + bitweight t j)
let rec bitweight_lemma_0 t i j =
  admit(); // OK
  bitweight_lemma_1 t (i+j); 
  bitweight_lemma_1 t i; bitweight_lemma_1 t j
  (* FproductLemmas.auxiliary_lemma_4 (t 0) i j *)

(* Lemma : combines the additivity property of the bitweight function and the exponential property 
   of the pow2 function *)
val auxiliary_lemma_1: 
  t:template{ forall (n:nat). t n = t 0 } -> a:nat -> b:nat -> 
  Lemma (ensures (pow2 (bitweight t (a+b)) = pow2 (bitweight t a) * pow2 (bitweight t b)))
let auxiliary_lemma_1 t a b =
  admit(); // OK
  bitweight_lemma_0 t a b;
  Math.Lemmas.pow2_plus (bitweight t a) (bitweight t b)

abstract type partialEquality (ha:heap) (a:bigint_wide{live ha a})
			    (hb:heap) (b:bigint_wide{live hb b}) 
			    (len:nat{len <= length a /\ len <= length b}) =
  (forall (i:nat). {:pattern (v (get ha a i))}
    i < len ==> v (get ha a i) = v (get hb b i))

abstract type storesSum (hc:heap) (c:bigint_wide{live hc c})
		      (ha:heap) (a:bigint_wide{live ha a})
		      (hb:heap) (b:bigint_wide{live hb b})
		      (a_idx:nat)
		      (len:nat{a_idx+len <= length a /\ len <= length b /\ a_idx+len <= length c}) =
 (forall (i:nat). {:pattern (v (get hc c (i+a_idx)))}
   (i < len ==> v (get hc c (i+a_idx)) = v (get ha a (i+a_idx)) + v (get hb b i)))
			      
val multiplication_step_lemma_1: h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> 
  b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} ->
  idx:nat -> len:pos{len+idx <= length a /\ len <= length b /\ length a = length c } -> Lemma
    (requires (
      storesSum h1 c h0 a h0 b idx len
      /\ partialEquality h1 c h0 a idx
      /\ eval_wide h1 c (len-1+idx) = eval_wide h0 a (len-1+idx) + pow2 (bitweight (templ) idx) * eval_wide h0 b (len-1)))
    (ensures (eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) +  
		          pow2 (bitweight (templ) idx) * eval_wide h0 b (len-1)  +	        
			  pow2 (bitweight (templ) (len-1+idx)) * v (get h0 b (len-1))))
let multiplication_step_lemma_1 h0 h1 a b c idx len = ()
  (* admit(); // OK *)
  (* let t = templ in *)
  (* (\* FproductLemmas.auxiliary_lemma_0 len idx 1;  *\) *)
  (* eval_wide_def h1 c (len+idx);  *)
  (* (\* FproductLemmas.auxiliary_lemma_00 len idx 1;    *\) *)
  (* cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1)) /\ True);  *)
  (* cut (True /\ eval h1 c (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)) + eval h1 c (len+idx-1));  *)
  (* cut (eval h1 c (len+idx) = eval h1 c (len+idx-1) + pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)) /\ True ); *)
  (* cut (eval h1 c (len+idx-1) = eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1) /\ True);  *)
  (* cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1)) /\ True);  *)
  (* cut (eval h1 c (len+idx) =  *)
  (* 	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)) *)
  (* 	+ pow2 (bitweight t (len-1+idx)) * (v (get h0 a (len+idx-1)) + v (get h0 b (len-1))) /\ True);  *)
  (* Math.Lemmas.distributivity_add_right (pow2 (bitweight t (len-1+idx))) (v (get h0 a (len+idx-1))) (v (get h0 b (len-1)));  *)
  (* cut (True /\ eval h1 c (len+idx) =  *)
  (* 	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)) *)
  (* 	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) *)
  (*       + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))));  *)
  (* (\* FproductLemmas.remove_paren_lemma (eval h0 a (len+idx-1)) ((pow2 (bitweight t idx)) * eval h0 b (len-1)) ((pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))));  *\) *)
  (* cut (True /\ eval h1 c (len+idx) =  *)
  (* 	eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1) *)
  (* 	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) *)
  (*       + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)))); *)
  (* (\* FproductLemmas.remove_paren_lemma (eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))  *\) *)
  (* (\* 		     (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1))) *\) *)
  (* (\* 		     (pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)));  *\) *)
  (* cut (True /\ eval h1 c (len+idx) =  *)
  (* 	eval h0 a (len+idx-1) + pow2 (bitweight t idx) * eval h0 b (len-1)  + *)
  (* 	pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) +    	         *)
  (*         pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)));  *)
  (* (\* FproductLemmas.auxiliary_lemma_6 (eval h0 a (len+idx-1))  *\) *)
  (* (\* 				  (pow2 (bitweight t idx) * eval h0 b (len-1)) *\) *)
  (* (\* 				  (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)))     *\) *)
  (* (\* 				  (pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))); *\) *)
  (* cut (True /\ eval h1 c (len+idx) =  *)
  (* 	pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1) +  *)
  (*         pow2 (bitweight t idx) * eval h0 b (len-1)  +	         *)
  (*         pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)));  *)
  (* eval_wide_def h0 a (len+idx); *)
  (* cut (True /\ eval h0 a (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1));  *)
  (* cut (True /\ eval h1 c (len+idx) =  *)
  (* 		eval h0 a (len+idx)  *)
  (* 		+ pow2 (bitweight t idx) * eval h0 b (len-1)   *)
  (* 		+ pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))) *)

(* #reset-options *)

(* Lemma : second half of the helper for the multiplication_step_lemma *)
val multiplication_step_lemma_2: h0:heap -> h1:heap -> a:bigint_wide{live h0 a } -> 
  b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma 
    (requires (
	 eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) +  
                          pow2 (bitweight (templ) idx) * eval_wide h0 b (len-1)  +	        
			  pow2 (bitweight (templ) (len-1+idx)) * v (get h0 b (len-1))
    ))
    (ensures (eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) + pow2 (bitweight (templ) idx) * eval_wide h0 b len))
let multiplication_step_lemma_2 h0 h1 a b c idx len = 
  admit(); // OK
  (* FproductLemmas.auxiliary_lemma_0 len idx 1; *)
  auxiliary_lemma_1 (templ) idx (len-1); 
  (* FproductLemmas.auxiliary_lemma_00 len (-1) idx; *)
  (* FproductLemmas.auxiliary_lemma_01 (len-1) idx;  *)
  cut (True /\ pow2 (bitweight (templ) (len-1+idx)) = pow2 (bitweight (templ) idx) * pow2 (bitweight (templ) (len-1)) ); 
  Math.Lemmas.paren_mul_left (pow2 (bitweight (templ) idx)) (pow2 (bitweight (templ) (len-1))) (v (get h0 b (len-1)));
  cut (eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) 
			     + pow2 (bitweight (templ) idx) * eval_wide h0 b (len-1)
			     + pow2 (bitweight (templ) idx) * pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1)) /\ True); 
  Math.Lemmas.distributivity_add_right (pow2 (bitweight (templ) idx)) (eval_wide h0 b (len-1)) (pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1)));
  eval_wide_def h0 b len; 
  cut (True /\ eval_wide h0 b len = eval_wide h0 b (len-1) + (pow2 (bitweight (templ) (len-1))) * v (get h0 b (len-1)) );  
  cut (True /\ pow2 (bitweight (templ) (len-1+idx)) * v (get h0 b (len-1)) =
        pow2 (bitweight (templ) idx) * pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))); 
  cut ( True /\ eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) + pow2 (bitweight (templ) idx) * eval_wide h0 b len) 

(* #reset-options *)

(* Lemma : changes the result of the addition function into the equivalent relation between 
  evaluated bigints *)
val multiplication_step_lemma: h0:heap -> h1:heap -> a:bigint_wide{live h0 a } -> 
  b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c} -> idx:nat ->
  len:nat{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires (storesSum h1 c h0 a h0 b idx len /\ partialEquality h1 c h0 a idx))
    (ensures (eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx) + pow2 (bitweight (templ) idx) * eval_wide h0 b len
    ))
let rec multiplication_step_lemma h0 h1 a b c idx len =
  admit(); // OK
  match len with
  | 0 ->
    cut (forall (i:nat). i < idx ==> v (get h1 c i) = v (get h0 a i)); 
    (* eval_eq_lemma h0 h1 a c idx;  *)
    (* FproductLemmas.auxiliary_lemma_02 len idx; *)
    cut (True /\ len+idx = idx); 
    cut (True /\ eval_wide h0 b len = 0);
    (* FproductLemmas.auxiliary_lemma_03 (pow2 (bitweight (templ) idx)); *)
    cut (True /\ pow2 (bitweight (templ) idx) * 0 = 0);
    cut (True /\ eval_wide h1 c (len+idx) = eval_wide h0 a (len+idx))
  | _ ->   
     (* FproductLemmas.auxiliary_lemma_0 len idx 1;  *)
     (* FproductLemmas.auxiliary_lemma_2 len; *)
     multiplication_step_lemma h0 h1 a b c idx (len-1); 
     multiplication_step_lemma_1 h0 h1 a b c idx len; 
     multiplication_step_lemma_2 h0 h1 a b c idx len

(* #reset-options *)

let (max_limb:nat) = parameters_lemma_1 (); (platform_wide - log_2 norm_length - 1) / 2
let (max_wide:nat) = 2 * max_limb

abstract type fitsMaxLimbSize (h:heap) (a:bigint{live h a}) =
  (forall (i:nat). {:pattern (U64.v (get h a i))} i < norm_length ==> U64.v (get h a i) < pow2 max_limb)
  
(* Lemma *)
val auxiliary_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint{live h0 a /\ fitsMaxLimbSize h0 a } ->
  b:bigint{live h1 b /\ (forall (i:nat). i < norm_length ==> U64.v (get h1 b i) < pow2 max_limb)} ->
  ctr:nat{(ctr <= norm_length)} -> c:bigint{live h2 c /\ maxValue h2 c (length c) <= ctr * (maxValueNorm h0 a * maxValueNorm h1 b)} -> Lemma ((maxValueNorm h0 a <= pow2 max_limb) /\ (maxValueNorm h1 b <= pow2 max_limb))
let auxiliary_lemma_2 h0 h1 h2 a b ctr c = 
  admit(); // OK
  ()

(* #reset-options *)

(* Lemma : bounds the maxValues product *)
val auxiliary_lemma_3: h0:heap -> h1:heap -> h2:heap -> a:bigint{live h0 a /\ maxValueNorm h0 a <= pow2 max_limb} -> b:bigint{live h1 b /\ maxValueNorm h1 b <= pow2 max_limb} -> ctr:nat{ctr <= norm_length} ->
  c:bigint_wide{live h2 c /\ maxValue_wide h2 c (length c) <= ctr * (maxValueNorm h0 a * maxValueNorm h1 b)} ->
  Lemma (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 max_wide)
let auxiliary_lemma_3 h0 h1 h2 a b ctr c =
  admit(); // OK
  let s = max_wide in
  Math.Axioms.slash_star_axiom max_limb 2 max_wide;
  cut (max_limb = s / 2 /\ True); 
  (* FproductLemmas.helper_lemma_3 (maxValueNorm h0 a) (maxValueNorm h1 b) (pow2 max_limb) (pow2 max_limb); *)
  Math.Lemmas.pow2_plus (s/2) (s/2); 
  cut (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 ((s/2)+(s/2)) /\ True); 
  (* FproductLemmas.helper_lemma_2 (s/2); *)
  Math.Lemmas.multiply_fractions s 2; 
  cut ((s / 2)+(s/2) <= (s) /\ True);
  if (((s/2)+(s/2)) < s ) then
	Math.Lemmas.pow2_lt_compat s ((s/2)+(s/2));
  cut (pow2 (((s/2)+(s/2))) <= pow2 s /\ True); 
  cut (maxValueNorm h0 a * maxValueNorm h1 b <= pow2 s /\ True)

(* #reset-options *)

abstract type partialEquality2 (ha:heap) (a:bigint_wide{live ha a})
			       (hb:heap) (b:bigint_wide{live hb b}) 
			       (len:nat)
			       (len2:nat{len2 >= len /\ len2 <= length a /\ len2 <= length b}) =
  (forall (i:nat). {:pattern (v (get ha a i))}
    (i < len2 /\ i >= len) ==> v (get ha a i) = v (get hb b i))

(* Lemma : extends the "eval" property to the total length if apporpriate *)
val auxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint_wide{live h0 a } -> b:bigint_wide{live h1 b} ->
  c:int -> len:nat -> len2:nat{ len2 >= len /\ len2 <= length b /\ len2 <= length a } -> Lemma 
    (requires ( (eval_wide h1 b len = eval_wide h0 a len + c)
		/\ partialEquality2 h1 b h0 a len len2))
    (ensures ( (eval_wide h1 b len2 = eval_wide h0 a len2 + c)))
let rec auxiliary_lemma_5 h0 h1 a b c len len2 =
  admit(); // OK
  match len2 - len with
  | 0 -> ()
     (* FproductLemmas.auxiliary_lemma_8 len2 len *)
  | _ ->
     let t = templ in
     (* FproductLemmas.auxiliary_lemma_7 len2 len; *)
     auxiliary_lemma_5 h0 h1 a b c len (len2-1); 
     cut (True /\ eval_wide h1 b (len2-1) = eval_wide h0 a (len2-1) + c); 
     eval_wide_def h1 b len2; 
     cut (True /\ eval_wide h1 b len2 = eval_wide h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * v (get h1 b (len2-1))); 
     cut (v (get h1 b (len2-1)) = v (get h0 a (len2-1)) /\ True); 
     cut (True /\ eval_wide h1 b len2 = (eval_wide h0 a (len2-1) + c) + (pow2 (bitweight t (len2-1))) * v (get h0 a (len2-1))); 
     (* FproductLemmas.auxiliary_lemma_04 (eval_wide h0 a (len2-1)) c ((pow2 (bitweight t (len2-1))) * v (get h0 a (len2-1)));   *)
     eval_wide_def h0 a len2;
     cut (True /\ eval_wide h1 b len2 = eval_wide h0 a len2 + c)

(* #reset-options *)

abstract type isScalarProduct 
  (hc:heap) (c:bigint_wide{live hc c /\ length c >= norm_length})
  (ha:heap) (a:bigint{live ha a /\ length a >= norm_length}) (s:u64) =
    (forall (i:nat). {:pattern (v (get hc c i))}
      (i<norm_length) ==> v (get hc c i) = U64.v (get ha a i) * U64.v s)  
  
val max_limb_lemma: a:nat -> b:nat -> 
  Lemma
    (requires (a < pow2 max_limb /\ b < pow2 max_limb))
    (ensures (a * b < pow2 platform_wide))
    [SMTPat (a * b)]
let max_limb_lemma a b =
  (* FproductLemmas.ineq_lemma_3 a b (pow2 max_limb); *)
  Math.Lemmas.pow2_plus max_limb max_limb;
  (* FproductLemmas.helper_lemma_10 max_limb;   *)
  Curve.Parameters.parameters_lemma_1 (); 
  (* FproductLemmas.helper_lemma_11 platform_wide (log_2 norm_length) max_limb;  *)
  Math.Lemmas.pow2_lt_compat platform_wide max_wide

val max_limb_lemma2: h:heap -> a:bigint{live h a} -> b:bigint{live h b} -> i:nat{i < length a} -> ctr:nat{ctr < length b} -> Lemma
    (requires (U64.v (get h a i) < pow2 max_limb /\ U64.v (get h b ctr) < pow2 max_limb))
    (ensures (U64.v (get h a i) * U64.v (get h b ctr) < pow2 platform_wide))
let max_limb_lemma2 h a b i ctr =
  max_limb_lemma (U64.v (get h a i)) (U64.v (get h b ctr))

(* #reset-options *)

val is_scalar_product_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a /\ length a >= norm_length} -> s:u64 -> res:bigint_wide{live h1 res /\ length res >= norm_length} ->
  Lemma
    (requires (Curve.Fscalar.isScalarProduct h0 h1 0 norm_length a s res))
    (ensures (isScalarProduct h1 res h0 a s))
let is_scalar_product_lemma h0 h1 a s res = ()

val multiplication_step_0: a:bigint -> b:bigint -> ctr:u32{w ctr<norm_length/\w ctr<2*norm_length-1} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit 
     (requires (fun h -> norm h a /\ norm h b /\ live h c /\ live h tmp
        /\ length c >= 2*norm_length -1
	/\ maxValueNorm h a < pow2 max_limb
	/\ maxValueNorm h b < pow2 max_limb
	/\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b
       ))
     (ensures (fun h0 _ h1 ->
       norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp
       /\ live h0 tmp /\ length tmp = length tmp
       /\ length c >= 2*norm_length-1 /\ length tmp >= norm_length
       /\ modifies_1 tmp h0 h1
       /\ isScalarProduct h1 tmp h0 a (get h0 b (w ctr))
       /\ eval_wide h1 tmp norm_length = eval h0 a norm_length * vv (get h0 b (w ctr)) ))
let multiplication_step_0 a b ctr c tmp = 
  admit(); // OK
  let h0 = HST.get() in
  let s = index b ctr in 
  assert(forall (n:nat). {:pattern (vv (get h0 b n))} n < norm_length ==> vv (get h0 b n) <= pow2 max_limb); 
  assert(forall (n:nat). n = w ctr ==> n < norm_length); 
  assert(True /\ vv s < pow2 max_limb); 
  assert(forall (i:nat). {:pattern (vv  (get h0 a i))} 
	   i < norm_length ==> vv (get h0 a i) < pow2 max_limb);
  assert(vv s < pow2 max_limb); 
  cut(forall (i:nat). (i < norm_length) ==> vv (get h0 a i) * vv s < pow2 platform_wide); 
  Curve.Fscalar.scalar_multiplication_tr tmp a s 0ul; 
  let h1 = HST.get() in
  cut(True /\ vv s = vv (get h0 b (w ctr))); 
  assert(Fscalar.isScalarProduct h0 h1 0 norm_length a s tmp); 
  is_scalar_product_lemma h0 h1 a s tmp;
  Curve.Fscalar.theorem_scalar_multiplication h0 h1 a s norm_length tmp

#reset-options

val std_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint_wide{disjoint a tmp} ->Lemma
    (requires (norm h0 a /\ live h1 tmp /\ modifies_1 tmp h0 h1))
    (ensures (norm h1 a))
let std_lemma h0 h1 a tmp = 
  admit(); // OK
  (* no_upd_lemma h0 h1 a (only tmp);  *)
  cut(forall (i:nat). {:pattern (vv (get h1 a i))} i < norm_length ==> vv (get h1 a i) = vv (get h0 a i)); 
  cut(True /\ live h1 a); cut(True /\ length a >= norm_length); cut (True /\ templ = templ); 
  cut(forall (i:nat). {:pattern (norm h1 a)} i < norm_length ==> vv (get h1 a i) < pow2 (templ i)); 
  cut(norm h1 a)
 
assume val max_wide_lemma:
  x:nat{x <= norm_length} -> Lemma (x * pow2 max_wide < pow2 platform_wide)

#reset-options

val lemma_helper_00: unit -> Lemma (forall (a:nat) (b:nat) (c:nat) (d:nat). (a <= b /\ c <= d) ==> a * c <= b * d)
let lemma_helper_00 () = 
  admit(); // OK
  ()

val lemma_helper_01: a:int -> b:int -> c:int -> Lemma (a * (b+c) + b + c = (a+1) * (b+c))
let lemma_helper_01 a b c = 
  admit(); // OK
  ()

val lemma_helper_02: a:nat -> b:nat -> c:nat -> Lemma (requires (b <= c)) (ensures (a*b <= a*c))
let lemma_helper_02 a b c = 
  admit(); // OK
  ()

val multiplication_step_lemma_0010:  h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
     (requires (
       norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp
       /\ length c >= 2*norm_length -1
       /\ maxValueNorm h0 a < pow2 max_limb /\ maxValueNorm h0 b < pow2 max_limb
       /\ maxValue_wide h0 c (length c) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b
       /\ modifies_1 tmp h0 h1
       /\ isScalarProduct h1 tmp h0 a (get h0 b ctr) ))
     (ensures (live h1 tmp /\ norm h0 a /\ norm h0 b
       /\ length tmp >= norm_length
       /\ (forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) <= maxValueNorm h0 a * maxValueNorm h0 b) ))
let multiplication_step_lemma_0010 h0 h1 a b ctr c tmp = 
  admit(); // OK
  lemma_helper_00 ()

val multiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> 
  Lemma
     (requires (
       norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp
       /\ (length c >= 2*norm_length -1)
       /\ (maxValueNorm h0 a < pow2 max_limb) /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (maxValue_wide h0 c (length c)  <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
       /\ modifies_1 tmp h0 h1
       /\ isScalarProduct h1 tmp h0 a (get h0 b ctr) ))
     (ensures (live h1 c /\ live h1 tmp /\ ctr+norm_length <= length c
       /\ Curve.FsumWide.willNotOverflow h1 ctr 0 norm_length 0 c tmp ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp =
  admit(); // OK
  multiplication_step_lemma_0010 h0 h1 a b ctr c tmp;
  Math.Lemmas.distributivity_add_left ctr 1 (maxValueNorm h0 a * maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (v (get h1 c i))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b);
  cut (True /\ ctr * maxValueNorm h0 a * maxValueNorm h0 b + maxValueNorm h0 a * maxValueNorm h0 b
    = (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) );
  cut (forall (i:nat). {:pattern (v (get h1 c (i+ctr)) + v (get h1 tmp i))} i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b));
  auxiliary_lemma_3 h0 h0 h1 a b ctr c;
  assert ((maxValueNorm h0 a * maxValueNorm h0 b) <= pow2 max_wide);
  lemma_helper_02 (ctr+1) (maxValueNorm h0 a * maxValueNorm h0 b) (pow2 max_wide);
  cut(True /\ (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) <= (ctr + 1) * pow2 max_wide);
  max_wide_lemma (ctr+1); 
  assert((ctr+1) * pow2 max_wide < pow2 platform_wide);
  (* FproductLemmas.helper_lemma_4 (maxValueNorm h0 a) (maxValueNorm h0 b); *)
  (* FproductLemmas.helper_lemma_4 (ctr+1) (maxValueNorm h0 a * maxValueNorm h0 b); *)
  (* FproductLemmas.helper_lemma_4 (ctr+1) (pow2 max_wide); *)
  (* FproductLemmas.ineq_lemma_2 ((ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)) ((ctr+1) * pow2 max_wide) (pow2 platform_wide); *)
  assert ((ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) < pow2 platform_wide);
  assert(forall (i:nat). i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b) ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) < pow2 platform_wide); 
  cut(forall (i:nat). i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) < pow2 platform_wide); 
  assert(FsumWide.willNotOverflow h1 ctr 0 norm_length 0 c tmp)

val multiplication_step_lemma_01: h0:heap -> h1:heap -> a:bigint -> b:bigint ->
  ctr:nat{ctr<norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->
  Lemma
     (requires (norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp
        /\ (length c >= 2*norm_length -1)
	/\ (maxValueNorm h0 a < pow2 max_limb) /\ (maxValueNorm h0 b < pow2 max_limb)
	/\ (maxValue_wide h0 c (length c) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
	/\ modifies_1 tmp h0 h1
	/\ isScalarProduct h1 tmp h0 a (get h0 b ctr) ))
     (ensures (
       (live h1 c) /\ (live h1 tmp) /\ (ctr+norm_length <= length c) 
       /\ (norm h1 a) /\ (norm h1 b)
       /\ (0+norm_length <= length tmp)
       /\ FsumWide.willNotOverflow h1 ctr 0 norm_length 0 c tmp
     ))
let multiplication_step_lemma_01 h0 h1 a b ctr c tmp =
  admit(); // OK
  (* no_upd_lemma h0 h1 c (only tmp);  *)
  cut(True /\ length c >= ctr + norm_length); 
  std_lemma h0 h1 a tmp;
  std_lemma h0 h1 b tmp; 
  multiplication_step_lemma_001 h0 h1 a b ctr c tmp

val partial_equality_lemma: h0:heap -> h1:heap -> c:bigint_wide{live h0 c /\ live h1 c /\ length c = length c} -> ctr:nat{ ctr + norm_length <= length c} ->
  Lemma
    (requires (FsumWide.isNotModified h0 h1 ctr norm_length 0 c))
    (ensures (partialEquality h1 c h0 c ctr))
let partial_equality_lemma h0 h1 c ctr = 
  admit(); // OK
  ()

val lemma_helper_10: a:nat -> b:nat -> c:nat -> Lemma (a <= a + (b * c))
let lemma_helper_10 a b c = 
  admit(); // OK
  ()

#reset-options

val max_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (
      norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c
      /\ length c >= 2 * norm_length - 1
      /\ modifies_1 tmp h0 h1
      /\ maxValue_wide h0 c (length c) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))} 
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (vv (get h0 a i) * vv (get h0 b ctr)))
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i))
    ))
    (ensures ( norm h0 a /\ norm h0 b /\ live h2 c
       /\ (maxValue_wide h2 c (length c) <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b)))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =
  admit(); // OK
  cut(forall (i:nat). {:pattern (vv (get h0 a i))} 
    i < norm_length ==> vv (get h0 a i) <= maxValueNorm h0 a);
  cut(forall (i:nat). {:pattern (vv (get h0 b i))} 
	   i < norm_length ==> vv (get h0 b i) <= maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (v (get h0 c i))} i < length c ==> v (get h0 c i) <= maxValue_wide h0 c (length c));
  cut(forall (i:nat). {:pattern (v (get h0 c (i+ctr)))} 
	   i < norm_length ==> v (get h0 c (i+ctr)) <= maxValue_wide h0 c (length c));
  (* FproductLemmas.ineq_lemma (); *)
  assert(forall (a:nat) (b':nat) (c:nat) (d:nat). {:pattern (vv (get h0 b ctr))} a <= c /\ b' <= d ==> a * b' <= c * d);
  assert(vv (get h0 b ctr) <= maxValueNorm h0 b);
  cut(forall (i:nat). {:pattern (vv (get h0 a i) * vv (get h0 b ctr))} i < norm_length ==>
    (vv (get h0 a i)) <= maxValueNorm h0 a /\ vv (get h0 b ctr) <= maxValueNorm h0 b); 
  cut(forall (i:nat). {:pattern (vv (get h0 a i) * vv (get h0 b ctr))} i < norm_length ==>
    (vv (get h0 a i) * vv (get h0 b ctr)) <= maxValueNorm h0 a * maxValueNorm h0 b);
  assert(forall (a':nat) (b':nat) (c':nat) (d:nat). {:pattern (maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b))} a' <= c' /\ b' <= d ==> a' + b' <= c' + d); 
  cut(forall (i:nat). {:pattern (v (get h0 c (i+ctr)) + (vv (get h0 a i) * vv (get h0 b ctr)))} i < norm_length ==> v (get h0 c (i+ctr)) + (vv (get h0 a i) * vv (get h0 b ctr)) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). i < norm_length ==> v (get h2 c (i+ctr)) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). {:pattern (i < length c)} i < length c ==>
	   ((i >= ctr /\ i < norm_length+ctr) \/ ((i < ctr \/ i >= norm_length + ctr) /\ i < length c))); 
  cut(forall (i:nat). (i>=ctr /\ i<norm_length+ctr) ==> (i-ctr>=0 /\ i-ctr < norm_length /\ ((i-ctr)+ctr) = i)); 
  cut(forall (i:nat). {:pattern (i >= ctr /\ i < norm_length+ctr)} (i >= ctr /\ i < norm_length+ctr) ==> v (get h2 c i) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b));
  assert(forall (i:nat). {:pattern ((i < ctr \/ i >= norm_length + ctr) /\ i < length c)} 
    ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) <= maxValue_wide h0 c (length c)); 
    lemma_helper_10 (maxValue_wide h0 c (length c)) (maxValueNorm h0 a) (maxValueNorm h0 b); 
  cut(True /\ maxValue_wide h0 c (length c) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat).  ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) <= maxValue_wide h0 c (length c)); 
  assert(forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  cut(forall (i:nat). {:pattern(maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b))}
    i < length c ==> 
      ((i >= ctr /\ i < norm_length+ctr) \/ ((i < ctr \/ i >= norm_length + ctr) /\ i < length c)) ==>
	v (get h2 c i) <= maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b)); 
  Math.Lemmas.paren_mul_right ctr (maxValueNorm h0 a) (maxValueNorm h0 b);
  cut(True /\ maxValue_wide h0 c (length c) <= ctr * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  (* FproductLemmas.factorise_lemma (maxValueNorm h0 a * maxValueNorm h0 b) ctr; *)
  assert(True /\ maxValue_wide h0 c (length c) + (maxValueNorm h0 a * maxValueNorm h0 b) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(forall (i:nat). 
    i < length c ==> 
	v (get h2 c i) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)); 
  assert(maxValue_wide h2 c (length c) <= (ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b))

val max_value_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->
  Lemma
    (requires (
      norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c
      /\ modifies_1 tmp h0 h1
      /\ length c >= 2 * norm_length - 1
      /\ (maxValue_wide h0 c (length c) <= ctr * maxValueNorm h0 a * maxValueNorm h0 b)
      /\ isScalarProduct h1 tmp h0 a (get h0 b ctr)
      /\ FsumWide.isSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ FsumWide.isNotModified h1 h2 ctr norm_length 0 c))
    (ensures (norm h0 a /\ norm h0 b /\ live h2 c
       /\ maxValue_wide h2 c (length c) <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
  admit(); // OK
  cut(forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = vv (get h0 a i) * vv (get h0 b ctr)); 
  cut(forall (i:nat). {:pattern (v (get h2 c (i+ctr)))} i < norm_length ==> v (get h2 c (i+ctr)) = v (get h1 c (i+ctr)) + v (get h1 tmp i)); 
  cut(forall (i:nat). {:pattern (v (get h2 c i))} 
    ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h1 c i)); 
  (* no_upd_lemma h0 h1 c (only tmp); *)
  cut(forall (i:nat). {:pattern (v (get h1 c i))} i < length c ==> v (get h1 c i) = v (get h0 c i)); 
  cut(forall (i:nat). {:pattern (v (get h1 tmp i))}
    i < norm_length ==> v (get h1 tmp i) = vv (get h0 a i) * vv (get h0 b ctr)); 
  cut(forall (i:nat). i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (vv (get h0 a i) * vv (get h0 b ctr))); 
  max_value_lemma_1 h0 h1 h2 a b ctr c tmp

let modifies_2 c tmp h0 h1 =
  HyperHeap.modifies_just (Set.union (Set.singleton (frameOf c)) (Set.singleton (frameOf tmp))) h0.h h1.h
  /\ modifies_bufs (frameOf c) (only c ++ only tmp) h0 h1
  /\ modifies_bufs (frameOf tmp) (only c ++ only tmp) h0 h1
  /\ h0.tip = h1.tip

val standardized_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint_wide{disjoint a c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint c tmp} -> Lemma
    (requires (norm h0 a /\ live h0 c /\ live h1 tmp /\ live h1 c
	/\ modifies_1 tmp h0 h1
	/\ modifies_1 c h1 h2 ))
     (ensures (norm h0 a /\ norm h2 a /\ live h0 c  /\ live h1 tmp /\ live h2 tmp
       /\ modifies_2 c tmp h0 h2 ))
let standardized_lemma h0 h1 h2 a c tmp =
  admit(); // OK
  (* cut(modifies !{getRef c,getRef tmp} h0 h2);  *)
  (* no_upd_lemma h0 h2 a (only c ++ tmp); *)
  (* no_upd_lemma h1 h2 tmp (only c); *)
  cut(forall (i:nat). {:pattern (vv (get h2 a i))} i < norm_length ==> vv (get h2 a i) = vv (get h0 a i));
  cut(True /\ live h2 a); cut(True /\ length a >= norm_length); cut (True /\ templ = templ); 
  cut(forall (i:nat). {:pattern (norm h2 a)} i < norm_length ==> vv (get h2 a i) < pow2 (templ i)); 
  cut(norm h2 a)

val length_lemma: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide -> ctr:nat{ctr < norm_length} ->
  tmp:bigint_wide{disjoint c tmp} -> Lemma 
     (requires (live h0 c /\ live h1 tmp /\ live h1 c /\ live h0 tmp
	/\ length c >= 2 * norm_length - 1
	/\ modifies_1 tmp h0 h1
	/\ live h2 c /\ live h2 tmp
	/\ ctr+norm_length <= length c
	/\ modifies_1 c h1 h2 ))
     (ensures (live h0 c /\ live h2 c  /\ live h0 tmp /\ live h2 tmp
       /\ length c >= 2 * norm_length - 1
       /\ modifies_2 c tmp h0 h2 ))
let length_lemma h0 h1 h2 c ctr tmp =
  admit(); // OK
  (* no_upd_lemma h0 h1 c (only tmp); *)
  (* no_upd_lemma h1 h2 tmp (only c); *)
  ()

val lemma_helper_20:   h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
  (requires(live h2 tmp /\ live h1 tmp /\ live h1 c /\ live h2 c /\ length c >= 2 * norm_length - 1
    /\ FsumWide.isSum h1 h2 ctr 0 norm_length 0 c tmp 
    ))
  (ensures (live h2 tmp /\ live h1 tmp /\ live h2 c /\ live h1 c /\ length c >= 2 * norm_length - 1
    /\ FsumWide.isSum h1 h2 ctr 0 norm_length 0 c tmp
    /\ storesSum h2 c h1 c h1 tmp ctr norm_length ))
let lemma_helper_20 h0 h1 h2 a b ctr c tmp = ()

val multiplication_step_lemma_02: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:u32{w ctr < norm_length} ->
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
     (requires (norm h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h1 c	/\ live h0 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValueNorm h0 a < pow2 max_limb
	/\ maxValueNorm h0 b < pow2 max_limb
	/\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b
	// After fscalar
	/\ modifies_1 tmp h0 h1
	/\ isScalarProduct h1 tmp h0 a (get h0 b (w ctr))
        /\ eval_wide h1 tmp norm_length = eval h0 a norm_length * vv (get h0 b (w ctr))
 	// After fsum
	/\ live h2 c /\ live h2 tmp
	/\ w ctr+norm_length <= length c
	/\ modifies_1 c h1 h2
	/\ FsumWide.isSum h1 h2 (w ctr) 0 norm_length 0 c tmp
	/\ FsumWide.isNotModified h1 h2 (w ctr) norm_length 0 c ))
     (ensures (norm h0 a /\ norm h2 a /\ norm h0 b /\ norm h2 b
       /\ live h0 c /\ live h2 c  /\ live h0 tmp /\ live h2 tmp  /\ length c >= 2 * norm_length - 1
       /\ modifies_2 c tmp h0 h2
       /\ maxValueNorm h0 a < pow2 max_limb
       /\ maxValueNorm h0 b < pow2 max_limb
       /\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b
       /\ maxValue_wide h2 c (length c) <= (w ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b
       /\ eval_wide h2 c (2*norm_length-1) = eval_wide h0 c (2*norm_length-1) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr)) ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
  admit(); // OK timeout 50
  assert(forall (i:nat). (i >= norm_length + w ctr /\ i < 2 * norm_length - 1) ==>
  	   v (get h2 c i) = v (get h1 c i));
  (* eval_partial_eq_lemma h1 h2 c c (norm_length+ctr) (2*norm_length-1);  *)
  (* no_upd_lemma h0 h1 c (only tmp); *)
  (* cut(forall (i:nat). i < length c ==> v (get h0 c i) = v (get h1 c i));  *)
  (* eval_eq_lemma h0 h1 c c (2*norm_length-1); *)
  (* eval_eq_lemma h0 h1 c c (norm_length+ctr); *)
  cut(True /\ eval_wide h2 c (2*norm_length-1) - eval_wide h2 c (norm_length+w ctr) = eval_wide h0 c (2*norm_length-1) - eval_wide h0 c (norm_length+w ctr)); 
  (* cut (True /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr));  *)
  lemma_helper_20 h0 h1 h2 a b (w ctr) c tmp;
  (* cut (storesSum h2 c h1 c h1 tmp ctr norm_length); admit() *)
  partial_equality_lemma h1 h2 c (w ctr); 
  cut (partialEquality h2 c h1 c (w ctr)); 
  multiplication_step_lemma h1 h2 c tmp c (w ctr) norm_length; 
  cut (True /\ eval_wide h2 c (norm_length+w ctr) = eval_wide h1 c (norm_length+w ctr) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr)));
  cut (True /\ eval_wide h2 c (norm_length+w ctr) = eval_wide h0 c (norm_length+w ctr) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr)));
  cut (True /\ eval_wide h2 c (2*norm_length-1) = eval_wide h0 c (2*norm_length-1) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr)));
  max_value_lemma h0 h1 h2 a b (w ctr) c tmp; 
  Math.Lemmas.paren_mul_right (w ctr+1) (maxValueNorm h0 a) (maxValueNorm h0 b);
  (* assert(maxValue_wid h2 c <= (ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b);  *)
  standardized_lemma h0 h1 h2 a c tmp; 
  standardized_lemma h0 h1 h2 b c tmp;
  length_lemma h0 h1 h2 c (w ctr) tmp;
  ()
  
#reset-options

val multiplication_step_p1: a:bigint -> b:bigint -> ctr:u32{w ctr<norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit 
     (requires (fun h -> norm h a /\ norm h b /\ live h c /\ live h tmp
        /\ length c >= 2*norm_length -1
	/\ maxValueNorm h a < pow2 max_limb
	/\ maxValueNorm h b < pow2 max_limb
	/\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b
	/\ eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr) ))
     (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp
       /\ norm h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp
       /\ length c >= 2*norm_length -1
       /\ modifies_2 c tmp h0 h1
       /\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b
       /\ maxValue_wide h1 c (length c) <= (w ctr+1) * (maxValueNorm h0 a * maxValueNorm h0 b)
       /\ eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr)
       /\ (eval_wide h1 c (2*norm_length-1) = eval_wide h0 c (2*norm_length-1) + pow2 (bitweight (templ) (w ctr)) * eval h0 a norm_length * vv (get h0 b (w ctr)))
     ))
let multiplication_step_p1 a b ctr c tmp =
  admit(); // OK
  let h0 = HST.get() in
  multiplication_step_0 a b ctr c tmp; 
  let h1 = HST.get() in
  multiplication_step_lemma_01 h0 h1 a b (w ctr) c tmp; 
  FsumWide.fsum_index c ctr tmp 0ul nlength 0ul; 
  let h2 = HST.get() in 
  multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp

val helper_lemma_6: h0:heap -> h1:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
     (requires (norm h0 a /\ norm h0 b /\ live h0 c /\ length c >= 2 * norm_length - 1))
    (ensures (norm h0 a /\ norm h0 b /\ live h0 c /\ length c >= 2 * norm_length - 1
       /\ eval_wide h0 c (2*norm_length-1) + pow2 (bitweight (templ) ctr) * eval h0 a (norm_length) * vv (get h0 b ctr)  = eval h0 a (norm_length) * vv (get h0 b ctr) * pow2 (bitweight (templ) ctr) + eval_wide h0 c (2*norm_length-1) ))
let helper_lemma_6 h0 h1 a b ctr c tmp = ()
  (* FproductLemmas.helper_lemma_5 (eval h0 c (2*norm_length-1)) (pow2 (bitweight (templ) ctr)) (eval h0 a norm_length) (v (get h0 b ctr)) *)

(* Code : does 1 step of the multiplication (1 scalar multiplication), 
   and infers the appropriate properties on sizes, values and evaluated
   values for the resulting bigint *)
val multiplication_step: a:bigint -> b:bigint -> ctr:u32{w ctr < norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit  
     (requires (fun h -> norm h a /\ norm h b /\ live h c /\ live h tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValueNorm h a < pow2 max_limb
	/\ maxValueNorm h b < pow2 max_limb
	/\ maxValue_wide h c (length c) <= w ctr * maxValueNorm h a * maxValueNorm h b
	/\ eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr) ))
     (ensures (fun h0 u h1 -> norm h0 a /\ norm h1 a /\ norm h0 b /\ norm h1 b
       /\ live h0 c /\ live h1 c  /\ live h0 tmp /\ live h1 tmp
       /\ length c >= 2 * norm_length - 1
       /\ modifies_2 c tmp h0 h1
       /\ maxValueNorm h0 a < pow2 max_limb
       /\ maxValueNorm h0 b < pow2 max_limb
       /\ maxValue_wide h0 c (length c) <= w ctr * maxValueNorm h0 a * maxValueNorm h0 b
       /\ maxValue_wide h1 c (length c) <= (w ctr+1) * maxValueNorm h0 a * maxValueNorm h0 b
       /\ eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr)
       /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * vv (get h0 b (w ctr)) * pow2 (bitweight (templ) (w ctr)) + eval_wide h0 c (2*norm_length-1)
     ))
let multiplication_step a b ctr c tmp =
  let h0 = HST.get() in
  multiplication_step_p1 a b ctr c tmp;  
  let h1 = HST.get() in
  helper_lemma_6 h0 h1 a b (w ctr) c tmp
  
(* Lemma : factorizes "eval" equation *)
val multiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{norm h0 a} -> b:bigint{norm h0 b} ->
  ctr:pos{ctr <= norm_length} -> c:bigint_wide{live h1 c /\ length c >= 2*norm_length-1} -> Lemma
    (requires (eval_wide h1 c (2*norm_length-1) = (eval h0 a (norm_length) * vv (get h0 b (norm_length - ctr))) * pow2 (bitweight (templ) (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures (eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
let multiplication_step_lemma_03 h0 h1 a b ctr c =
  admit(); // OK
  let t = templ in 
  Math.Lemmas.paren_mul_left (eval h0 a norm_length) (vv (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr)));
  cut (True /\ eval_wide h1 c (2*norm_length-1) = eval h0 a norm_length * vv (get h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ); 
  Math.Lemmas.swap_mul (vv (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr)));
  cut (True /\ eval_wide h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * vv (get h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) ) ; 
  Math.Lemmas.distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * vv (get h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr));
  cut (True /\ eval_wide h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * vv (get h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr))); 
  eval_def h0 b (norm_length-ctr+1)

val helper_lemma_7: ctr:pos{ctr < norm_length} -> Lemma 
    (requires (True))
    (ensures (norm_length - ctr + 1 >= 0 /\ norm_length - ctr + 1 <= norm_length))
    [SMTPat (norm_length - ctr + 1)]
let helper_lemma_7 ctr = ()
  (* FproductLemmas.helper_lemma_7 norm_length ctr *)

val multiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (norm h0 a /\ norm h1 a /\ norm h0 b /\ norm h1 b
       /\ live h0 c /\ live h1 c  /\ live h0 tmp /\ live h1 tmp 
       /\ length c >= 2 * norm_length - 1
       /\ ((norm_length - ctr) < norm_length) 
       /\ modifies_2 c tmp h0 h1
       /\ maxValueNorm h0 a < pow2 max_limb
       /\ maxValueNorm h0 b < pow2 max_limb
       /\ maxValue_wide h0 c (length c) <= (norm_length - ctr) * maxValueNorm h0 a * maxValueNorm h0 b
       /\ maxValue_wide h1 c (length c) <= ((norm_length - ctr)+1) * maxValueNorm h0 a * maxValueNorm h0 b
       /\ eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * vv (get h0 b (norm_length - ctr)) * pow2 (bitweight (templ) (norm_length - ctr)) + eval_wide h0 c (2*norm_length-1) ))
    (ensures (norm h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp /\ (length c >= 2 * norm_length - 1)
	/\ maxValueNorm h1 a < pow2 max_limb
	/\ maxValueNorm h1 b < pow2 max_limb
	/\ maxValue_wide h1 c (length c) <= (norm_length - ctr + 1) * (maxValueNorm h1 a * maxValueNorm h1 b)
	/\ eval_wide h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp =
  admit(); // OK timeout 50
  (* no_upd_lemma h0 h1 a (only c ++ tmp); *)
  maxValueNorm_eq_lemma h0 h1 a a; 
  eval_eq_lemma h0 h1 a a norm_length;
  (* no_upd_lemma h0 h1 b (only c ++ tmp);  *)
  maxValueNorm_eq_lemma h0 h1 b b; 
  eval_eq_lemma h0 h1 b b (norm_length - ctr);
  eval_eq_lemma h0 h1 b b (norm_length - ctr + 1);
  cut((maxValueNorm h1 a = maxValueNorm h0 a)
       /\ (maxValueNorm h1 b = maxValueNorm h0 b)); 
  cut((norm_length - ctr)+1 = norm_length - ctr + 1 /\ True);
  cut(eval h0 a norm_length = eval h1 a norm_length /\ eval h0 b (norm_length-ctr) = eval h1 b (norm_length - ctr) /\ eval h0 b (norm_length - ctr + 1) = eval h1 b (norm_length - ctr + 1) /\ vv (get h0 b (norm_length - ctr)) = vv (get h1 b (norm_length - ctr)));
  Math.Lemmas.paren_mul_right (norm_length - ctr + 1) (maxValueNorm h1 a) (maxValueNorm h1 b);
  cut(norm_length - ctr + 1 > 0 /\ length b >= norm_length - ctr + 1);
  eval_def h0 b (norm_length - ctr + 1); 
  assert (eval_wide h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr));
  assert (eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * vv (get h0 b (norm_length - ctr)) * pow2 (bitweight (templ) (norm_length - ctr)) + eval_wide h0 c (2*norm_length-1));
  assert (eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * vv (get h0 b (norm_length - ctr)) * pow2 (bitweight (templ) (norm_length - ctr)) + (eval h0 a (norm_length) * eval h0 b (norm_length - ctr))); 
  (* FproductLemmas.helper_lemma_12 (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight (templ) (norm_length - ctr))) (eval h0 b (norm_length - ctr)) *)
  ()
  
val multiplication_aux_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr <= norm_length} -> c:bigint_wide{disjoint a c /\ disjoint b c} -> 
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
    (requires ((norm h0 a) /\ (norm h0 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (norm h1 a) /\ (norm h1 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (norm h2 a) /\ (norm h2 b) /\ (live h2 c) /\ (live h2 tmp)
       /\ (length c >= 2 * norm_length - 1)
       /\ modifies_2 c tmp h0 h1
       /\ modifies_2 c tmp h1 h2
       /\ eval_wide h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length) ))
    (ensures (norm h0 a /\ norm h0 b /\ live h1 c /\ norm h2 a /\ norm h2 b /\ live h2 c
       /\ length c >= 2 * norm_length - 1
       /\ modifies_2 c tmp h0 h2
       /\ eval_wide h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
  admit(); // OK
    cut(modifies_2 c tmp h0 h2);
    (* no_upd_lemma h0 h1 a (only c ++ tmp);  *)
    (* no_upd_lemma h0 h1 b (only c ++ tmp);  *)
    eval_eq_lemma h0 h1 a a norm_length; 
    eval_eq_lemma h0 h1 b b norm_length

(* Code : tail recursive calls to run the multiplication *)
val multiplication_aux: a:bigint -> b:bigint -> ctr:u32{w ctr <= norm_length} -> 
  c:bigint_wide{disjoint a c /\ disjoint b c} ->
  tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit
     (requires (fun h -> (norm h a) /\ (norm h b) /\ (live h c) /\ (live h tmp)
	/\ (length c >= 2 * norm_length - 1)
	/\ (maxValueNorm h a < pow2 max_limb)
	/\ (maxValueNorm h b < pow2 max_limb)
	/\ (maxValue_wide h c (length c) <= (norm_length - w ctr) * (maxValueNorm h a * maxValueNorm h b))
	/\ (eval_wide h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - w ctr))))
     (ensures (fun h0 u h1 -> 
       (norm h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h0 tmp)
       /\ (norm h1 a) /\ (norm h1 b) /\ (live h1 c) /\ (live h1 tmp)
       /\ (length c >= 2 * norm_length - 1)
       /\ (modifies_2 c tmp h0 h1)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
       /\ (maxValue_wide h1 c (length c) <= norm_length * (maxValueNorm h0 a * maxValueNorm h0 b))
     ))
let rec multiplication_aux a b ctr c tmp = 
  let h0 = HST.get() in
  if U32.eq ctr 0ul then ()
  else begin
    (* FproductLemmas.helper_lemma_8 norm_length ctr; *)
    multiplication_step a b (nlength -| ctr) c tmp;
    let h1 = HST.get() in    
    multiplication_aux_lemma h0 h1 a b (w ctr) c tmp;
    multiplication_aux a b (ctr-|1ul) c tmp;
    let h2 = HST.get() in
    multiplication_aux_lemma_2 h0 h1 h2 a b (w ctr) c tmp
  end

#reset-options

(* val helper_lemma_16: h0:heap -> h1:heap -> a:bigint -> mods:FStar.Set.set aref -> *)
(*   Lemma (requires (norm h0 a /\ modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef a)) mods))) *)
(* 	(ensures (norm h1 a)) *)
(* let helper_lemma_16 h0 h1 a mods =  *)
(*   no_upd_lemma h0 h1 a mods *)

val helper_lemma_13: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires ((norm h0 a) /\ modifies FStar.Set.empty h0 h1))
    (ensures (norm h0 a /\ norm h1 a
	      /\ live h1 a /\ length a >= norm_length
	      /\ maxValueNorm h0 a = maxValueNorm h1 a
	      /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a = 
  admit(); // OK
  (* no_upd_lemma h0 h1 a (!{}); *)
  (* helper_lemma_16 h0 h1 a !{}; *)
  eval_eq_lemma h0 h1 a a norm_length; 
  maxValueNorm_eq_lemma h0 h1 a a

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint_wide ->
  Lemma
    (requires (live h0 c /\ null_wide h0 c /\ length c >= 2 * norm_length - 1 /\ modifies FStar.Set.empty h0 h1))
    (ensures (live h1 c /\ null_wide h1 c /\ maxValue_wide h1 c (length c) <= 0 /\ length c >= 2 * norm_length - 1 /\ eval_wide h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  admit(); // OK
  (* no_upd_lemma h0 h1 c !{}; *)
  ()
  (* eval_null h1 c (2*norm_length - 1);  *)
  (* max_value_of_null_lemma h1 c *)

#reset-options

val multiplication_lemma_1: h0:heap -> h1:heap -> c:bigint_wide -> a:bigint{disjoint c a} -> 
  b:bigint{disjoint c b} -> Lemma
     (requires (norm h0 a /\ norm h0 b /\ live h0 c /\ null_wide h0 c /\ length c >= 2*norm_length-1
	/\ maxValueNorm h0 a < pow2 max_limb
	/\ maxValueNorm h0 b < pow2 max_limb
	/\ HyperStack.modifies FStar.Set.empty h0 h1
	/\ h0.tip = h1.tip))
     (ensures (norm h1 a /\ norm h1 b /\ live h1 c /\ null_wide h1 c /\ length c >= 2*norm_length-1
	/\ maxValueNorm h1 a < pow2 max_limb
	/\ maxValueNorm h1 b < pow2 max_limb
	/\ maxValue_wide h1 c (length c) <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b)
	/\ (eval_wide h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)) ))
let multiplication_lemma_1 h0 h1 c a b =
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(norm_length - norm_length = 0 /\ True); 
  (* FproductLemmas.auxiliary_lemma_90 (norm_length);  *)
  (* FproductLemmas.helper_lemma_13 (maxValueNorm h1 a * maxValueNorm h1 b);  *)
  cut(True /\ eval h1 b 0 = 0); 
  (* FproductLemmas.helper_lemma_13 (eval h1 a norm_length) *)
  ()

val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide -> tmp:bigint_wide{disjoint c tmp} ->
  Lemma
    (requires (live h0 c /\ live h2 c /\ ~(contains h0 (tmp))
	       /\ modifies FStar.Set.empty h0 h1 /\ live h1 tmp /\ modifies_2 c tmp h1 h2))
    (ensures (modifies_1 c h0 h2))
let helper_lemma_14 h0 h1 h2 c tmp =
  admit(); // OK
  ()

val multiplication_lemma_2: h0:heap -> h1:heap -> h2:heap -> c:bigint_wide ->  a:bigint{disjoint c a} -> 
  b:bigint{disjoint c b} -> tmp:bigint_wide{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
     (requires (norm h0 a /\ norm h0 b /\ live h0 c /\ null_wide h0 c /\ length c >= 2*norm_length-1
	/\ maxValueNorm h0 a < pow2 max_limb
	/\ maxValueNorm h0 b < pow2 max_limb
	/\ HyperStack.modifies FStar.Set.empty h0 h1 /\ h0.tip = h1.tip 
	/\ ~(contains h0 (tmp)) /\ contains h1 (tmp)
	/\ norm h1 a /\ norm h1 b /\ live h1 c /\ null_wide h1 c
	/\ length c >= 2*norm_length-1
	/\ maxValueNorm h1 a < pow2 max_limb
	/\ maxValueNorm h1 b < pow2 max_limb
	/\ maxValue_wide h1 c (length c) <= (norm_length - norm_length) * (maxValueNorm h1 a * maxValueNorm h1 b)
	/\ eval_wide h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)
       /\ norm h2 a /\ norm h2 b /\ live h2 c
       /\ length c >= 2*norm_length-1
       /\ modifies_2 c tmp h1 h2
       /\ eval_wide h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length)
       /\ maxValue_wide h2 c (length c) <= norm_length * (maxValueNorm h1 a * maxValueNorm h1 b)
     ))
     (ensures (
       (norm h0 a) /\ (norm h0 b) /\ (live h0 c)
       /\ (norm h2 a) /\ (norm h2 b) /\ (live h2 c)
       /\ (length c >= 2*norm_length-1) /\ (length c >= 2*norm_length-1)
       /\ (null_wide h0 c) /\ (modifies_1 c h0 h2)
       /\ (maxValueNorm h0 a < pow2 max_limb)
       /\ (maxValueNorm h0 b < pow2 max_limb)
       /\ (eval_wide h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length))
       /\ (maxValue_wide h2 c (length c) <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b) ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
  admit(); // OK
  helper_lemma_14 h0 h1 h2 c tmp;
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

(* Code : core multiplication function *)
val multiplication: c:bigint_wide -> a:bigint{disjoint c a} -> b:bigint{disjoint c b} -> STL unit
     (requires (fun h -> norm h a /\ norm h b /\ live h c /\ null_wide h c /\ length c >= 2*norm_length-1
	/\ maxValueNorm h a < pow2 max_limb
	/\ maxValueNorm h b < pow2 max_limb ))
     (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h0 c /\ norm h1 a /\ norm h1 b /\ live h1 c
       /\ length c >= 2*norm_length-1
       /\ null_wide h0 c /\ modifies_1 c h0 h1
       /\ maxValueNorm h0 a < pow2 max_limb
       /\ maxValueNorm h0 b < pow2 max_limb
       /\ eval_wide h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue_wide h1 c (length c) <= norm_length * maxValueNorm h0 a * maxValueNorm h0 b ))
let multiplication c a b =
  admit(); // OK
  let h0 = HST.get() in
  let tmp = create (UInt128.of_string "0") nlength in
  let h1 = HST.get() in
  assert(modifies FStar.Set.empty h0 h1); 
  multiplication_lemma_1 h0 h1 c a b; 
  cut(True /\ length tmp >= norm_length);
  (* constant_template_lemma c a;  *)
  multiplication_aux a b nlength c tmp; 
  let h2 = HST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp
