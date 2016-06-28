module Poly.Bignum

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open Math.Axioms
open Math.Lib
open Math.Lemmas
open FStar.UInt64
open FStar.Buffer
open Poly.Bigint
open Poly.Parameters

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

let u32 = UInt32.t

let w: u32 -> Tot int = U32.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub
let op_Hat_Less_Less = U64.op_Less_Less_Hat
let op_Hat_Greater_Greater = U64.op_Greater_Greater_Hat
let op_Hat_Subtraction = U64.op_Subtraction_Hat
let op_Hat_Amp = U64.op_Amp_Hat

let heap = HS.mem

(* Prime value *)
val prime: p:erased pos{reveal p = pow2 130 - 5}
let prime = hide (pow2 130 - 5)

let live (h:heap) (b:bigint) : GTot Type0 = live h b /\ length b >= norm_length

(* Lemmas that should go elsewhere but are terribly useful *)
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

(*** Addition ***)

let willNotOverflow (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint) : GTot Type0 =
  live h a /\ length a >= a_idx+len /\ live h b /\ length b >= b_idx+len
  /\ (forall (i:nat). {:pattern (v (get h a (i+a_idx)))} (i >= ctr /\ i < len) ==>
	(v (get h a (i+a_idx)) + v (get h b (i+b_idx)) < pow2 64))

let isNotModified (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) (a:bigint) : GTot Type0 = 
  live h0 a /\ live h1 a /\ a_idx+len <= length a 
  /\  (forall (i:nat). {:pattern (get h1 a i)} ((i<ctr+a_idx \/ i >= len+a_idx) /\ i < length a) ==>
	       get h1 a i = get h0 a i)

let isSum (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat) (a:bigint) (b:bigint) : GTot Type0 =
  live h0 a /\ live h1 a /\ a_idx+len <= length a /\ live h0 b /\ b_idx+len <= length b
  /\ (forall (i:nat). {:pattern (v (get h1 a (i+a_idx)))} (i>= ctr /\ i<len) ==> 
	v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)))

(* I have no idea why that fails *)
val op_Plus_Hat: a:U64.t -> b:U64.t -> Pure U64.t (requires (v a + v b < pow2 64 /\ v a + v b >= 0))
							 (ensures (fun c -> v c = v a + v b))
let op_Plus_Hat a b = admit(); FStar.UInt64.op_Plus_Hat a b

val op_Hat_Star: a:U64.t -> b:U64.t -> Pure U64.t (requires (v a * v b < pow2 64 /\ v a * v b >= 0))
							 (ensures (fun c -> v c = v a * v b))
let op_Hat_Star a b = admit(); FStar.UInt64.op_Star_Hat a b

(* More specialized than the "no_upd_lemma_1" from FStar.Buffer.fst *)
let eq_lemma_1 h0 h1 (a:bigint) (b:bigint) : Lemma 
  (requires (modifies_1 a h0 h1 /\ disjoint a b /\ live h0 a /\ live h0 b))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). i < length b ==> get h1 b i = get h0 b i)))
  = ()

let eq_lemma_2 h0 h1 (a:bigint) (a':bigint) (b:bigint) : Lemma 
  (requires (modifies_2 a a' h0 h1 /\ disjoint a b /\ disjoint a' b 
    /\ live h0 a /\ live h0 b /\ live h0 a'))
  (ensures  (live h0 b /\ live h1 b /\ (forall (i:nat). i < length b ==> get h1 b i = get h0 b i)))
  = ()

#set-options "--lax" // TODO

val fsum_index: a:bigint -> a_idx:u32 -> b:bigint{disjoint a b} -> b_idx:u32 -> len:u32 -> 
  ctr:u32{w ctr<=w len} -> STL unit
    (requires (fun h -> live h a /\ live h b /\ w a_idx+w len <= length a /\ w b_idx+w len <= length b
	/\ willNotOverflow h (w a_idx) (w b_idx) (w len) (w ctr) a b))
    (ensures (fun h0 _ h1 -> live h0 a /\ live h0 b /\ live h1 a /\ live h1 b
      /\ w a_idx+w len <= length a /\ w b_idx+w len <= length b /\ modifies_1 a h0 h1
      /\ isNotModified h0 h1 (w a_idx) (w len) (w ctr) a
      /\ isSum h0 h1 (w a_idx) (w b_idx) (w len) (w ctr) a b))
let rec fsum_index a a_idx b b_idx len ctr =
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
      let i = ctr in
      let (ai:U64.t) = index a (i+|a_idx) in 
      let (bi:U64.t) = index b (i+|b_idx) in 
      let z = ai +^ bi in
      upd a (a_idx+|i) z; 
      let h1 = HST.get() in
      eq_lemma_1 h0 h1 a b; 
      fsum_index a a_idx b b_idx len (ctr+|1ul);
      let h2 = HST.get() in
      eq_lemma_1 h1 h2 a b;
      assert(isSum h1 h2 (w a_idx) (w b_idx) (w len) (w ctr + 1) a b);
      assert(isSum h0 h2 (w a_idx) (w b_idx) (w len) (w ctr + 1) a b); 
      assert(v (get h2 a (w a_idx + w ctr)) = v (get h0 a (w a_idx + w ctr)) + v (get h0 b (w b_idx + w ctr)) )
  end

#reset-options
#set-options "--lax" // OK

val addition_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a /\ live h1 a} -> b:bigint{live h0 b} ->
  len:nat{len <= length a /\ len <= length b /\ 
	 (forall (i:nat). {:pattern (v (get h1 a i))} i < len ==> 
	    v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } -> 
  Lemma (requires (True)) (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let rec addition_lemma h0 h1 a b len =
  match len with
  | 0 -> ()
  | _ -> addition_lemma h0 h1 a b (len-1); 
    distributivity_add_right (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1))) (v (get h0 b (len-1)))

#reset-options
#set-options "--lax" // OK

val fsum': a:bigint -> b:bigint{disjoint a b} -> STL unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ live h1 a 
      /\ modifies_1 a h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      /\ isNotModified h0 h1 0 norm_length 0 a
      /\ isSum h0 h1 0 0 norm_length 0 a b))
let fsum' a b =
  let h0 = HST.get() in
  cut (pow2 26 + pow2 26 <= pow2 27);
  Math.Lib.pow2_increases_lemma 64 27;
  let h0 = HST.get() in
  fsum_index a 0ul b 0ul nlength 0ul; 
  let h1 = HST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0)));
  cut (forall (i:nat). (i >= norm_length /\ i < length a) ==> v (get h1 a (i+0)) = v (get h0 a (i+0)));
  addition_lemma h0 h1 a b norm_length;
  ()

#reset-options

(*** Scalar multiplication ***)

#set-options "--lax" // OK

val scalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint{live h1 b} -> s:u64 -> len:nat{len <= length a /\ len <= length b} ->
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

let scalarProduct (h0:heap) (h1:heap) (ctr:nat) (a:bigint) (s:u64) (res:bigint) : GTot Type0 =
  live h0 a /\ live h1 res /\ ctr <= norm_length
  /\ (forall (i:nat). {:pattern (v (get h1 res i))} i < ctr ==> v (get h1 res i) = v (get h0 a i) * v s)

(* Equality between fragments of buffers *)
let equalSub (ha:heap) (a:bigint) (a_idx:nat) (hb:heap) (b:bigint) (b_idx:nat) (len:nat) : GTot Type0 =
  (live ha a) /\ (live hb b) /\ (length a >= a_idx + len) /\ (length b >= b_idx + len)
  /\ (forall (i:nat). {:pattern (get ha a (a_idx+i)) \/ (get hb b (b_idx+i))} i < len ==> get ha a (a_idx+i) = get hb b (b_idx+i))

#reset-options "--z3timeout 5"

let lemma_helper_01 (ctr:u32): Lemma (forall (i:nat). {:pattern (w ctr+i-1)} w ctr + i - 1 = w ctr - 1 + i)
  = ()

let lemma_helper_02 h0 h2 (a:bigint{live h0 a}) (res:bigint{live h2 res}) (ctr:u32{w ctr <= norm_length /\ w ctr > 0}) (s:u64) : Lemma
  (requires (
    (forall (i:nat). {:pattern (v (get h2 res i))} i < w ctr - 1 ==> v (get h2 res i) = v (get h0 a i) * v s)
    /\ v (get h2 res (w ctr - 1)) = v (get h0 a (w ctr - 1)) * v s))
  (ensures (scalarProduct h0 h2 (w ctr) a s res))
  = ()

#reset-options "--z3timeout 200"
#set-options "--lax" // OK

val scalar_multiplication_aux: res:bigint -> a:bigint{disjoint res a} -> s:u64 -> ctr:u32 -> STL unit
  (requires (fun h -> live h res /\ live h a /\ w ctr <= norm_length
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < w ctr ==> v (get h a i) * v s < pow2 64) ))
  (ensures (fun h0 _ h1 -> scalarProduct h0 h1 (w ctr) a s res 
    /\ modifies_1 res h0 h1 /\ equal h0 a h1 a 
    /\ equalSub h0 res (w ctr) h1 res (w ctr) (length res - w ctr) ))
let rec scalar_multiplication_aux res a s ctr =
  let h0 = HST.get() in
  if U32.eq ctr 0ul then ()
  else begin
    let i = ctr -| 1ul in
    let ai = index a i in
    let resi = ai ^* s in
    upd res i resi; 
    let h1 = HST.get() in
    eq_lemma_1 h0 h1 res a;
    scalar_multiplication_aux res a s i;
    let h2 = HST.get() in
    eq_lemma_1 h1 h2 res a;
    cut (modifies_1 res h0 h2);
    cut (equal h0 a h2 a);
    cut (forall (i:nat). {:pattern (v (get h2 res (w ctr+i-1)))} i < length res - w ctr + 1 ==> v (get h2 res (w ctr-1 + i)) = v (get h1 res (w ctr-1+i)));
    lemma_helper_01 ctr;
    cut (forall (i:nat). {:pattern (v (get h2 res (w ctr+(i-1))))} i < length res - w ctr + 1 ==> v (get h2 res (w ctr+i-1)) = v (get h1 res (w ctr+i-1)));
    cut (forall (i:nat). {:pattern (get h2 res (w ctr+i))} i < length res - w ctr ==> v (get h2 res (w ctr-1+(i+1))) = v (get h1 res (w ctr-1+i+1)));
    cut (equalSub h1 res (w i) h2 res (w i) (length res - w i));
    cut (forall (i:nat). {:pattern (v (get h2 res i))} i < w ctr - 1 ==> v (get h2 res i) = v (get h1 a i) * v s);
    cut (forall (i:nat). {:pattern (v (get h1 res i))} (i < length res /\ i <> w ctr-1) ==> v (get h1 res i) = v (get h0 res i));
    cut (v (get h2 res (w ctr - 1)) = v (get h0 a (w ctr - 1)) * v s);
    lemma_helper_02 h0 h2 a res ctr s;
    cut (scalarProduct h0 h2 (w ctr) a s res); 
    cut (equal h0 a h2 a);
    cut (equalSub h0 res (w ctr) h1 res (w ctr) (length res - w ctr));
    ()
  end

#reset-options

val scalar_multiplication: res:bigint -> a:bigint{disjoint res a} -> s:u64 -> STL unit
  (requires (fun h -> live h res /\ live h a
    /\ (forall (i:nat). {:pattern (v (get h a i))} i < norm_length ==> v (get h a i) * v s < pow2 64) ))
  (ensures (fun h0 _ h1 -> scalarProduct h0 h1 norm_length a s res 
    /\ modifies_1 res h0 h1 /\ equal h0 a h1 a 
    /\ equalSub h0 res norm_length h1 res norm_length (length res - norm_length)
    /\ eval h1 res norm_length = eval h0 a norm_length * v s ))
let scalar_multiplication res a s =
  let h0 = HST.get() in
  scalar_multiplication_aux res a s nlength;
  let h1 = HST.get() in
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

val auxiliary_lemma_1: a:nat -> b:nat -> 
  Lemma 
    (requires (True))
    (ensures (pow2 (bitweight templ (a+b)) = pow2 (bitweight templ a) * pow2 (bitweight templ b))) 
let auxiliary_lemma_1 a b =
  bitweight_lemma_0 a b;
  Math.Lib.pow2_exp_lemma (bitweight templ a) (bitweight templ b);
  ()

let partialEquality (ha:heap) (a:bigint) (hb:heap) (b:bigint) (len:nat) : GTot Type0 =
  live ha a /\ live hb b /\ len <= length a /\ len <= length b	      
  /\ (forall (i:nat). {:pattern (v (get ha a i))} i < len ==> v (get ha a i) = v (get hb b i))

let storesSum (hc:heap) (c:bigint) (ha:heap) (a:bigint) (hb:heap) (b:bigint)
		      (a_idx:nat) (len:nat) : GTot Type0 =
  live ha a /\ live hb b /\ live hc c /\ a_idx+len <= length a /\ len <= length b /\ a_idx+len <= length c
  /\  (forall (i:nat). {:pattern (v (get hc c (i+a_idx)))}
	(i < len ==> v (get hc c (i+a_idx)) = v (get ha a (i+a_idx)) + v (get hb b i)))

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val multiplication_step_lemma_1:
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> b:bigint{live h0 b} -> c:bigint{live h1 c} ->
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
  cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1)));
  eval_def h1 c (len+idx);
  cut (eval h1 c (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)) + eval h1 c (len+idx-1));
  cut (eval h1 c (len+idx) = eval h1 c (len+idx-1) + pow2 (bitweight t (len+idx-1)) * v (get h1 c (len+idx-1)));
  cut (eval h1 c (len+idx-1) = eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1) /\ True);
  cut (v (get h1 c (len+idx-1)) = v (get h0 a (len+idx-1)) + v (get h0 b (len-1))); 
  cut (eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ pow2 (bitweight t (len-1+idx)) * (v (get h0 a (len+idx-1)) + v (get h0 b (len-1))));
  distributivity_add_right (pow2 (bitweight t (len-1+idx))) (v (get h0 a (len+idx-1))) (v (get h0 b (len-1))); 
  cut (eval h1 c (len+idx) = 
	(eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1))
	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))));
  cut (eval h1 c (len+idx) = 
	eval h0 a (len+idx-1) + (pow2 (bitweight t idx)) * eval h0 b (len-1)
	+ (pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1))
        + pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1))));
  cut (eval h1 c (len+idx) = eval h0 a (len+idx-1) + pow2 (bitweight t idx) * eval h0 b (len-1)  +
	  pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) +    	        
          pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)));
  cut (eval h1 c (len+idx) = 
	pow2 (bitweight t (len-1+idx)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1) + 
          pow2 (bitweight t idx) * eval h0 b (len-1)  +	        
          pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)));
  cut (eval h0 a (len+idx) = pow2 (bitweight t (len+idx-1)) * v (get h0 a (len+idx-1)) + eval h0 a (len+idx-1));
  cut (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight t idx) * eval h0 b (len-1)  
		+ pow2 (bitweight t (len-1+idx)) * v (get h0 b (len-1)))

#reset-options "--z3timeout 5"
#set-options "--lax" // OK

val multiplication_step_lemma_2:
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> b:bigint{live h0 b} -> c:bigint{live h1 c} -> idx:nat ->
  len:pos{len+idx <= length a /\ len <= length b /\ length a = length c} -> Lemma
    (requires ( eval h1 c (len+idx) = eval h0 a (len+idx) +  
                          pow2 (bitweight templ idx) * eval h0 b (len-1)  +	        
			  pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) ))
    (ensures (eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len))
let multiplication_step_lemma_2 h0 h1 a b c idx len = 
  auxiliary_lemma_1 idx (len-1); 
  cut (pow2 (bitweight templ (len-1+idx)) = pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) ); 
  paren_mul_left (pow2 (bitweight templ idx)) (pow2 (bitweight templ (len-1))) (v (get h0 b (len-1))); 
  cut (eval h1 c (len+idx) = eval h0 a (len+idx) 
			     + pow2 (bitweight templ idx) * eval h0 b (len-1)
			     + pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)) /\ True); 
  distributivity_add_right (pow2 (bitweight templ idx)) (eval h0 b (len-1)) (pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)));  
  cut (eval h0 b len = eval h0 b (len-1) + (pow2 (bitweight templ (len-1))) * v (get h0 b (len-1)) ); 
  cut (pow2 (bitweight templ (len-1+idx)) * v (get h0 b (len-1)) =
        pow2 (bitweight templ idx) * pow2 (bitweight templ (len-1)) * v (get h0 b (len-1))); 
  cut ( eval h1 c (len+idx) = eval h0 a (len+idx) + pow2 (bitweight templ idx) * eval h0 b len) 

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val multiplication_step_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> b:bigint{live h0 b} -> c:bigint{live h1 c} -> idx:nat ->
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

#reset-options

let partialEquality2 (ha:heap) (a:bigint{live ha a}) (hb:heap) (b:bigint{live hb b}) 
	             (len:nat) (len2:nat{len2 >= len /\ len2 <= length a /\ len2 <= length b}) : GTot Type0 =
  (forall (i:nat). {:pattern (v (get ha a i))}  (i < len2 /\ i >= len) ==> v (get ha a i) = v (get hb b i))

#set-options "--lax" // OK

val auxiliary_lemma_5: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint{live h1 b} -> c:int -> len:nat -> len2:nat{len2 >= len /\ len2 <= length b /\ len2 <= length a} ->
  Lemma
    (requires (eval h1 b len = eval h0 a len + c /\ partialEquality2 h1 b h0 a len len2))
    (ensures (eval h1 b len2 = eval h0 a len2 + c))
let rec auxiliary_lemma_5 h0 h1 a b c len len2 =
  match len2 - len with
  | 0 -> ()
  | _ -> 
     let t = templ in
     auxiliary_lemma_5 h0 h1 a b c len (len2-1); 
     cut (eval h1 b (len2-1) = eval h0 a (len2-1) + c); 
     cut (eval h1 b len2 = eval h1 b (len2-1) + (pow2 (bitweight t (len2-1))) * v (get h1 b (len2-1))); 
     cut (v (get h1 b (len2-1)) = v (get h0 a (len2-1)) /\ True); 
     cut (eval h1 b len2 = (eval h0 a (len2-1) + c) + (pow2 (bitweight t (len2-1))) * v (get h0 a (len2-1)));  
     cut (eval h1 b len2 = eval h0 a len2 + c)

let bound27 (h:heap) (b:bigint) : GTot Type0 = 
  live h b /\ length b >= norm_length
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 27)

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

val multiplication_step_0: a:bigint -> b:bigint -> ctr:u32{w ctr<norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  STL unit 
     (requires (fun h -> bound27 h a /\ norm h b /\ live h c /\ live h tmp /\ length c >= 2*norm_length -1
       /\ maxValue h c (length c) <= w ctr * pow2 53 ))
     (ensures (fun h0 _ h1 ->
       bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h0 tmp /\ length c >= 2*norm_length-1
       /\ modifies_1 tmp h0 h1 /\ scalarProduct h0 h1 norm_length a (get h0 b (w ctr)) tmp
       /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b (w ctr)) ))
let multiplication_step_0 a b ctr c tmp = 
  let h0 = HST.get() in
  let s = index b ctr in 
  cut (forall (n:nat). {:pattern (v (get h0 b n))} n < norm_length ==> v (get h0 b n) < pow2 27); 
  Math.Lib.pow2_exp_lemma 27 26;
  Math.Lib.pow2_increases_lemma 64 53;
  cut (forall (a:nat) (b:nat) (c:pos) (d:pos). (a < c /\ b < d) ==> (a * b < c * d)); 
  cut (forall (i:nat). i < norm_length ==> v (get h0 a i) * v s < pow2 27 * pow2 26);  
  scalar_multiplication tmp a s; admit()

#reset-options

val norm_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint{disjoint a tmp} -> Lemma
    (requires (norm h0 a /\ live h0 tmp /\ modifies_1 tmp h0 h1))
    (ensures (norm h1 a))
let norm_lemma h0 h1 a tmp = 
  eq_lemma_1 h0 h1 tmp a;
  ()

val bound27_lemma: h0:heap -> h1:heap -> a:bigint -> tmp:bigint{disjoint a tmp} -> Lemma
    (requires (bound27 h0 a /\ live h0 tmp /\ modifies_1 tmp h0 h1))
    (ensures (bound27 h1 a))
let bound27_lemma h0 h1 a tmp = 
  eq_lemma_1 h0 h1 tmp a;
  ()
  
val aux_lemma_4: unit -> Lemma (pow2 3 = 8)
let aux_lemma_4 () = ()

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

val aux_lemma_41: b:u64{v b < pow2 26} -> Lemma (forall (a:u64). (v a < pow2 27 /\ v b < pow2 26) ==> (v a * v b < pow2 53))
let aux_lemma_41 b = 
  cut (forall (a:u64). v a < pow2 27 ==> v a * v b < pow2 27 * pow2 26); 
  Math.Lib.pow2_exp_lemma 27 26;
  ()
  
#reset-options
#set-options "--lax" // OK

val aux_lemma_42: h:heap -> a:bigint{bound27 h a} -> z:u64{v z < pow2 26} -> Lemma (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)
let aux_lemma_42 h a z = 
  cut (forall (i:nat). {:pattern (get h a i)} i < norm_length ==> (v (get h a i) < pow2 27)); 
  aux_lemma_41 z; 
  Math.Lib.pow2_exp_lemma 27 26;
  cut (forall (i:nat). i < norm_length ==> v (get h a i) * v z < pow2 53)

#reset-options
#set-options "--lax" // OK

val aux_lemma_43: h1:heap -> c:bigint{live h1 c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{live h1 tmp} -> ctr:nat{ctr < norm_length} -> Lemma 
  (requires ((forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53)
    /\ (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53) ))
	(ensures (forall (i:nat). {:pattern (v (get h1 c (i+ctr)) + v (get h1 tmp i))} i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) <= (ctr+1) * pow2 53))
let aux_lemma_43 h1 c tmp ctr = 
  ()

let lemma_helper_10 (x:nat) : Lemma (requires (x <= norm_length))
				 (ensures  (x * pow2 53 <= pow2 3 * pow2 53))
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val multiplication_step_lemma_001: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> 
  Lemma
     (requires (
       bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h0 tmp
       /\ (length c >= 2*norm_length -1)
       /\ (maxValue h0 c (length c) <= ctr * pow2 53)
       /\ modifies_1 tmp h0 h1
       /\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp ))
     (ensures ( (live h1 c) /\ (live h1 tmp) /\ (ctr+norm_length <= length c)
       /\ willNotOverflow h1 ctr 0 norm_length 0 c tmp ))
let multiplication_step_lemma_001 h0 h1 a b ctr c tmp = 
  eq_lemma_1 h0 h1 tmp c;
  cut (live h1 c /\ v (get h0 b ctr) < pow2 (templ 0)); 
  cut (forall (i:nat). {:pattern (get h1 c)} i < norm_length ==> i+ctr < length c); 
  cut (forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> (v (get h0 a i) < pow2 27));
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  Math.Lib.pow2_exp_lemma 27 26;
  aux_lemma_42 h0 a (get h0 b ctr); 
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) < pow2 53); 
  maxValue_lemma h1 c;
  maxValue_eq_lemma h0 h1 c c (length c);
  cut (forall (i:nat). {:pattern (v (get h1 c (i+ctr)))} i < norm_length ==> v (get h1 c (i+ctr)) <= ctr * pow2 53); 
  aux_lemma_43 h1 c tmp ctr; 
  aux_lemma_4 ();
  lemma_helper_10 (ctr+1);
  Math.Lib.pow2_exp_lemma 3 53;
  Math.Lib.pow2_increases_lemma 64 56;
  cut((ctr+1) * pow2 53 < pow2 platform_wide);
  cut (forall (i:nat). i < norm_length ==> v (get h1 c (i+ctr)) + v (get h1 tmp i) < pow2 64)

#reset-options

val aux_lemma_5: ctr:nat -> Lemma (ctr * pow2 53 <= (ctr+1) * pow2 53)
let aux_lemma_5 ctr = ()

val aux_lemma_51: ctr:nat -> Lemma (ctr * pow2 53 + pow2 53 = (ctr+1) * pow2 53)
let aux_lemma_51 ctr = ()

let lemma_helper_20 () : Lemma  (forall (a:nat) (b':nat) (c:nat) (d:nat). (a < c /\ b' < d) ==> a * b' < c * d)
  = ()

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

val max_value_lemma_1: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (
      bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c
      /\ modifies_1 tmp h0 h1 /\ length c >= 2 * norm_length - 1
      /\ (maxValue h0 c (length c) <= ctr * pow2 53)
      /\ (forall (i:nat). {:pattern (v (get h2 c (i+ctr)))}
	  i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))) 
      /\ (forall (i:nat). {:pattern (v (get h2 c i))} ((i < ctr \/ i >= norm_length + ctr) /\ i < length c) ==> v (get h2 c i) = v (get h0 c i)) ))
    (ensures (bound27 h0 a /\ norm h0 b /\ live h2 c /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53 ))
let max_value_lemma_1 h0 h1 h2 a b ctr c tmp =
  cut(forall (i:nat). {:pattern (v (get h0 a i))} i < norm_length ==> v (get h0 a i) < pow2 27);
  cut(forall (i:nat). {:pattern (v (get h0 b i))} i < norm_length ==> v (get h0 b i) < pow2 26);
  maxValue_lemma h0 c;
  cut (forall (i:nat). {:pattern (v (get h0 c i))} i < length c ==> v (get h0 c i) <= maxValue h0 c (length c)) ;
  cut (forall (i:nat). {:pattern (v (get h0 c (i+ctr)))} i < norm_length ==> v (get h0 c (i+ctr)) <= maxValue h0 c (length c));
  lemma_helper_20 ();
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

let eq_lemma_0 h0 h1 (a:bigint) : Lemma 
  (requires (modifies_0 h0 h1 /\ live h0 a))
  (ensures  (live h0 a /\ live h1 a /\ (forall (i:nat). i < length a ==> get h1 a i = get h0 a i)))
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val max_value_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr < norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  Lemma
    (requires (
      bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h2 c /\ live h1 c /\ live h0 tmp
      /\ modifies_1 tmp h0 h1 /\ length c >= 2 * norm_length - 1
      /\ maxValue h0 c (length c) <= ctr * pow2 53
      /\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
      /\ isSum h1 h2 ctr 0 norm_length 0 c tmp
      /\ equalSub h1 c 0 h2 c 0 ctr
      /\ equalSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr) ))
    (ensures (bound27 h0 a /\ norm h0 b /\ live h2 c /\ maxValue h2 c (length c) <= (ctr+1) * pow2 53))
let max_value_lemma h0 h1 h2 a b ctr c tmp =
  cut(forall (i:nat). {:pattern (v (get h1 tmp i))} i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr)); 
  cut(forall (i:nat). {:pattern (v (get h2 c (i+ctr)))} i < norm_length ==> v (get h2 c (i+ctr)) = v (get h1 c (i+ctr)) + v (get h1 tmp i));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c (0+i)) = v (get h1 c (0+i)));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < length c - norm_length - ctr ==> v (get h2 c ((norm_length+ctr)+i)) = v (get h1 c ((norm_length+ctr)+i)));
  eq_lemma_1 h0 h1 tmp c;
  cut (forall (i:nat). {:pattern (v (get h1 c i))} i < length c ==> v (get h1 c i) = v (get h0 c i));
  cut (forall (i:nat). {:pattern (v (get h1 tmp i))}
    i < norm_length ==> v (get h1 tmp i) = v (get h0 a i) * v (get h0 b ctr));
  cut(forall (i:nat). i < norm_length ==> v (get h2 c (i+ctr)) = v (get h0 c (i+ctr)) + (v (get h0 a i) * v (get h0 b ctr))); 
  cut (forall (i:nat). {:pattern (v (get h2 c i))} (i >= norm_length + ctr /\ i < length c) ==> v (get h2 c ((norm_length+ctr)+(i-norm_length-ctr))) = v (get h0 c ((norm_length+ctr)+(i-norm_length-ctr))));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c (0+i)) = v (get h0 c (0+i)));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} (i >=norm_length + ctr /\ i < length c) ==> v (get h2 c i) = v (get h0 c i));
  cut (forall (i:nat). {:pattern (v (get h2 c i))} i < ctr ==> v (get h2 c i) = v (get h0 c i));
  max_value_lemma_1 h0 h1 h2 a b ctr c tmp

#reset-options
#set-options "--lax" // OK

let lemma_modifies_2_refl a b h0 h1 : Lemma (requires (modifies_2 a b h0 h1))
					    (ensures  (modifies_2 b a h0 h1))
  = ()

val standardized_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint{disjoint a c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint c tmp} -> Lemma
    (requires (bound27 h0 a /\ live h0 c /\ live h1 tmp /\ live h1 c /\ modifies_1 tmp h0 h1
      /\ live h0 tmp /\ (modifies_1 c h1 h2) ))
     (ensures (bound27 h0 a /\ bound27 h2 a /\ live h0 c /\ live h1 tmp /\ live h2 tmp
       /\ modifies_2 c tmp h0 h2))
let standardized_lemma h0 h1 h2 a c tmp = 
  eq_lemma_1 h1 h2 c tmp; 
  eq_lemma_1 h0 h1 tmp c;
  lemma_modifies_1_1 tmp c h0 h1 h2;
  lemma_modifies_2_refl tmp c h0 h2;
  assert(modifies_2 tmp c h0 h2);
  eq_lemma_2 h0 h2 c tmp a;
  ()

val standardized_lemma2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> c:bigint{disjoint a c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint c tmp} -> Lemma
    (requires (norm h0 a /\ live h0 c /\ live h0 tmp /\ live h1 tmp /\ live h1 c /\ modifies_1 tmp h0 h1
	/\ (modifies_1 c h1 h2) ))
     (ensures (norm h0 a /\ norm h2 a /\ live h0 c /\ live h1 tmp /\ live h2 tmp
       /\ modifies_2 c tmp h0 h2))
let standardized_lemma2 h0 h1 h2 a c tmp = 
  eq_lemma_1 h1 h2 c tmp; 
  eq_lemma_1 h0 h1 tmp c;
  lemma_modifies_1_1 tmp c h0 h1 h2;
  lemma_modifies_2_refl tmp c h0 h2;
  assert(modifies_2 tmp c h0 h2);
  eq_lemma_2 h0 h2 c tmp a;
  ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TOOD

val multiplication_step_lemma_02: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr<norm_length} -> c:bigint{disjoint a c /\ disjoint b c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
     (requires (bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h1 tmp /\ live h1 c /\ live h0 tmp 
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h0 c (length c) <= ctr * pow2 53
	// After fscalar
	/\ modifies_1 tmp h0 h1
	/\ scalarProduct h0 h1 norm_length a (get h0 b ctr) tmp
        /\ eval h1 tmp norm_length = eval h0 a norm_length * v (get h0 b ctr)
 	// After fsum
	/\ live h2 c /\ live h2 tmp 
	/\ modifies_1 c h1 h2
	/\ isSum h1 h2 ctr 0 norm_length 0 c tmp
	/\ equalSub h1 c 0 h2 c 0 ctr
	/\ equalSub h1 c (norm_length+ctr) h2 c (norm_length+ctr) (length c - norm_length - ctr)
	)) 
     (ensures (bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h2 c  /\ live h0 tmp /\ live h2 tmp
       /\ bound27 h2 a /\ norm h2 b
       /\ length c >= 2 * norm_length - 1 /\ modifies_2 c tmp h0 h2
       /\ (maxValue h2 c (length c) <= (ctr+1) * pow2 53)
       /\ (eval h2 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a norm_length * v (get h0 b ctr)) ))
let multiplication_step_lemma_02 h0 h1 h2 a b ctr c tmp =
  cut (forall (i:nat). i < ctr ==> v (get h1 c (0+i)) = v (get h2 c (0+i)));
  cut (forall (i:nat). i < length c - norm_length - ctr ==> v (get h1 c ((norm_length+ctr)+i)) = v (get h2 c ((norm_length+ctr)+i)));
  eval_partial_eq_lemma h1 h2 c c (norm_length+ctr) (2*norm_length-1);
  eq_lemma_1 h0 h1 tmp c;
  cut (forall (i:nat). i < 2*norm_length-1 ==> get h1 c i = get h0 c i);
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

let lemma_helper_70 h0 h1 ctr (c:bigint{length c >= norm_length + w ctr}) : Lemma
  (requires (isNotModified h0 h1 (w ctr) norm_length 0 c))
  (ensures  (equalSub h0 c 0 h1 c 0 (w ctr)
    /\ equalSub h0 c (norm_length+w ctr) h1 c (norm_length+w ctr) (length c - norm_length - w ctr) ))
  = ()

#reset-options "--z3timeout 10"
#set-options "--lax" // OK

val multiplication_step_p1: a:bigint -> b:bigint -> ctr:u32{w ctr<norm_length} -> 
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} ->  STL unit 
     (requires (fun h -> (bound27 h a) /\ (norm h b) /\ (live h c) /\ (live h tmp)
        /\ (maxValue h c (length c) <= w ctr * pow2 53)
	/\ (eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr)) ))
     (ensures (fun h0 u h1 -> (bound27 h0 a) /\ (norm h0 b) /\ (live h0 c) /\ (live h0 tmp)       
       /\ (bound27 h1 a) /\ (norm h1 b) /\ (live h1 c) /\ (live h1 tmp) /\ (modifies_2 c tmp h0 h1)
       /\ (maxValue h0 c (length c) <= w ctr * pow2 53)
       /\ (maxValue h1 c (length c) <= (w ctr+1) * pow2 53)
       /\ (eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr))
       /\ (eval h1 c (2*norm_length-1) = eval h0 c (2*norm_length-1) + pow2 (bitweight templ (w ctr)) * eval h0 a norm_length * v (get h0 b (w ctr))) ))
let multiplication_step_p1 a b ctr c tmp =
  let h0 = HST.get() in
  multiplication_step_0 a b ctr c tmp;
  let h1 = HST.get() in
  eq_lemma_1 h0 h1 tmp a;
  eq_lemma_1 h0 h1 tmp b;  
  eq_lemma_1 h0 h1 tmp c;  
  multiplication_step_lemma_001 h0 h1 a b (w ctr) c tmp; 
  fsum_index c ctr tmp 0ul nlength 0ul;
  let h2 = HST.get() in 
  eq_lemma_1 h1 h2 c a;
  eq_lemma_1 h1 h2 c b;
  eq_lemma_1 h1 h2 c tmp;
  lemma_helper_70 h1 h2 ctr c;
  multiplication_step_lemma_02 h0 h1 h2 a b (w ctr) c tmp

#reset-options

let helper_lemma_61 (a:int) (b:int) (c:int) (d:int) : Lemma (a*b*c+d = d+c*a*b) = ()

val helper_lemma_6: h0:heap -> h1:heap -> a:bigint -> b:bigint -> ctr:nat{ctr < norm_length} -> 
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2 * norm_length - 1} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
     (requires (bound27 h0 a /\ norm h0 b /\ live h0 c))
    (ensures (bound27 h0 a /\ norm h0 b /\ live h0 c
       /\ eval h0 c (2*norm_length-1) + pow2 (bitweight templ ctr) * eval h0 a (norm_length) * v (get h0 b ctr)  = eval h0 a (norm_length) * v (get h0 b ctr) * pow2 (bitweight templ ctr) + eval h0 c (2*norm_length-1) ))
let helper_lemma_6 h0 h1 a b ctr c tmp = 
  helper_lemma_61 (eval h0 a norm_length) (v (get h0 b ctr)) (pow2 (bitweight templ ctr)) (eval h0 c (2*norm_length-1))

val multiplication_step: a:bigint -> b:bigint -> ctr:u32{w ctr < norm_length} -> 
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit  
     (requires (fun h -> bound27 h a /\ norm h b /\ live h c /\ live h tmp
	/\ maxValue h c (length c) <= w ctr * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (w ctr)  ))
     (ensures (fun h0 u h1 -> bound27 h0 a /\ bound27 h1 a /\ norm h0 b /\ norm h1 b
       /\ live h0 c /\ live h1 c  /\ live h0 tmp /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       /\ maxValue h0 c (length c) <= w ctr * pow2 53
       /\ maxValue h1 c (length c) <= (w ctr+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (w ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (w ctr)) * pow2 (bitweight templ (w ctr)) + eval h0 c (2*norm_length-1) ))
let multiplication_step a b ctr c tmp =
  let h0 = HST.get() in
  multiplication_step_p1 a b ctr c tmp;
  let h1 = HST.get() in
  helper_lemma_6 h0 h1 a b (w ctr) c tmp;
  ()

#reset-options "--z3timeout 20"

val multiplication_step_lemma_03: h0:heap -> h1:heap -> a:bigint{norm h0 a} -> 
  b:bigint{norm h0 b} -> ctr:pos{ctr<=norm_length} -> 
  c:bigint{live h1 c /\ length c >= 2*norm_length-1} -> Lemma 
    (requires (eval h1 c (2*norm_length-1) = (eval h0 a (norm_length) * v (get h0 b (norm_length - ctr))) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 a (norm_length) * eval h0 b (norm_length - ctr) ))
    (ensures ( eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr + 1)))
let multiplication_step_lemma_03 h0 h1 a b ctr c = 
  let t = templ in 
  paren_mul_left (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight t (norm_length - ctr))); 
  cut (eval h1 c (2*norm_length-1) = eval h0 a norm_length * v (get h0 b (norm_length - ctr)) * pow2 (bitweight t (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) );
  cut (eval h1 c (2*norm_length-1) = eval h0 a norm_length * pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 a norm_length * eval h0 b (norm_length - ctr) );
  distributivity_add_right (eval h0 a norm_length) (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr))) (eval h0 b (norm_length - ctr));
  cut (eval h1 c (2*norm_length-1) = eval h0 a norm_length * (pow2 (bitweight t (norm_length - ctr)) * v (get h0 b (norm_length - ctr)) + eval h0 b (norm_length - ctr)))

#reset-options

val helper_lemma_12: a:nat -> v:nat -> p:nat -> b:nat -> Lemma (a * v * p + (a * b) = a * (p * v + b))
let helper_lemma_12 a v p b = ()

#reset-options "--z3timeout 20"
#set-options "--lax" // TODO

val multiplication_aux_lemma: h0:heap -> h1:heap -> a:bigint -> b:bigint -> 
  ctr:pos{ctr <= norm_length} ->  c:bigint{disjoint a c /\ disjoint b c} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
    (requires (bound27 h0 a /\ bound27 h1 a /\ norm h0 b /\ norm h1 b 
       /\ live h0 c /\ live h1 c /\ live h0 tmp /\ live h1 tmp
       /\ length c >= 2 * norm_length - 1 /\ modifies_2 c tmp h0 h1
       /\ maxValue h0 c (length c) <= (norm_length - ctr) * pow2 53
       /\ maxValue h1 c (length c) <= ((norm_length - ctr)+1) * pow2 53
       /\ eval h0 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length - ctr)
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * v (get h0 b (norm_length - ctr)) * pow2 (bitweight templ (norm_length - ctr)) + eval h0 c (2*norm_length-1) ))
    (ensures (bound27 h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp
	/\ length c >= 2 * norm_length - 1
	/\ maxValue h1 c (length c) <= (norm_length - ctr + 1) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - ctr + 1) ))
let multiplication_aux_lemma h0 h1 a b ctr c tmp =
  eq_lemma_2 h0 h1 c tmp a;
  eq_lemma_2 h0 h1 c tmp b;
  eval_eq_lemma h0 h1 a a norm_length;
  eval_eq_lemma h0 h1 b b norm_length;
  eval_eq_lemma h0 h1 b b (norm_length - ctr);
  eval_eq_lemma h0 h1 b b (norm_length - ctr + 1); 
  cut((norm_length - ctr)+1 = norm_length - ctr + 1); 
  cut(eval h0 a norm_length = eval h1 a norm_length);
  cut(eval h0 b (norm_length-ctr) = eval h1 b (norm_length - ctr));
  cut(eval h0 b (norm_length - ctr + 1) = eval h1 b (norm_length - ctr + 1));
  cut(v (get h0 b (norm_length - ctr)) = v (get h1 b (norm_length - ctr)));
  helper_lemma_12 (eval h0 a norm_length) (v (get h0 b (norm_length - ctr))) (pow2 (bitweight templ (norm_length - ctr))) (eval h0 b (norm_length - ctr))

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

val multiplication_aux_lemma_2: h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint -> 
  ctr:nat{ctr <= norm_length} -> c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma 
    (requires (bound27 h0 a /\ norm h0 b /\ live h1 c /\ live h1 tmp /\ live h0 tmp /\ live h0 c
       /\ bound27 h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp
       /\ bound27 h2 a /\ norm h2 b /\ live h2 c /\ live h2 tmp
       /\ modifies_2 c tmp h1 h2 /\ modifies_2 c tmp h0 h1
       /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length) ))
    (ensures (bound27 h0 a /\ norm h0 b /\ live h1 c /\ bound27 h2 a /\ norm h2 b /\ live h2 c
       /\ modifies_2 c tmp h0 h2
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length) ))
let multiplication_aux_lemma_2 h0 h1 h2 a b ctr c tmp =
  lemma_modifies_2_trans c tmp h0 h1 h2;
  eq_lemma_2 h0 h1 c tmp a;
  eq_lemma_2 h0 h1 c tmp b;
  eval_eq_lemma h0 h1 a a norm_length; 
  eval_eq_lemma h0 h1 b b norm_length

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val multiplication_aux: a:bigint -> b:bigint -> ctr:u32{w ctr<=norm_length} -> 
  c:bigint{disjoint a c /\ disjoint b c /\ length c >= 2*norm_length-1} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> STL unit
     (requires (fun h -> bound27 h a /\ norm h b /\ live h c /\ live h tmp
	/\ maxValue h c (length c) <= (norm_length - w ctr) * pow2 53
	/\ eval h c (2*norm_length-1) = eval h a (norm_length) * eval h b (norm_length - w ctr) ))
     (ensures (fun h0 u h1 -> bound27 h0 a /\ norm h0 b /\ live h0 c /\ live h0 tmp
       /\ bound27 h1 a /\ norm h1 b /\ live h1 c /\ live h1 tmp /\ modifies_2 c tmp h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let rec multiplication_aux a b ctr c tmp = 
  let h0 = HST.get() in
  if U32.eq ctr 0ul then admit()
  else begin
    multiplication_step a b (nlength -| ctr) c tmp; 
    let h1 = HST.get() in    
    multiplication_aux_lemma h0 h1 a b (w ctr) c tmp;
    multiplication_aux a b (ctr-|1ul) c tmp; 
    let h2 = HST.get() in
    multiplication_aux_lemma_2 h0 h1 h2 a b (w ctr) c tmp;
    ()
  end

#reset-options

val helper_lemma_13: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (bound27 h0 a /\ modifies_0 h0 h1))
    (ensures (bound27 h0 a /\ bound27 h1 a /\ live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_13 h0 h1 a =  
  eq_lemma_0 h0 h1 a;
  eval_eq_lemma h0 h1 a a norm_length;
  ()

val helper_lemma_131: h0:heap -> h1:heap -> a:bigint ->
  Lemma 
    (requires (norm h0 a /\ modifies_0 h0 h1))
    (ensures (norm h0 a /\ norm h1 a /\ live h1 a /\ eval h0 a norm_length = eval h1 a norm_length))
let helper_lemma_131 h0 h1 a =  
  eq_lemma_0 h0 h1 a;
  eval_eq_lemma h0 h1 a a norm_length;
  ()

val helper_lemma_15: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> Lemma
    (requires (live h0 c /\ null h0 c /\ modifies_0 h0 h1))
    (ensures (live h1 c /\ null h1 c /\ maxValue h1 c (length c) = 0 /\ eval h1 c (2*norm_length-1) = 0))
let helper_lemma_15 h0 h1 c =
  eq_lemma_0 h0 h1 c;
  eval_null h1 c (2*norm_length - 1); 
  max_value_of_null_lemma h1 c (length c)
	 
val multiplication_lemma_1: h0:heap -> h1:heap -> c:bigint{length c >= 2*norm_length-1} -> 
  a:bigint{disjoint c a} ->  b:bigint{disjoint c b} -> Lemma
     (requires (bound27 h0 a /\ norm h0 b /\ live h0 c /\ null h0 c /\ modifies_0 h0 h1))
     (ensures (bound27 h1 a /\ norm h1 b /\ live h1 c /\ null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length) )) 
let multiplication_lemma_1 h0 h1 c a b =
  helper_lemma_13 h0 h1 a;
  helper_lemma_131 h0 h1 b;
  helper_lemma_15 h0 h1 c;   
  cut(eval h1 b 0 = 0)

#reset-options "--z3timeout 100"
#set-options "--lax" // OK
val helper_lemma_14: h0:heap -> h1:heap -> h2:heap -> c:bigint -> tmp:bigint{disjoint c tmp} ->
  Lemma
    (requires (live h0 c /\ live h2 c /\ ~(contains h0 tmp) /\ modifies_0 h0 h1 /\ live h1 tmp /\ modifies_2 c tmp h1 h2))
    (ensures ((frameOf tmp = frameOf c /\ modifies_1 c h0 h2)
	      \/ (frameOf tmp <> frameOf c /\ modifies_buf (frameOf c) (only c) h0 h2
		  /\ modifies_buf (frameOf tmp) Set.empty h0 h2)))
let helper_lemma_14 h0 h1 h2 c tmp = 
  if frameOf tmp = frameOf c then begin
    let rid = frameOf tmp in
    cut(modifies_buf rid Set.empty h0 h1);
    cut(modifies_buf rid (only c ++ tmp) h1 h2);
    cut(~(contains h0 tmp));
    cut(modifies_buf rid (only c) h0 h2)
  end
  else ()

#reset-options
#set-options "--lax" // OK

val multiplication_lemma_2: h0:heap -> h1:heap -> h2:heap -> c:bigint{length c >= 2*norm_length-1} -> 
  a:bigint{disjoint c a} -> b:bigint{disjoint c b} -> 
  tmp:bigint{disjoint a tmp /\ disjoint b tmp /\ disjoint c tmp} -> Lemma
     (requires (bound27 h0 a /\ norm h0 b /\ live h0 c /\ null h0 c
	/\ modifies_0 h0 h1 /\ ~(contains h0 tmp) /\ live h1 tmp
	/\ bound27 h1 a /\ norm h1 b /\ live h1 c /\ null h1 c
	/\ maxValue h1 c (length c) <= (norm_length - norm_length) * pow2 53
	/\ eval h1 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length - norm_length)
        /\ bound27 h2 a /\ norm h2 b /\ live h2 c
        /\ modifies_2 c tmp h1 h2
        /\ eval h2 c (2*norm_length-1) = eval h1 a (norm_length) * eval h1 b (norm_length)
        /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
     (ensures (bound27 h0 a /\ norm h0 b /\ live h0 c /\ bound27 h2 a /\ norm h2 b /\ live h2 c
       (* /\ modifies_1 c h0 h2 *)
       /\ ((frameOf tmp = frameOf c /\ modifies_1 c h0 h2)
	      \/ (frameOf tmp <> frameOf c /\ modifies_buf (frameOf c) (only c) h0 h2
		  /\ modifies_buf (frameOf tmp) Set.empty h0 h2))
       /\ eval h2 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h2 c (length c) <= norm_length * pow2 53 ))
let multiplication_lemma_2 h0 h1 h2 c a b tmp =
  helper_lemma_14 h0 h1 h2 c tmp; 
  helper_lemma_13 h0 h1 a;
  helper_lemma_13 h0 h1 b

(* TODO: move a generalized version to buffer *)
let eq_lemma_fresh h0 h1 a : Lemma
  (requires (live h0 a /\ fresh_frame h0 h1))
  (ensures  (live h0 a /\ live h1 a /\ (forall (i:nat). {:pattern (get h1 a i)} i < length a 
			    ==> get h1 a i = get h0 a i)))
  = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO, need lemmas for the pop

(* Code : core multiplication function *)
val multiplication: c:bigint{length c >= 2*norm_length-1} -> a:bigint{disjoint c a} -> 
  b:bigint{disjoint c b} -> STL unit
     (requires (fun h -> bound27 h a /\ norm h b /\ live h c /\ null h c))
     (ensures (fun h0 u h1 -> bound27 h0 a /\ norm h0 b /\ live h0 c /\ bound27 h1 a /\ norm h1 b /\ live h1 c
       /\ modifies_1 c h0 h1
       /\ eval h1 c (2*norm_length-1) = eval h0 a (norm_length) * eval h0 b (norm_length)
       /\ maxValue h1 c (length c) <= norm_length * pow2 53 ))
let multiplication c a b =
  let h_init = HST.get() in
  push_frame ();
  let h0 = HST.get() in
  eq_lemma_fresh h_init h0 a;
  eq_lemma_fresh h_init h0 b;
  eq_lemma_fresh h_init h0 c;
  let tmp = create (U64.of_string "0") nlength in 
  let h1 = HST.get() in
  eq_lemma_0 h0 h1 a; 
  eq_lemma_0 h0 h1 b; 
  eq_lemma_0 h0 h1 c;
  multiplication_lemma_1 h0 h1 c a b;
  multiplication_aux a b nlength c tmp; 
  let h2 = HST.get() in 
  multiplication_lemma_2 h0 h1 h2 c a b tmp;
  pop_frame ();
  ()

#reset-options

(*** Modulo ***)

assume val prime_modulo_lemma: unit -> Lemma (pow2 130 % (reveal prime) = 5)

val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a)) 
  [SMTPat (a % b)]
let modulo_lemma a b = ()

let satisfiesModuloConstraints (h:heap) (b:bigint) : GTot Type0 = 
  live h b /\ length b >= 2*norm_length-1 && maxValue h b (2*norm_length-1) * 6 < pow2 62

(* Just like the other operators *)
val op_At_Less_Less: a:u64 -> s:u32{w s <= 32} -> Tot (b:u64{v b = (pow2 (w s) * v a) % pow2 64})
let op_At_Less_Less a s = admit(); UInt64.op_Less_Less_Hat a s 

val times_5: x:u64{5 * v x < pow2 64} -> Tot (y:u64{v y = 5 * v x})
let times_5 x = 
  let z = x @<< 2ul in
  x +^ z
  
let reducible (h:heap) (b:bigint) (ctr:nat{ctr < norm_length-1}) : GTot Type0 =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (get h b (i+norm_length))}
      i <= ctr ==> v (get h b i) + 5 * v (get h b (i+norm_length)) < pow2 64)

let times5 (h0:heap) (h1:heap) (b:bigint) (ctr:nat{ctr < norm_length - 1}) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)}
       i <= ctr ==> v (get h1 b i) = v (get h0 b i) + 5 * (v (get h0 b (i+norm_length))))

let untouched (h0:heap) (h1:heap) (b:bigint) (ctr:nat) : GTot Type0 = 
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==> 
      get h0 b i = get h1 b i)

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val pow2_bitweight_lemma_1: ctr:pos -> Lemma (requires (True))
    (ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let rec pow2_bitweight_lemma_1 ctr =
  match ctr with
  | 1 -> ()
  | _ -> 
    cut(ctr-1+norm_length = ctr+norm_length-1 /\ ctr+norm_length-1 = (ctr-1) + norm_length
	/\ (ctr+norm_length-1)-1=ctr+norm_length-2); 
    pow2_bitweight_lemma_1 (ctr-1); 
    cut (pow2 (bitweight templ (ctr+norm_length-2)) = pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    cut (bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 26); 
    Math.Lib.pow2_exp_lemma (bitweight templ (ctr+norm_length-2)) 26;
    cut(pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * pow2 (bitweight templ (ctr+norm_length-2))); 
    cut(pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * (pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)));  
    paren_mul_right (pow2 26) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
    cut (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 26 * pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    Math.Lib.pow2_exp_lemma 26 (bitweight templ (ctr-2));
    cut (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (26 + bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)) 

#reset-options

val bitweight_norm_length_lemma: unit -> Lemma 
  (requires (True)) 
  (ensures (bitweight templ norm_length = 130))
  [SMTPat (bitweight templ norm_length)]
let bitweight_norm_length_lemma () = 
  ()

(* TODO: express in terms of general % property *)
assume val helper_lemma_5: a:nat -> b:nat -> c:nat -> p:pos -> Lemma (ensures ( (a*b+c) % p = ((a % p) * b + c)%p))

val lemma_aux_0: a:int -> b:int -> c:int -> d:int -> Lemma (a * b + c - (a * (b + 5 * d) + c) = - 5 * a * d)
let lemma_aux_0 a b c d = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO

val freduce_degree_lemma_2: h0:heap -> h1:heap -> b:bigint{live h1 b /\ live h0 b /\ length b >= 2 * norm_length - 1} -> ctr:pos{ctr < norm_length-1} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
	/\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma_2 h0 h1 b ctr =
  let prime = reveal prime in 
  cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); 
  cut (eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length)); 
  pow2_bitweight_lemma_1 (ctr+1); 
  cut(pow2 (bitweight templ (norm_length+ctr)) = pow2 130 * pow2 (bitweight templ ctr)); 
  paren_mul_left (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  paren_mul_right (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  cut (eval h0 b (norm_length+1+ctr) = (pow2 130 * pow2 (bitweight templ ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)); 
  helper_lemma_5 (pow2 130) (pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) (eval h0 b (norm_length+ctr)) prime; 
  cut (eval h0 b (norm_length+1+ctr) % prime = ((pow2 130 % prime) * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  prime_modulo_lemma (); 
  cut (eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  eval_eq_lemma h0 h1 b b ctr; 
  cut (eval h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval h0 b ctr); 
  cut (eval h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (get h0 b ctr) + 5 * v (get h0 b (norm_length+ctr))) + eval h0 b ctr); 
  lemma_aux_0 (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (eval h0 b ctr) (v (get h0 b (norm_length+ctr)));
  cut (eval h0 b (ctr+1) - eval h1 b (ctr+1) = - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) /\ True); 
  distributivity_add_right (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (5 * v (get h0 b (norm_length+ctr))); 
  eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr); 
  cut (eval h0 b (norm_length+ctr) - eval h0 b (ctr+1) = eval h1 b (norm_length+ctr) - eval h1 b (ctr+1) /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) + eval h0 b (ctr+1) - eval h1 b (ctr+1)) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (eval h1 b (norm_length+ctr) ) % prime /\ True)

#reset-options "--z3timeout 50"
#set-options "--lax" // OK

val freduce_degree_lemma:
  h0:heap -> h1:heap -> b:bigint{live h1 b /\ live h0 b /\ length b >= 2 * norm_length - 1} -> 
  ctr:nat{ctr < norm_length-1} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))  
let freduce_degree_lemma h0 h1 b ctr =
  let prime = reveal prime in
  if ctr = 0 then (
    helper_lemma_5 (pow2 130) (v (get h0 b norm_length)) (eval h0 b norm_length) prime;
    prime_modulo_lemma ();
    cut(eval h0 b 1 = v (get h0 b 0) /\ eval h1 b 1 = v (get h0 b 0) + 5 * v (get h0 b norm_length)); 
    eval_partial_eq_lemma h0 h1 b b 1 norm_length;
    cut(eval h1 b norm_length - eval h1 b 1 = eval h0 b norm_length - eval h0 b 1)
  ) else (
    freduce_degree_lemma_2 h0 h1 b ctr
  )

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO

val freduce_degree': 
  b:bigint -> ctr:u32{w ctr < norm_length - 1} -> STL unit 
    (requires (fun h -> reducible h b (w ctr))) 
    (ensures (fun h0 _ h1 -> untouched h0 h1 b (w ctr) /\ times5 h0 h1 b (w ctr)
      /\ eval h1 b (norm_length) % reveal prime = eval h0 b (norm_length+1+w ctr) % reveal prime
      /\ modifies_1 b h0 h1))
let rec freduce_degree' b ctr' =
  let h0 = HST.get() in
  if U32.eq ctr' 0ul then begin
    let b5ctr = index b (0ul+|nlength) in 
    let bctr = index b 0ul in
    let b5ctr = times_5 b5ctr in
    let bctr = bctr +^ b5ctr in 
    upd b 0ul bctr;
    let h1 = HST.get() in
    freduce_degree_lemma h0 h1 b 0;
    cut (eval h0 b (norm_length+1+0) % reveal prime = eval h1 b (norm_length+0) % reveal prime);
    cut (eval h0 b (norm_length+1) % reveal prime = eval h1 b (norm_length+0) % reveal prime)
    end
  else begin
    let ctr = ctr' in
    let b5ctr = index b (ctr +| nlength) in 
    let bctr = index b ctr in
    let b5ctr = times_5 b5ctr in
    let bctr = bctr +^ b5ctr in 
    upd b ctr bctr;
    let h1 = HST.get() in
    freduce_degree_lemma h0 h1 b (w ctr); 
    cut (eval h0 b (norm_length+1+w ctr) % reveal prime = eval h1 b (norm_length+w ctr) % reveal prime);
    cut(reducible h1 b (w ctr-1)); 
    freduce_degree' b (ctr-|1ul); 
    let h2 = HST.get() in 
    cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > w ctr /\ i < 2*norm_length-1) ==>
	   v (get h1 b i) = v (get h0 b i)); 
    cut(untouched h0 h2 b (w ctr));
    cut (times5 h0 h2 b (w ctr)) ;
    ()
  end

#reset-options

val aux_lemma_4': h:heap -> b:bigint -> Lemma
  (requires (satisfiesModuloConstraints h b))
  (ensures (reducible h b (norm_length-2)))
let aux_lemma_4' h b =
  maxValue_lemma_aux h b (2*norm_length-1);
  Math.Lib.pow2_increases_lemma 64 62;
  ()
  
val aux_lemma_5': h0:heap -> h1:heap -> b:bigint -> Lemma
  (requires (live h0 b /\ satisfiesModuloConstraints h0 b /\ times5 h0 h1 b (norm_length-2)
      /\ untouched h0 h1 b (norm_length-2)))
  (ensures (live h0 b /\ satisfiesModuloConstraints h0 b /\ times5 h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (get h1 b i) < pow2 62)))
let aux_lemma_5' h0 h1 b = 
  maxValue_lemma_aux h0 b (2*norm_length-1)

val freduce_degree: b:bigint -> STL unit 
  (requires (fun h -> live h b /\ satisfiesModuloConstraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfiesModuloConstraints h0 b
    /\ modifies_1 b h0 h1
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> 
	v (get h1 b i) < pow2 62)
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
  let h0 = HST.get() in
  aux_lemma_4' h0 b; 
  freduce_degree' b (nlength-|2ul); 
  let h1 = HST.get() in
  aux_lemma_5' h0 h1 b

val pow2_bitweight_lemma: ctr:nat -> Lemma 
    (requires (True)) 
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr)))
let pow2_bitweight_lemma ctr =
  Math.Lib.pow2_exp_lemma (bitweight templ ctr) (templ ctr);
  ()

val helper_lemma_2: pb:nat -> pc:pos -> a0:nat -> b:nat ->
  Lemma  (ensures ((pb*pc) * a0/pc + (pb * (a0 % pc) + b) = pb * a0 + b))
let helper_lemma_2 pb pc a0 b = ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO

val eval_carry_lemma: ha:heap -> a:bigint{live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint{live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> Lemma
    (requires (v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr =
  eval_eq_lemma ha hb a b ctr;
  cut(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + eval hb b (ctr+1)); 
  cut(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (get hb b ctr) + eval hb b ctr));  
  cut(eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr)); 
  distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (get ha a (ctr+1))) (v (get ha a ctr) / pow2 (templ ctr));
  cut(eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  pow2_bitweight_lemma ctr; 
  cut(eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (get ha a ctr)) (eval hb b ctr); 
  cut( eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (get ha a ctr) + eval hb b ctr));  
  cut(eval hb b (ctr+2) = eval ha a (ctr+2)); 
  eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1)

#reset-options

val helper_lemma_4: a:nat -> b:nat -> c:pos -> size:pos{size > c} ->
  Lemma (requires (a < pow2 (size-1) /\ b < pow2 (size-c)))
	(ensures (a + b < pow2 size))
let helper_lemma_4 a b c size = 
  if size-1 > size - c then begin
    Math.Lib.pow2_increases_lemma (size-1) (size-c) ;
    ()
    end
  else ()

val auxiliary_lemma_1': bip1:u64 -> c:u64 -> Lemma
    (requires (v bip1 < pow2 62 /\ v c < pow2 (64 - 26)))
    (ensures (v bip1 + v c < pow2 64)) 
let auxiliary_lemma_1' bip1 c =
  helper_lemma_4 (v bip1) (v c) 26 64

val auxiliary_lemma_2: bip1:u64 -> c:u64 -> Lemma
    (requires (v bip1 < pow2 26 /\ v c < pow2 15))
    (ensures (v bip1 + v c < pow2 27)) 
let auxiliary_lemma_2 bip1 c =
  helper_lemma_4 (v bip1) (v c) 12 27

(* TODO: move somewhere more appropriate *)
assume MaxUint32: FStar.UInt.max_int 32 = 4294967295

val op_At_Subtraction: a:u64 -> b:u64{v a >= v b} -> Tot (c:u64{v c = v a - v b})
let op_At_Subtraction a b = admit(); U64.op_Subtraction_Hat a b

val mod2_26: a:u64 -> Tot (b:u64{v b = v a % pow2 26})
let mod2_26 a = 
  admit(); // TODO
  let mask = shift_left 1uL 26ul in
  Math.Lib.pow2_increases_lemma 64 26;
  let mask = mask @- 1uL in
  let res = a &^ mask in
  (* SInt.ulogand_lemma_4 #64 a 26 mask; *)
  res

let carriable (h:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) : GTot Type0 =
  live h b /\ length b >= norm_length + 1  
  /\ (forall (i:nat). {:pattern (v (get h b i))}
      (i > ctr /\ i <= norm_length) ==> v (get h b i) < pow2 62)

let carried (h1:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) : GTot Type0 =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (get h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h1 b norm_length) < pow2 37)
  
let carried' (h1:heap) (b:bigint) (ctr:nat{ctr <= norm_length}) : GTot Type0 =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= ctr /\ i < norm_length) ==> v (get h1 b i) < pow2 (templ ctr))
  /\ v (get h1 b norm_length) < pow2 37
  
let untouched_2 (h0:heap) (h1:heap) (b:bigint) (ctr:nat) : GTot Type0 =
  live h0 b /\ live h1 b /\ length b >= norm_length+1 
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (get h0 b i) = v (get h1 b i))

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO

val carry: b:bigint -> ctr:u32{w ctr <= norm_length} -> ST unit
    (requires (fun h -> carriable h b (w ctr) /\ carried h b (w ctr)))
    (ensures (fun h0 _ h1 -> carried h1 b norm_length /\ untouched_2 h0 h1 b (w ctr)
      /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
      /\ modifies_1 b h0 h1 ))
let rec carry b i =
  let h0 = HST.get() in
  if U32.eq i nlength then admit()
  else begin 
    let bi = index b i in
    let ri = mod2_26 bi in
    upd b i ri;
    let h1 = HST.get() in
    let c = (bi ^>> 26ul) in
    cut (v c = (v bi) / (pow2 26));
    Math.Lib.pow2_div_lemma 64 26;
    (* TODO *)
    assume (v c < pow2 (64 - 26));
    assert(live h1 b);
    assert(w i + 1 < length b); 
    let bip1 = index b (i+|1ul) in
    auxiliary_lemma_1' bip1 c; 
    let z = bip1 +^ c in
    upd b (i+|1ul) z;
    let h2 = HST.get() in
    eval_carry_lemma h0 b h2 b (w i);
    carry b (i+|1ul)
  end 

#reset-options "--z3timeout 20"
#set-options "--lax" // OK

val carry_top_to_0: b:bigint -> STL unit
    (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1
      /\ v (get h b 0) + 5 * v (get h b norm_length) < pow2 63))
    (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carried' h1 b 1
      /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime)
      /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (get h1 b i) = v (get h0 b i))
      /\ modifies_1 b h0 h1))      
let carry_top_to_0 b =
  Math.Lib.pow2_increases_lemma 64 63;
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in 
  let btop_5 = times_5 btop in
  upd b 0ul (b0 +^ btop_5);
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0

#reset-options

let carriable2 (h:heap) (b:bigint) (ctr:pos{ctr<=norm_length}) : GTot Type0 =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < ctr ==> v (get h b i) < pow2 26)
  /\ (forall (i:nat). {:pattern (v (get h b i))} (i > ctr /\ i < norm_length) ==> v (get h b i) < pow2 26)
  /\ (ctr < norm_length ==> v (get h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h b norm_length) < 2)
  /\ v (get h b ctr) < pow2 26 + pow2 15
  /\ (v (get h b ctr) >= pow2 26 ==> (
      forall (i:nat). {:pattern (v (get h b i))} ( i < ctr /\ i > 0) ==> v (get h b i) < pow2 15))
  /\ ((ctr = norm_length /\ v (get h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (get h b i))} (i > 0 /\ i < norm_length) ==> v (get h b i) < pow2 15))

val lemma_aux: a:nat -> b:pos -> Lemma (Math.Lib.div a b > 0 ==> a >= b)
let lemma_aux a b = 
  ()

(* TODO: express in terms of % properties *)
assume val lemma_aux_2: a:u64 -> Lemma ((v a < pow2 26+pow2 15 /\ v a >= pow2 26) ==> v a % pow2 26 < pow2 15)

#reset-options "--z3timeout 100"
#set-options "--lax" // OK

val carry2_aux: b:bigint -> ctr:u32{w ctr > 0 /\ w ctr <= norm_length} -> STL unit
  (requires (fun h -> carriable2 h b (w ctr)))
  (ensures (fun h0 _ h1 -> carriable2 h0 b (w ctr) /\ carriable2 h1 b norm_length
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ modifies_1 b h0 h1 ))
let rec carry2_aux b i = 
  let h0 = HST.get() in
  if U32.eq i nlength then ()
  else begin
    let bi = index b i in 
    let ri = mod2_26 bi in
    lemma_aux_2 bi;
    cut (v ri < pow2 (templ (w i))); 
    upd b i ri; 
    let h1 = HST.get() in
    let c = (bi ^>> 26ul) in
    // In the spec of >>, TODO
    assume(v c < 2); 
    let bip1 = index b (i+|1ul) in
    auxiliary_lemma_2 bip1 c; 
    Math.Lib.pow2_increases_lemma 64 27;
    Math.Lemmas.pow2_double_sum 26;
    Math.Lib.pow2_increases_lemma 26 15;
    let z = bip1 +^ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 26); 
    cut (v z >= pow2 26 ==> v c = 1); 
    cut (v c > 0 ==> v (get h0 b (w i)) / (pow2 26) > 0 ==> v (get h0 b (w i)) >= pow2 26);
    cut (v z >= pow2 26 ==> v (get h1 b (w i)) < pow2 15); 
    upd b (i+|1ul) z;
    let h2 = HST.get() in 
    cut (v z >= pow2 26 ==> v c = 1); 
    eval_carry_lemma h0 b h2 b (w i); 
    carry2_aux b (i+|1ul)
  end

#reset-options

val pow2_3_lemma: unit -> Lemma (pow2 3 = 8)
let pow2_3_lemma () = 
  ()

#reset-options "--z3timeout 100"
#set-options "--lax" // TODO

val carry2: b:bigint -> STL unit
  (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carriable2 h1 b norm_length 
    /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_1 b h0 h1))
let rec carry2 b = 
  let h0 = HST.get() in
  pow2_3_lemma ();
  Math.Lib.pow2_exp_lemma 3 37;
  Math.Lib.pow2_increases_lemma 40 37;
  Math.Lib.pow2_increases_lemma 40 26;
  Math.Lemmas.pow2_double_sum 40;
  Math.Lib.pow2_increases_lemma 63 41;
  carry_top_to_0 b;
  let h1 = HST.get() in
  upd b nlength (U64.of_string "0");
  let h2 = HST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut ( eval h2 b (norm_length+1) = eval h1 b (norm_length)); 
  let bi = index b 0ul in 
  let ri = mod2_26 bi in
  cut (v ri < pow2 26); 
  upd b 0ul ri; 
  let h3 = HST.get() in
  let c = (bi ^>> 26ul) in
  cut (v bi < pow2 41); 
  // In the spec of >>, TODO
  assume (v c < pow2 15); 
  let bip1 = index b 1ul in 
  auxiliary_lemma_2 bip1 c; 
  Math.Lib.pow2_increases_lemma 64 27;
  Math.Lemmas.pow2_double_sum 26;
  Math.Lib.pow2_increases_lemma 26 15;
  let z = bip1 +^ c in 
  upd b 1ul z;
  let h4 = HST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut(carriable2 h4 b 1);
  carry2_aux b 1ul

#reset-options "--z3timeout 100"

val last_carry: b:bigint -> STL unit
  (requires (fun h -> carriable2 h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carriable2 h0 b norm_length /\ norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_1 b h0 h1))
let last_carry b =
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let btop = index b nlength in 
  cut (v b0 < pow2 26 /\ v btop < 2); 
  pow2_3_lemma ();
  cut (5 * v btop < pow2 3 /\ True); 
  Math.Lib.pow2_increases_lemma 26 3;
  Math.Lemmas.pow2_double_sum 26;
  Math.Lib.pow2_increases_lemma 64 27;
  cut(v b0 + 5 * v btop < pow2 27 /\ True); 
  let btop_5 = times_5 btop in  
  upd b 0ul (b0 +^ btop_5); 
  let h1 = HST.get() in
  freduce_degree_lemma h0 h1 b 0;
  upd b nlength (U64.of_string "0");
  let h2 = HST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length);
  let bi = index b 0ul in 
  let ri = mod2_26 bi in
//  assert(v ri < pow2 26); 
  upd b 0ul ri; 
  let h3 = HST.get() in
  let c = (bi ^>> 26ul) in
  cut (v bi < pow2 26 + 5); 
  cut (v bi >= pow2 26 ==> v (get h3 b 1) < pow2 15); 
  // In the spec of >>, TODO
  assume (v bi >= pow2 26 ==> v c = 1); 
  let bip1 = index b 1ul in 
  auxiliary_lemma_2 bip1 c; 
  Math.Lib.pow2_increases_lemma 64 27;
  Math.Lemmas.pow2_double_sum 26;
  Math.Lib.pow2_increases_lemma 26 15;
  let z = bip1 +^ c in 
  upd b 1ul z;
  let h4 = HST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (v (get h4 b 1) < pow2 26); 
  cut (norm h4 b);
  ()

val modulo: b:bigint -> ST unit
  (requires (fun h -> live h b /\ satisfiesModuloConstraints h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ satisfiesModuloConstraints h0 b /\ norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime 
    /\ modifies_1 b h0 h1))
let modulo b =
  let h0 = HST.get() in
  freduce_degree b; 
  let h1 = HST.get() in
  upd b nlength (U64.of_string "0");
  let h2 = HST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length);
  carry b 0ul; 
  let h3 = HST.get() in
  carry2 b; 
  let h4 = HST.get() in
  last_carry b

val freduce_coefficients: b:bigint -> ST unit
  (requires (fun h -> live h b  
    /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 62)))
  (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b 
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime
    /\ modifies_1 b h0 h1))
let freduce_coefficients b = 
  let h0 = HST.get() in
  let tmp = create (U64.of_string "0") (U32.mul 2ul nlength-|1ul) in
  let h1 = HST.get() in
  eq_lemma_0 h0 h1 b;
  eval_eq_lemma h0 h1 b b norm_length; 
  blit b 0ul tmp 0ul nlength;
  let h2 = HST.get() in
  eval_eq_lemma h1 h2 b tmp norm_length;
  cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp i) = v (get h0 b i)); 
  carry tmp 0ul; 
  carry2 tmp; 
  last_carry tmp; 
  let h = HST.get() in
  blit tmp 0ul b 0ul nlength; 
  let h' = HST.get() in
  eval_eq_lemma h h' tmp b norm_length; 
  cut (forall (i:nat). {:pattern (v (get h tmp i))} i < norm_length ==> v (get h tmp i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h' b i))} i < norm_length ==> v (get h' b (0+i)) = v (get h tmp (0+i)))

(*** Finalization ***)

#set-options "--lax" // Never done

val finalize: b:bigint -> ST unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ norm h1 b
    /\ modifies_1 b h0 h1
    /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime))
let finalize b =
  let mask_26 = U64.sub ((U64.of_string "1") ^<< 26ul) (U64.of_string "1") in
  let mask2_26m5 = U64.sub mask_26 (U64.of_string "1" ^<< 2ul) in
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  let mask = U64.eq_mask b4 mask_26 in
  let mask = U64.eq_mask b3 mask_26 ^& mask in 
  let mask = U64.eq_mask b2 mask_26 ^& mask in 
  let mask = U64.eq_mask b1 mask_26 ^& mask in 
  let mask = U64.gte_mask b0 mask2_26m5 ^& mask in 
  upd b 0ul (b0 ^- (mask ^& mask2_26m5));
  upd b 1ul (b1 ^- (b1 ^& mask));
  upd b 2ul (b2 ^- (b2 ^& mask));
  upd b 3ul (b3 ^- (b3 ^& mask));
  upd b 4ul (b4 ^- (b4 ^& mask));
  ()
