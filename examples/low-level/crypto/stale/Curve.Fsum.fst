module Curve.Fsum

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer
open Math.Lib
open Curve.Parameters
open Curve.Bigint

#set-options "--lax"

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

abstract type willNotOverflow (h:heap) 
		     (a:bigint{live h a /\ length a >= norm_length}) 
		     (b:bigint{live h b /\ length b >= norm_length}) 
		     (ctr:nat) =
  (forall (i:nat). {:pattern (v (get h a i) + v (get h b i))} (i >= ctr /\ i < norm_length) ==> v (get h a i) + v (get h b i) < pow2 platform_size)

abstract type notModified (h0:heap) (h1:heap) 
			(a:bigint{live h0 a /\ live h1 a /\ length a >= norm_length})
			(ctr:nat) =
  (forall (i:nat). {:pattern (get h1 a i)}
    ((i <> ctr /\ i < length a) ==>  get h1 a i = get h0 a i))

val fsum_index_aux:
  a:bigint -> b:bigint{disjoint a b} -> ctr:u32{U32.v ctr < norm_length} ->
  STL unit
    (requires (fun h -> 
      live h a /\ live h b /\ norm_length <= length a /\ norm_length <= length b
      /\ willNotOverflow h a b (U32.v ctr) ))
    (ensures (fun h0 _ h1 -> 
      let ctr = U32.v ctr in
      live h0 a /\ live h1 a /\ live h0 b /\ live h1 b
      /\ length a = length a /\ length b = length b
      /\ norm_length <= length a /\ norm_length <= length b /\ modifies_1 a h0 h1
      /\ (willNotOverflow h1 a b (ctr+1))
      /\ (notModified h0 h1 a (ctr))
      /\ v (get h1 a (ctr)) = v (get h0 a ctr) + v (get h0 b ctr)))
let fsum_index_aux a b ctr =
  //@@
  let h0 = HST.get() in
  let ai = index a ctr in 
  let bi = index b ctr in 
  assert(U32.v ctr < norm_length); 
  assert(b2t(v (get h0 a (U32.v ctr)) + v (get h0 b (U32.v ctr)) < pow2 platform_size)); 
  let z = add ai bi in 
  upd a ctr z; 
  let h1 = HST.get() in
  (* upd_lemma h0 h1 a ctr z;  *)
  assert(v (get h1 a (U32.v ctr)) = v (get h0 a (U32.v ctr)) + v (get h0 b (U32.v ctr))); 
  assert(notModified h0 h1 a (U32.v ctr)); 
  assert(willNotOverflow h1 a b ((U32.v ctr)+1));
  (* no_upd_lemma h0 h1 b (only a); *)
  ()

abstract let isSum (h0:heap) (h1:heap) (a:bigint{live h0 a /\ live h1 a /\ length a = length a}) 
		  (b:bigint{live h0 b}) (ctr:nat) =
  (forall (i:nat). {:pattern (v (get h1 a i))}
	  (i>=ctr /\ i<norm_length) ==> (v (get h1 a i) = v (get h0 a i) + v (get h0 b i)))

abstract let notModified2 (h0:heap) (h1:heap)
			 (a:bigint{live h0 a /\ live h1 a})
			 (ctr:nat) =
  (forall (i:nat). {:pattern (get h1 a i)} 
    ((i < ctr \/ i >= norm_length) /\ i < length a) ==> get h1 a i = get h0 a i)
    
val fsum_index_lemma: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies_1 a h0 h1 /\ modifies_1 a h1 h2
      /\ modifies_1 a h1 h2
      /\ notModified2 h1 h2 a (ctr+1)
      /\ isSum h1 h2 a b (ctr+1)
      /\ willNotOverflow h0 a b (ctr+1)
      /\ notModified h0 h1 a ctr
      /\ v (get h1 a ctr) = v (get h0 a ctr) + v (get h0 b ctr) ))
    (ensures (
      live h0 a /\ live h0 b /\ live h2 a /\ live h2 b
      /\ modifies_1 a h0 h2
      /\ isSum h0 h2 a b ctr ))
let fsum_index_lemma h0 h1 h2 a b ctr =
  //@@
  (* no_upd_lemma h0 h1 b (only a); *)
  (* no_upd_lemma h1 h2 b (only a); *)
  assert(isSum h1 h2 a b (ctr+1)); 
  assert(notModified2 h1 h2 a (ctr+1)); 
  assert(notModified h0 h1 a ctr); 
  cut(isSum h0 h2 a b (ctr+1)); 
  cut(True /\ v (get h2 a ctr) = v (get h0 a ctr) + v (get h0 b ctr)); 
  (* FsumLemmas.auxiliary_lemma_7 ctr norm_length;  *)
  assert(isSum h0 h2 a b ctr)

// Verified, try with big timeout
val fsum_index:
  a:bigint -> b:bigint{disjoint a b} -> ctr:u32{U32.v ctr <= norm_length } ->
  STL unit
    (requires (fun h -> live h a /\ live h b
      /\ (forall (i:nat). (i >= U32.v ctr /\ i < norm_length) ==>
	  (v (get h a i) + v (get h b i) < pow2 platform_size)) ))
    (ensures (fun h0 _ h1 -> let ctr = U32.v ctr in
      live h0 a /\ live h0 b /\ live h1 a /\ live h1 b
      /\ modifies_1 a h0 h1
      /\ isSum h0 h1 a b ctr
      /\ notModified2 h0 h1 a ctr ))
let rec fsum_index a b ctr =
  //@@
  let h0 = HST.get() in
  if U32.eq nlength ctr then ()
  else (
    fsum_index_aux a b ctr; 
    let h1 = HST.get() in
    (* no_upd_lemma h0 h1 b (only a);  *)
    (* FsumLemmas.auxiliary_lemma_6 norm_length ctr;  *)
    fsum_index a b (U32.add ctr 1ul); 
    let h2 = HST.get() in
    fsum_index_lemma h0 h1 h2 a b (U32.v ctr)
  )
  
(* #reset-options *)

val addition_lemma_aux: h0:heap ->  h1:heap -> a:bigint{live h0 a /\ live h1 a} -> 
  b:bigint{live h0 b} -> len:pos{len <= length a /\ len <= length b
	   /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->
  Lemma
    (requires ( (eval h0 a (len-1) + eval h0 b (len-1) = eval h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 a (len-1)) + v (get h0 b (len-1))) ) )
    (ensures (eval h0 a len + eval h0 b len = eval h1 a len))
let addition_lemma_aux h0 h1 a b len =
  eval_def h1 a len;
  assert(eval h1 a len = pow2 (bitweight templ (len-1)) * v (get h1 a (len-1)) + eval h1 a (len-1));
  assert(v (get h1 a (len-1)) = v (get h0 a (len-1)) + v (get h0 b (len-1)));
  Math.Lemmas.distributivity_add_right (pow2 (bitweight templ (len-1))) (v (get h0 a (len-1)))  (v (get h0 b (len-1)));
  assert(eval h1 a len = (pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1)) + pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))) + eval h1 a (len-1));
  (* FsumLemmas.helper_lemma_2 (pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1))) *)
  (* 		(pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))) *)
  (* 		(eval h0 a (len-1)) *)
  (* 		(eval h0 b (len-1)); *)
  eval_def h0 a len;
  eval_def h0 b len

val addition_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a /\ live h1 a} ->
  b:bigint{live h0 b} -> len:nat{len <= length a /\ len <= length b /\ len <= length a
	  /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } -> Lemma
    (requires (True))
    (ensures ( eval h0 a len + eval h0 b len = eval h1 a len ))
let rec addition_lemma h0 h1 a b len =
  //@@
  match len with
  | 0 -> ()
  | _ -> addition_lemma h0 h1 a b (len-1);
    addition_lemma_aux h0 h1 a b len

(* #reset-options *)

val addition_max_value_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} -> b:bigint{live h0 b /\ length a = length b} -> c:bigint{live h1 c /\ length c = length a 
  /\ (forall (i:nat{i<length c}). v (get h1 c i) = v (get h0 a i) + v (get h0 b i)) } -> Lemma
    (requires (True))
    (ensures (let l = length c in maxValue h1 c l <= maxValue h0 a l + maxValue h0 b l))
let addition_max_value_lemma h0 h1 a b c = ()
  
val max_value_lemma: 
  h:heap -> a:bigint{ live h a } -> m:nat ->
  Lemma 
    (requires (forall (n:nat). n < length a ==> v (get h a n) <= m))
    (ensures (maxValue h a (length a) <= m))
let max_value_lemma h a m = ()

(* #reset-options *)

val addition_max_value_lemma_extended: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint{live h0 b} -> c:bigint{live h1 c /\ length a = length c} ->
  idx:nat -> len:nat{len + idx <= length a /\ len <= length b} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 c (i+idx)))} 
		  (i<len) ==> v (get h1 c (i+idx)) = v (get h0 a (i+idx)) + v (get h0 b i))
	       /\ (forall (i:nat). {:pattern (v (get h1 c i))}
		   (i < length c /\ (i < idx \/ i >= idx + len)) ==> v (get h1 c i) = v (get h0 a i))))
    (ensures (maxValue h1 c len <= maxValue h0 a len + maxValue h0 b len))
let addition_max_value_lemma_extended h0 h1 a b c idx len = 
  cut ( forall (i:nat). (i < length c /\ (i < idx \/ i >= idx + len))
	==> (v (get h1 c i) = v (get h0 a i) /\ v (get h1 c i) <= maxValue h0 a len + maxValue h0 b len)); 
  cut ( forall (i:nat). (i < length c /\ (i < idx \/ i >= idx + len)) 
  	==> v (get h1 c i) <= maxValue h0 a len + maxValue h0 b len); 
  cut(forall (i:nat). {:pattern (v (get h1 c i))} (i+idx < idx + len /\ i+idx >= idx) ==> (i >= 0 /\ i < len)); 
  cut((forall (i:nat). {:pattern (v (get h1 c i))} (i-idx)+idx=i)); 
  assert(forall (i:nat). {:pattern (v (get h1 c (i)))} (i<len) ==> v (get h1 c (i+idx)) = v (get h0 a (i+idx)) + v (get h0 b i)); 
  assert(forall (i:nat). {:pattern (v (get h1 c i))} (i >= idx /\ i < idx + len) ==> (v (get h1 c i) = v (get h1 c ((i-idx)+idx)))); 
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> ((v (get h1 c i) = v (get h0 a i) + v (get h0 b (i-idx))) )); 
  cut ( forall (i:nat). (i < idx + len /\ i >= idx)
	==> (v (get h0 a i) <= maxValue h0 a len /\ v (get h0 b (i-idx)) <= maxValue h0 b len));
  cut ( forall (i:nat). (i >= idx /\ i < idx + len)
	==> v (get h1 c i) <= maxValue h0 a len + maxValue h0 b len);
  cut ( forall (i:nat). i < length c 
	==> v (get h1 c i) <= maxValue h0 a len + maxValue h0 b len);
  max_value_lemma h1 c (maxValue h0 a len + maxValue h0 b len);
  ()

(* #reset-options *)

val auxiliary_lemma_2: ha:heap -> a:bigint{norm ha a} -> hb:heap -> b:bigint{norm hb b} -> 
  i:nat{ i < norm_length} -> Lemma
  (v (get ha a i) + v (get hb b i) < pow2 platform_size)
let auxiliary_lemma_2 ha a hb b i = ()
  (* UInt.add_lemma #(templ i) (v (get ha a i)) #(templ i) (v (get hb b i)); *)
  (* parameters_lemma_0 (); *)
  (* Lemmas.pow2_le_compat platform_size (templ i + 1) *)

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{norm ha a} ->
  hb:heap -> b:bigint{norm hb b} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> v (get ha a i) + v (get hb b i) < pow2 platform_size))
let auxiliary_lemma_0 ha a hb b = ()

(* #reset-options *)

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> b:bigint{norm h0 b} ->
  Lemma (requires (live h1 b /\ Seq.equal (sel h1  b) (sel h0 b)))
	(ensures (norm h1 b))
let auxiliary_lemma_1 h0 h1 b = 
  //@@
  ()

val auxiliary_lemma_3:
  h0:heap -> h1:heap -> 
  a:bigint{norm h0 a /\ live h1 a /\ length a >= norm_length} ->
  b:bigint{norm h0 b /\ norm h1 b} ->
  Lemma (requires (forall (i:nat{i>= 0 /\ i<norm_length}). 
	  (v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0))) ))
	(ensures (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)))
let auxiliary_lemma_3 h0 h1 a b =	
  cut (forall (i:nat{ i >= 0 /\ i < norm_length }). True ==> (i < norm_length /\ i+0 = i));
  cut (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i))

#reset-options

val fsum':
  a:bigint -> b:bigint{disjoint a b} -> STL unit
    (requires (fun h -> norm h a /\ norm h b))
    (ensures (fun h0 u h1 -> norm h0 a /\ norm h0 b /\ norm h1 b /\ live h1 a 
      /\ modifies_1 a h0 h1
      /\ eval h1 a norm_length = eval h0 a norm_length + eval h0 b norm_length
      /\ isSum h0 h1 a b 0 ))
let fsum' a b =
  let h0 = HST.get() in
  auxiliary_lemma_0 h0 a h0 b;
  fsum_index a b 0ul;
  let h1 = HST.get() in
  (* no_upd_lemma h0 h1 b (only a); *)
  auxiliary_lemma_1 h0 h1 b;
  auxiliary_lemma_3 h0 h1 a b;
  addition_lemma h0 h1 a b norm_length;
  cut(forall (i:nat). (i >= 0 /\ i < norm_length) ==> i < norm_length);
  ()
