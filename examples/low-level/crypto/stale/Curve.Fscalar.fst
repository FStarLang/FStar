module Curve.Fscalar

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
module U128 = FStar.UInt128

let w: u32 -> Tot int = U32.v
let vv: u128 -> Tot int = U128.v

let op_Plus_Bar = U32.add
let op_Plus_Subtraction = U32.sub

#reset-options

abstract type willNotOverflow (h:heap) 
		     (a:bigint{live h a /\ length a >= norm_length}) 
		     (s:u64) (ctr:nat) =
  (forall (i:nat). {:pattern (v (get h a i))}
    (i >= ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide)

abstract type isScalarProduct (h0:heap) (h1:heap) (ctr:nat) (len:nat)
		  (a:bigint{live h0 a /\ length a >= len}) 
		  (s:u64)
		  (res:bigint_wide{live h1 res /\ length res >= len}) =
  (forall (i:nat). {:pattern (U128.v (get h1 res i))}
    (i>= ctr /\ i < len) ==> U128.v (get h1 res i) = v (get h0 a i) * v s)

abstract type isNotModified (h0:heap) (h1:heap) 
		   (res:bigint_wide{live h0 res /\ live h1 res /\ length res >= norm_length
		     /\ length res = length res})
		   (ctr:nat) =
  (forall (i:nat). {:pattern (get h1 res i)}
    (i < length res /\ (i < ctr \/ i >= norm_length)) ==>
      (get h1 res i == get h0 res i))

#reset-options

(* Lemma *)
val scalar_multiplication_lemma_aux: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b} -> s:int -> len:pos{ (len <= length a)  /\ (len <= length b) } ->
  Lemma
    (requires ( (eval h0 a (len-1) * s = eval_wide h1 b (len-1))
		/\ (v (get h0 a (len-1)) * s = U128.v (get h1 b (len-1)))))
    (ensures ( eval h0 a len * s = eval_wide h1 b len ))
let scalar_multiplication_lemma_aux h0 h1 a b s len =
//  admit();
  Math.Lemmas.paren_mul_left (pow2 (bitweight (templ) (len-1))) (v (get h0 a (len-1))) s;
  Math.Lemmas.distributivity_add_left ((pow2 (bitweight (templ) (len-1))) * (v (get h0 a (len-1)))) (eval h0 a (len-1)) s

#reset-options

(* Lemma *)
val scalar_multiplication_lemma: h0:heap -> h1:heap -> a:bigint{live h0 a} -> 
  b:bigint_wide{live h1 b} -> s:int -> len:nat{len <= length a /\ len <= length b} ->
  Lemma
    (requires (forall (i:nat). i < len ==> v (get h0 a i) * s = U128.v (get h1 b i)))
    (ensures (eval h0 a len * s = eval_wide h1 b len))
let rec scalar_multiplication_lemma h0 h1 a b s len =
//  admit();
  match len with
  | 0 -> 
    assert(eval h0 a len = 0); ()
    (* FscalarLemmas.lemma_1 s *)
  | _ -> 
    (* FscalarLemmas.lemma_3 len; *)
    scalar_multiplication_lemma h0 h1 a b s (len-1); 
    scalar_multiplication_lemma_aux h0 h1 a b s len

val scalar_multiplication_tr_1: res:bigint_wide -> a:bigint{disjoint res a} -> s:u64 -> 
  ctr:u32{w ctr<norm_length} -> STL unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (modifies_1 res h0 h1) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= w ctr+1 /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide) 
       /\ (forall (i:nat). (i < length res /\ i <> w ctr) ==> (get h1 res i == get h0 res i))
       /\ (U128.v (get h1 res (w ctr)) = v (get h0 a (w ctr)) * v s)
     ))
let rec scalar_multiplication_tr_1 res a s ctr =
    let ai = index a ctr in
    let z = U128.mul_wide ai s in
    upd res ctr z

val scalar_multiplication_tr_2:
  h0:heap -> h1:heap -> h2:heap -> res:bigint_wide -> a:bigint{disjoint res a} -> s:u64 -> ctr:nat{ctr<norm_length} -> 
  Lemma
     (requires (
       (live h1 res) /\ (live h2 res) /\ (live h1 a) /\ (live h2 a) /\ live h0 a /\ live h0 res
       /\ modifies_1 res h0 h1
       /\ (modifies_1 res h1 h2) /\ (length a >= norm_length)
       /\ (forall (i:nat). {:pattern (get h1 a i)} (i >= ctr+1 /\ i < norm_length) ==> v (get h1 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ length res = length res
       /\ (forall (i:nat). {:pattern (get h1 res i)} (i < length res /\ i <> ctr) ==> get h1 res i == get h0 res i)
       /\ vv (get h1 res ctr) = v (get h0 a ctr) * v s
       /\ (forall (i:nat{(i>= ctr+1 /\ i < norm_length)}). {:pattern (get h2 res i)} vv (get h2 res i) = v (get h1 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < ctr+1 \/ i >= norm_length))}). {:pattern (get h2 res i)}
	   (get h2 res i == get h1 res i))
       /\ (Seq.equal (sel h1 (a)) (sel h2 (a))) ))
     (ensures (
       (live h0 res) /\ (live h2 res) /\ (live h0 a) /\ (live h2 a)
       /\ (modifies_1 res h0 h2) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (forall (i:nat{(i>= ctr /\ i < norm_length)}). vv (get h2 res i) = v (get h0 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < ctr \/ i >= norm_length))}). 
	   (get h2 res i == get h0 res i))
       /\ (Seq.equal (sel h0 (a)) (sel h2 (a)))
     ))
let scalar_multiplication_tr_2 h0 h1 h2 res a s ctr =
  (* no_upd_lemma h0 h1 a (only res); *)
  (* no_upd_lemma h1 h2 a (only res); *)
  ()

(* Code *)
(* Tail recursive version of the scalar multiplication *)
val scalar_multiplication_tr: res:bigint_wide -> a:bigint{disjoint res a} -> s:u64 -> ctr:u32{w ctr<=norm_length} -> STL unit
     (requires (fun h -> 
       (live h res) /\ (live h a) /\ (length a >= norm_length) /\ (length res >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h a i) * v s < pow2 platform_wide)))
     (ensures (fun h0 u h1 -> 
       (live h0 res) /\ (live h1 res) /\ (live h0 a) /\ (live h1 a)
       /\ (modifies_1 res h0 h1) /\ (length a >= norm_length)
       /\ (forall (i:nat). (i >= w ctr /\ i < norm_length) ==> v (get h0 a i) * v s < pow2 platform_wide)
       /\ (length res >= norm_length) /\ (length res = length res)
       /\ (forall (i:nat{(i>= w ctr /\ i < norm_length)}). vv (get h1 res i) = v (get h0 a i) * v s)
       /\ (forall (i:nat{(i < length res /\ (i < w ctr \/ i >= norm_length))}). 
	   (get h1 res i == get h0 res i))
       /\ (Seq.equal (sel h0 (a)) (sel h1 (a)))  ))
let rec scalar_multiplication_tr res a s ctr =
  //admit();
  let h0 = HST.get() in
  if U32.eq ctr nlength then ()
  else begin
     let i = ctr in
     (* FscalarLemmas.lemma_4 norm_length ctr;  *)
     scalar_multiplication_tr_1 res a s ctr; 
     let h1 = HST.get() in 
     (* no_upd_lemma h0 h1 a (only res); *)
     scalar_multiplication_tr res a s (ctr+|1ul); 
     let h2 = HST.get() in
     scalar_multiplication_tr_2 h0 h1 h2 res a s (w ctr)
  end

(* Lemma *)   	 
val theorem_scalar_multiplication: h0:heap -> h1:heap -> a:bigint{live h0 a} -> s:u64 -> 
  len:nat{len <= length a} -> b:bigint_wide{live h1 b /\ len <= length b} -> Lemma
    (requires (forall (i:nat). i < len ==> vv (get h1 b i) = v (get h0 a i) * v s))
    (ensures ((eval_wide h1 b len) = (eval h0 a len) * v s))
let theorem_scalar_multiplication h0 h1 a s len b = 
  scalar_multiplication_lemma h0 h1 a b (v s) len; ()

#reset-options

val auxiliary_lemma_2: ha:heap -> a:bigint{norm ha a} -> s:u64 -> i:nat{ i < norm_length} -> Lemma
    (requires (True))
    (ensures (v (get ha a i) * v s < pow2 (platform_wide)))
let auxiliary_lemma_2 ha a s i =
  (* UInt.mul_lemma #(templ i) (v (get ha a i)) #platform_size (v s); *)
  Curve.Parameters.parameters_lemma_0 ();
  (* Math.Lib.pow2_le_compat platform_wide (templ i + platform_size) *)
  ()
  
val auxiliary_lemma_0: ha:heap -> a:bigint{norm ha a} -> s:u64 -> Lemma
  (forall (i:nat). i < norm_length ==> v (get ha a i) * v s < pow2 platform_wide)
let auxiliary_lemma_0 ha a s = ()

val auxiliary_lemma_1: h0:heap -> h1:heap -> b:bigint{norm h0 b} -> #t:Type -> b':buffer t ->
  Lemma (requires (live h1 b /\ modifies_1 b' h0 h1 /\ disjoint b b'))
	(ensures (norm h1 b))
let auxiliary_lemma_1 h0 h1 b #t b' = ()

val scalar': res:bigint_wide -> a:bigint{disjoint res a} -> s:u64 -> STL unit
     (requires (fun h -> norm h a /\ live h res))
     (ensures (fun h0 u h1 -> live h0 res /\ live h1 res /\ norm h0 a /\ norm h1 a
       /\ modifies_1 res h0 h1
       /\ eval_wide h1 res norm_length = eval h0 a norm_length * v s ))
let scalar' res a s =
  let h0 = HST.get() in  
  auxiliary_lemma_0 h0 a s; 
  scalar_multiplication_tr res a s 0ul; 
  let h1 = HST.get() in
  (* no_upd_lemma h0 h1 a (only res); *)
  auxiliary_lemma_1 h0 h1 a (res); 
  theorem_scalar_multiplication h0 h1 a s norm_length res; 
  ()

	       
