(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Curve.FsumWide

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

let u32 = U32.t
let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

abstract let willNotOverflow 
  (h:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat)
  (a:bigint_wide{live h a /\ length a >= a_idx+len})
  (b:bigint_wide{live h b /\ length b >= b_idx+len}) = 
    (forall (i:nat). {:pattern (v (get h a (i+a_idx)))}
      (i >= ctr /\ i < len) ==>
	(v (get h a (i+a_idx)) + v (get h b (i+b_idx)) < pow2 platform_wide))

abstract let isNotModified
  (h0:heap) (h1:heap) (a_idx:nat) (len:nat) (ctr:nat) 
  (a:bigint_wide{live h0 a /\ live h1 a /\ a_idx+len <= length a /\ length a = length a}) = 
    (forall (i:nat). {:pattern (get h1 a i)}
      ((i<ctr+a_idx \/ i >= len+a_idx) /\ i<length a) ==>
	(get h1 a i = get h0 a i))

abstract let isSum
  (h0:heap) (h1:heap) (a_idx:nat) (b_idx:nat) (len:nat) (ctr:nat)
  (a:bigint_wide{live h0 a /\ live h1 a /\ a_idx+len <= length a /\ length a = length a})
  (b:bigint_wide{live h0 b /\ b_idx+len <= length b}) =
    (forall (i:nat). {:pattern (v (get h1 a (i+a_idx))) \/ (v (get h1 a i))}
      (i>= ctr /\ i<len) ==> 
	(v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx))) )

(* #reset-options *)

val fsum_index_lemma: h0:heap -> h1:heap -> h2:heap -> a:bigint_wide -> a_idx:nat -> 
  b:bigint_wide{disjoint a b} -> b_idx:nat -> len:nat -> ctr:nat{ ctr < len } -> Lemma
    (requires (
      live h0 a /\ live h0 b /\ live h1 b /\ live h1 a /\ live h2 a /\ live h2 b
      /\ a_idx+len <= length a /\ b_idx+len <= length b
      /\ (modifies_1 a h0 h1) /\ (modifies_1 a h1 h2)
      // Before fsum_index (ctr+1)
      /\ (forall (i:nat). 
	  (i >= ctr+1 /\ i < len) ==>
	    (v (get h1 a (i+a_idx)) + v (get h1 b (i+b_idx)) < pow2 platform_wide))
      /\ (forall (i:nat).
	  (i<>ctr /\ i < length a - a_idx) ==> get h0 a (i+a_idx) == get h1 a (i+a_idx))
      /\ (v (get h1 a (ctr+a_idx)) = v (get h0 a (ctr+a_idx)) + v (get h0 b (ctr+b_idx)))
       // After fsum
      /\ (forall (i:nat). (i>= ctr+1 /\ i<len) ==> 
	  (v (get h2 a (i+a_idx)) = v (get h1 a (i+a_idx)) + v (get h1 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<length a-a_idx) ==>
	  (get h2 a (i+a_idx) == get h1 a (i+a_idx))) ))
    (ensures (
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (a_idx+len <= length a /\ b_idx+len <= length b)
      /\ (modifies_1 a h0 h2)
      /\ (forall (i:nat). (i>= ctr /\ i<len) ==> 
	  (v (get h2 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx))) )
      /\ (forall (i:nat). ((i<ctr \/ i >= len) /\ i<length a-a_idx) ==>
	  (get h2 a (i+a_idx) == get h0 a (i+a_idx)))
     ))     
let fsum_index_lemma h0 h1 h2 a a_idx b b_idx len ctr =
  //@@
      (* no_upd_lemma_1 h1 h2 b (only a); *)
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> (v (get h2 a (i+a_idx)) = v (get h1 a (i+a_idx)) + v (get h1 b (i+b_idx)))); 
      let (f:(i:nat{i<>ctr/\i<length a-a_idx} -> GTot bool)) =  (fun i -> v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx))) in 
      (* FsumLemmas.auxiliary_lemma_3 a_idx ctr len (length a) f;  *)
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> v (get h1 a (i+a_idx)) = v (get h0 a (i+a_idx))); 
      (* no_upd_lemma h0 h1 b (only a); *)
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> v (get h1 b (i+b_idx)) = v (get h0 b (i+b_idx))); 
      cut(forall (i:nat). (i>=ctr+1 /\ i < len) ==> (v (get h2 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx)))); 
      cut(forall (i:nat). ((i<ctr+1 \/ i >= len) /\ i<length a-a_idx) ==>  
	  (get h2 a (i+a_idx) == get h1 a (i+a_idx)) ); 
      cut(get h2 a (ctr+a_idx) == get h1 a (ctr+a_idx)); 
      cut(True /\ v (get h2 a (ctr+a_idx)) = v (get h1 a (ctr+a_idx))); 
      assert(v (get h2 a (ctr+a_idx)) = v (get h0 a (ctr+a_idx)) + v (get h0 b (ctr+b_idx)));
      let (g:(i:nat{(i>=ctr+1 /\ i < len)\/i=ctr} -> GTot bool)) = fun i -> 
	(v (get h2 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx))) in
      (* FsumLemmas.auxiliary_lemma_4 len ctr g;  *)
      cut(forall (i:nat). (i>=ctr /\ i < len) ==> (v (get h2 a (i+a_idx)) = v (get h0 a (i+a_idx)) + v (get h0 b (i+b_idx))) ); 
      cut(forall (i:nat). ((i<ctr \/ i >= len) /\ i<length a-a_idx) ==> (get h2 a (i+a_idx) == get h0 a (i+a_idx))); 
      (* no_upd_lemma h0 h2 b (only a) *)
      ()
      
(* #reset-options *)

// Verified, try with big timeout
val fsum_index: a:bigint_wide -> a_idx:u32 -> b:bigint_wide{disjoint a b} -> b_idx:u32 -> len:u32 -> 
  ctr:u32{U32.v ctr <= U32.v len} -> STL unit
    (requires (fun h ->
      live h a /\ live h b /\ U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+U32.v len <= length b
      /\ (forall (i:nat). {:pattern (i+U32.v a_idx); (i+U32.v b_idx)} (i >= U32.v ctr /\ i < U32.v len) 
	   ==> (v (get h a (i+U32.v a_idx)) + v (get h b (i+U32.v b_idx)) < pow2 platform_wide)) ))
    (ensures (fun h0 _ h1 -> 
      live h0 a /\ live h0 b /\ live h1 a /\ live h1 b
      /\ U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+U32.v len <= length b
      /\ modifies_1 a h0 h1
      /\ (forall (i:nat). (i>= U32.v ctr /\ i<U32.v len) ==> 
	  (v (get h1 a (i+U32.v a_idx)) = v (get h0 a (i+U32.v a_idx)) + v (get h0 b (i+U32.v b_idx))) )
      /\ (forall (i:nat). ((i<U32.v ctr \/ i >= U32.v len) /\ i<length a-U32.v a_idx) ==>
	  (get h1 a (i+U32.v a_idx) == get h0 a (i+U32.v a_idx)))  ))
let rec fsum_index a a_idx b b_idx len ctr =
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
    let i = ctr in
    (* FsumLemmas.helper_lemma_1 a_idx i len (length a); *)
    (* FsumLemmas.helper_lemma_1 b_idx i len (length b); *)
    let ai = index a (i+|a_idx) in 
    let bi = index b (i+|b_idx) in 
    assert(U32.v i >= U32.v ctr /\ U32.v i < U32.v len); 
    cut(b2t(v (get h0 a (U32.v i+U32.v a_idx)) + v (get h0 b (U32.v i+U32.v b_idx)) < pow2 platform_wide));
    let z = ai +^ bi in
    upd a (a_idx+|i) z; 
    let h1 = HST.get() in
    (* upd_lemma h0 h1 a (i+|a_idx) z;  *)
    (* no_upd_lemma h0 h1 b (only a);  *)
    cut(True /\ live h1 a); 
    cut(True /\ live h1 b); 
    (* cut(U32.v a_idx+U32.v len <= length a /\ U32.v b_idx+len <= length b);  *)
    (* cut(forall (i:nat). (i >= ctr+1 /\ i < len) ==>  *)
    (*   (v (get h1 a (i+a_idx)) + v (get h1 b (i+b_idx)) < pow2 platform_wide)); *)
    (* FsumLemmas.auxiliary_lemma_0 len ctr; *)
    fsum_index a a_idx b b_idx len (ctr+|1ul); 
    let h2 = HST.get() in
    (* no_upd_lemma h1 h2 b (only a);       *)
    (* cut (forall (i:nat). *)
    (*   (i<>ctr+a_idx /\ i < length a) ==> get h0 a (i) == get h1 a (i));  *)
    (* FsumLemmas.auxiliary_lemma_5 ctr (elength a) a_idx; *)
    (* cut (forall (i:nat). *)
    (*   (i<>ctr /\ i < length a - a_idx) ==> get h0 a (i+a_idx) == get h1 a (i+a_idx)); *)
    fsum_index_lemma h0 h1 h2 a (U32.v a_idx) b (U32.v b_idx) (U32.v len) (U32.v ctr)
  end

(* #reset-options *)

val addition_lemma_aux: h0:heap ->  h1:heap -> a:bigint_wide{live h0 a /\ live h1 a} -> 
  b:bigint_wide{live h0 b} -> len:pos{len <= length a /\ len <= length b
	   /\ (forall (i:nat{ i < len }). v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) } ->Lemma 
    (requires ( (eval_wide h0 a (len-1) + eval_wide h0 b (len-1) = eval_wide h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 a (len-1)) + v (get h0 b (len-1))) ) )
    (ensures (eval_wide h0 a len + eval_wide h0 b len = eval_wide h1 a len))
let addition_lemma_aux h0 h1 a b len =
  //@@
  eval_wide_def h1 a len;
  assert(eval_wide h1 a len = pow2 (bitweight templ (len-1)) * v (get h1 a (len-1)) + eval_wide h1 a (len-1));
  assert(v (get h1 a (len-1)) = v (get h0 a (len-1)) + v (get h0 b (len-1)));
  Math.Lemmas.distributivity_add_right (pow2 (bitweight (templ) (len-1))) (v (get h0 a (len-1)))  (v (get h0 b (len-1)));
  assert(eval_wide h1 a len = (pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1)) + pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))) + eval_wide h1 a (len-1));
  (* FsumLemmas.helper_lemma_2 (pow2 (bitweight (templ) (len-1)) * v (get h0 a (len-1))) *)
  (* 		(pow2 (bitweight (templ) (len-1)) * v (get h0 b (len-1))) *)
  (* 		(eval_wide h0 a (len-1)) *)
  (* 		(eval_wide h0 b (len-1)); *)
  eval_wide_def h0 a len;
  eval_wide_def h0 b len

(* #reset-options *)

val addition_lemma: h0:heap -> h1:heap -> a:bigint_wide{live h0 a /\ live h1 a} -> 
  b:bigint_wide{live h0 b} -> len:nat{len <= length a /\ len <= length b 
    /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i))} ->
  Lemma
    (requires (True))
    (ensures (eval_wide h0 a len + eval_wide h0 b len = eval_wide h1 a len ))
let rec addition_lemma h0 h1 a b len =
  //@@
  match len with
  | 0 -> ()
  | _ -> addition_lemma h0 h1 a b (len-1);
    addition_lemma_aux h0 h1 a b len

(* #reset-options *)

val addition_max_value_lemma: h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> 
  b:bigint_wide{live h0 b /\ length a = length b} ->
  c:bigint_wide{live h1 c /\ length c = length a /\ (forall (i:nat{i<length c}). v (get h1 c i) = v (get h0 a i) + v (get h0 b i)) } ->
  Lemma
    (requires (True))
    (ensures (let l = length c in maxValue_wide h1 c l <= maxValue_wide h0 a l + maxValue_wide h0 b l))
let addition_max_value_lemma h0 h1 a b c = ()

(* #reset-options *)

val max_value_lemma: 
  h:heap -> a:bigint_wide{ live h a } -> m:nat ->
  Lemma 
    (requires (forall (n:nat). n < length a ==> v (get h a n) <= m))
    (ensures (maxValue_wide h a (length a) <= m))
let max_value_lemma h a m = ()

(* #reset-options *)

val addition_max_value_lemma_extended: h0:heap -> h1:heap -> a:bigint_wide{live h0 a} -> 
  b:bigint_wide{live h0 b} -> c:bigint_wide{live h1 c /\ length a = length c} ->
  idx:nat -> len:nat{ len + idx <= length a /\ len <= length b } -> Lemma
    (requires ((forall (i:nat{i<len}). 
		  v (get h1 c (i+idx)) = v (get h0 a (i+idx)) + v (get h0 b i))
	       /\ (forall (i:nat{i < length c /\ (i < idx \/ i >= idx + len)}).
		   v (get h1 c i) = v (get h0 a i))))
    (ensures (let l = length c in maxValue_wide h1 c l  <= maxValue_wide h0 a l + maxValue_wide h0 b l))
let addition_max_value_lemma_extended h0 h1 a b c idx len = 
  //@@
  (* cut ( forall (i:nat). (i < length c /\ (i < idx \/ i >= idx + len)) *)
  (* 	==> (v (get h1 c i) = v (get h0 a i) /\ v (get h1 c i) <= maxValue h0 a + maxValue h0 b)); *)
  (* cut ( forall (i:nat). (i < length c /\ (i < idx \/ i >= idx + len))  *)
  (* 	==> v (get h1 c i) <= maxValue h0 a + maxValue h0 b); *)
  (* cut ( forall (i:nat). (i < idx + len /\ i >= idx) *)
  (* 	==> ((v (get h1 c i) = v (get h0 a i) + v (get h0 b (i-idx)))  *)
  (* 	     /\ (v (get h1 c i) <= v (get h0 a i) + v (get h0 b (i-idx)))) ); *)
  (* cut ( forall (i:nat). (i < idx + len /\ i >= idx) *)
  (* 	==> (v (get h0 a i) <= maxValue h0 a /\ v (get h0 b (i-idx)) <= maxValue h0 b)); *)
  (* cut ( forall (i:nat). (i >= idx /\ i < idx + len) *)
  (* 	==> v (get h1 c i) <= maxValue h0 a + maxValue h0 b); *)
  (* cut ( forall (i:nat). i < length c  *)
  (* 	==> v (get h1 c i) <= maxValue h0 a + maxValue h0 b); *)
  (* max_value_lemma h1 c (maxValue h0 a + maxValue h0 b); *)
  ()

(* #reset-options *)

val auxiliary_lemma_2: ha:heap -> a:bigint_wide{norm_wide ha a} ->
  hb:heap -> b:bigint_wide{norm_wide hb b} -> i:nat{ i < norm_length} ->
  Lemma (v (get ha a i) + v (get hb b i) < pow2 platform_size)
let auxiliary_lemma_2 ha a hb b i = ()
  (* UInt.add_lemma #(templ i) (v (get ha a i)) #(templ i) (v (get hb b i)); *)
  (* parameters_lemma_0 (); *)
  (* Lemmas.pow2_le_compat platform_size (templ i + 1) *)

(* #reset-options *)

val auxiliary_lemma_0: 
  ha:heap -> a:bigint_wide{norm_wide ha a} ->
  hb:heap -> b:bigint_wide{norm_wide hb b} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> v (get ha a i) + v (get hb b i) < pow2 platform_size))
let auxiliary_lemma_0 ha a hb b = ()

(* #reset-options *)

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> b:bigint_wide{norm_wide h0 b} ->
  Lemma (requires (live h1 b /\ Seq.equal (sel h1 b) (sel h0 b)))
	(ensures (norm_wide h1 b))
let auxiliary_lemma_1 h0 h1 b = 
  //@@
  ()

(* #reset-options *)

val auxiliary_lemma_3:
  h0:heap -> h1:heap -> 
  a:bigint_wide{norm_wide h0 a /\ live h1 a /\ length a >= norm_length} ->
  b:bigint_wide{norm_wide h0 b /\ norm_wide h1 b} ->
  Lemma (requires (forall (i:nat{i>= 0 /\ i<norm_length}). 
	  (v (get h1 a (i+0)) = v (get h0 a (i+0)) + v (get h0 b (i+0))) ))
	(ensures (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)))
let auxiliary_lemma_3 h0 h1 a b =	
  cut (forall (i:nat{ i >= 0 /\ i < norm_length }). True ==> (i < norm_length /\ i+0 = i));
  cut (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i))

(* #reset-options *)

val fsum':
  a:bigint_wide -> b:bigint_wide{disjoint a b} -> STL unit
    (requires (fun h -> norm_wide h a /\ norm_wide h b))
    (ensures (fun h0 u h1 -> norm_wide h0 a /\ norm_wide h0 b /\ norm_wide h1 b /\ live h1 a 
      /\ modifies_1 a h0 h1
      /\ eval_wide h1 a norm_length = eval_wide h0 a norm_length + eval_wide h0 b norm_length
      /\ (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i)) ))
let fsum' a b =
  //@@
  admitP(True /\ pow2 platform_size < pow2 platform_wide);
  let h0 = HST.get() in
  auxiliary_lemma_0 h0 a h0 b;
  fsum_index a 0ul b 0ul nlength 0ul;
  let h1 = HST.get() in
  (* no_upd_lemma h0 h1 b (only a); *)
  auxiliary_lemma_1 h0 h1 b;
  auxiliary_lemma_3 h0 h1 a b;
  addition_lemma h0 h1 a b norm_length;
  ()

