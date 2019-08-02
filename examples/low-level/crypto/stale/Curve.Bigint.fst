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
module Curve.Bigint

open FStar.UInt8
open FStar.UInt128
open FStar.UInt64
open FStar.HST
open FStar.Buffer
open FStar.Mul
open FStar.Ghost
open Math.Axioms
open Math.Lib
open Curve.Parameters

let u8 = UInt8.t
let u32 = UInt32.t
let u64  = UInt64.t
let u128 = UInt128.t
let heap = HyperStack.mem

(* * Types ***) 

(* Maps the index of the integer data to the theoretic bit size of the cell *)
let template : Type = (nat -> Tot pos)
type template_const = t:template{ forall (n:nat). t n = t 0 }

val byte_templ: template
let byte_templ = fun x -> 8

(* Big integer types *)
type bigint = b:buffer u64{length b >= norm_length}
type bigint_wide = b:buffer u128{length b >= norm_length}
type bytes = buffer u8

(* Normalized big integer type *)
let norm (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length 
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==>  v (get h b i) < pow2 (templ i))

(* Normalized big integer type *)
let norm_wide (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ length b >= norm_length 
  /\ (forall (i:nat). {:pattern (UInt128.v (get h b i))} i < norm_length ==>  UInt128.v (get h b i) < pow2 (templ i))

let null (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ (forall (n:nat). {:pattern (v (get h b n))} n < length b ==> v (get h b n) = 0)

let null_wide (h:heap) (b:bigint_wide) : GTot Type0 =
  live h b /\ (forall (n:nat). {:pattern (UInt128.v (get h b n))} n < length b ==> UInt128.v (get h b n) = 0)

let filled (h:heap) (b:bigint) : GTot Type0 =
  live h b /\ length b >= norm_length /\ 
  (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> (pow2 (templ i) <= v (get h b i) /\ v (get h b i) < pow2 (templ i + 1)))

val bitweight : t:template -> n:nat -> GTot nat
let rec bitweight t n = 
  match n with 
  | 0 -> 0
  | _ -> t (n-1) + bitweight t (n-1)

let bitweight_def t n : Lemma ((n = 0 ==> bitweight t n = 0) /\ (n > 0 ==> bitweight t n = bitweight t (n-1) + t (n-1))) = ()

val eval : h:heap -> b:bigint{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval h  b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight templ (n-1)) * v (get h b (n-1)) + eval h  b (n-1)

val eval_wide: h:heap -> b:bigint_wide{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval_wide h b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight templ (n-1)) * UInt128.v (get h b (n-1)) + eval_wide h  b (n-1)

let eval_def h (b:bigint{live h b}) (n:nat{n<=length b}) : Lemma 
  ((n = 0 ==> eval h b n = 0)
    /\ (n <> 0 ==> eval h b n = pow2 (bitweight templ (n-1)) * v (get h b (n-1)) + eval h b (n-1)))
  = ()

let eval_wide_def h (b:bigint_wide{live h b}) (n:nat{n<=length b}) : Lemma 
  ((n = 0 ==> eval_wide h b n = 0)
    /\ (n <> 0 ==> eval_wide h b n = pow2 (bitweight templ (n-1)) * UInt128.v (get h b (n-1)) + eval_wide h b (n-1)))
  = ()

val eval_bytes : h:heap -> b:bytes{live h b} -> n:nat{n <= length b} -> GTot nat
let rec eval_bytes h b n =
  match n with
  | 0 -> 0
  | _ -> pow2 (bitweight byte_templ (n-1)) * UInt8.v (get h b (n-1)) + eval_bytes h b (n-1)

val maxValue: h:heap -> b:bigint{live h  b} -> l:pos{l <= length  b} -> GTot nat
let rec maxValue h  b l = 
  match l with
  | 1 -> v (get h  b 0)
  | _ -> if maxValue h  b (l-1) > v (get h  b (l-1)) then maxValue h  b (l-1)
	 else v (get h  b (l-1))

val maxValue_wide: h:heap -> b:bigint_wide{live h  b} -> l:pos{l <= length  b} -> GTot nat
let rec maxValue_wide h  b l = 
  match l with
  | 1 -> UInt128.v (get h  b 0)
  | _ -> if maxValue_wide h  b (l-1) > UInt128.v (get h  b (l-1)) then maxValue_wide h  b (l-1)
	 else UInt128.v (get h  b (l-1))

val maxValue_wide_lemma_aux: h:heap -> b:bigint_wide{live h b} -> l:pos{l <= length b} ->
  Lemma (forall (i:nat). i < l ==> UInt128.v (get h b i) <= maxValue_wide h b l)
let rec maxValue_wide_lemma_aux h b l =
  match l with
  | 1 -> ()
  | _ -> maxValue_wide_lemma_aux h b (l-1)

val maxValue_wide_lemma: h:heap -> b:bigint_wide{live h b} ->
  Lemma (forall (i:nat). {:pattern (UInt128.v (get h b i))}
    i < length b ==> UInt128.v (get h b i) <= maxValue_wide h b (length b))
let rec maxValue_wide_lemma h b = maxValue_wide_lemma_aux h b (length b)

val maxValue_wide_bound_lemma_aux: h:heap -> b:bigint_wide{live h b /\ length b > 0} -> l:pos{l <= length b} -> bound:nat -> Lemma
  (requires (forall (i:nat). i < l ==> UInt128.v (get h b i) <= bound))
  (ensures (maxValue_wide h b l <= bound))
let rec maxValue_wide_bound_lemma_aux h b l bound =
  match l with
  | 1 -> ()
  | _ -> maxValue_wide_bound_lemma_aux h b (l-1) bound

val maxValue_wide_bound_lemma: h:heap -> b:bigint_wide{live h b /\ length b > 0} -> bound:nat -> Lemma
  (requires (forall (i:nat). i < length b ==> UInt128.v (get h b i) <= bound))
  (ensures (maxValue_wide h b (length b) <= bound))
let maxValue_wide_bound_lemma h b bound =
  maxValue_wide_bound_lemma_aux h b (length b) bound

val maxValue_lemma_aux: h:heap -> b:bigint{live h b} -> l:pos{l<=length b} ->
  Lemma (forall (i:nat). i < l ==> v (get h b i) <= maxValue h b l)
let rec maxValue_lemma_aux h b l = match l with | 1 -> () | _ -> maxValue_lemma_aux h b (l-1)

val maxValue_lemma: h:heap -> b:bigint{live h b /\ length b > 0} ->
  Lemma (forall (i:nat). {:pattern (v (get h b i))} i < length b ==> v (get h b i) <= maxValue h b (length b))
let rec maxValue_lemma h b = maxValue_lemma_aux h b (length b)

val maxValue_bound_lemma_aux: h:heap -> b:bigint{live h b /\ length b > 0} -> l:pos{l<=length b} -> 
  bound:nat ->  Lemma (requires (forall (i:nat). i < l ==> v (get h b i) <= bound))
	             (ensures (maxValue h b l <= bound))
let rec maxValue_bound_lemma_aux h b l bound = match l with | 1 -> () | _ -> maxValue_bound_lemma_aux h b (l-1) bound

val maxValue_bound_lemma: h:heap -> b:bigint{live h b /\ length b > 0} -> bound:nat ->  
  Lemma (requires (forall (i:nat). i < length b ==> v (get h b i) <= bound))
	(ensures (maxValue h b (length b) <= bound))
let maxValue_bound_lemma h b bound = maxValue_bound_lemma_aux h b (length b) bound

val maxValueNorm: h:heap -> b:bigint{live h b /\ length b >= norm_length} -> GTot nat
let maxValueNorm h b = maxValue h b norm_length

val maxValueIdx: h:heap -> b:bigint{live h b} -> l:pos{l <= length b} -> GTot nat
let rec maxValueIdx h b l =
  match l with 
  | 1 -> 0
  | _ -> if maxValue h b l = v (get h b (l-1)) then l - 1 else maxValueIdx h b (l-1)

#reset-options "--z3rlimit 60"

val maxValue_eq_lemma: 
  ha:heap -> hb:heap -> a:bigint{live ha a} -> b:bigint{live hb b} -> l:pos -> Lemma
    (requires (equal ha a hb b /\ l > 0 /\ l <= length a)) 
    (ensures  (equal ha a hb b /\ l > 0 /\ l <= length a /\ l <= length b /\ maxValue ha a l == maxValue hb b l))
let rec maxValue_eq_lemma ha hb a b l =
  match l with
  | 1 -> ()
  | _ ->
    cut (Seq.index (as_seq ha a) (l - 1) == Seq.index (as_seq hb b) (l - 1));
    cut (v (get ha a (l-1)) == v (get hb b (l-1)));
    maxValue_eq_lemma ha hb a b (l-1)
  
val maxValueNorm_eq_lemma: 
  ha:heap -> hb:heap -> a:bigint{ live ha a /\ length a >= norm_length } -> b:bigint{ live hb b /\ length b >= norm_length } ->
  Lemma 
    (requires (equal ha a hb b)) 
    (ensures (maxValueNorm ha a = maxValueNorm hb b))
let maxValueNorm_eq_lemma ha hb a b = maxValue_eq_lemma ha hb a b norm_length

val eval_eq_lemma: ha:heap -> hb:heap -> a:bigint{live ha a} -> b:bigint{live hb b} ->
  len:nat{ (len <= length a) /\ (len <= length b) } -> Lemma
    (requires ( (forall (i:nat). i < len ==> v (get ha a i) = v (get hb b i)) ))
    (ensures ( eval ha a len = eval hb b len ))
let rec eval_eq_lemma ha hb a b len =
  match len with
  | 0 -> ()
  | _ -> eval_eq_lemma ha hb a b (len-1)

val eval_partial_eq_lemma: ha:heap -> hb:heap -> a:bigint{live ha a} -> b:bigint{live hb b} ->
  ctr:nat -> len:nat{ ctr <= len /\ len <= length a /\ len <= length b} -> Lemma
    (requires (live ha a /\ live hb b
      /\ (forall (i:nat). i < len-ctr ==> get ha a (ctr+i) = get hb b (ctr+i)) ))
    (ensures ( eval ha a len - eval ha a ctr = eval hb b len - eval hb b ctr ))
let rec eval_partial_eq_lemma ha hb a b ctr len =
  if len = ctr then ()
  else 
    begin
      eval_def ha a len;
      eval_def hb b len;
      eval_partial_eq_lemma ha hb a b ctr (len-1)
    end     	 

#reset-options

val eval_null: h:heap -> b:bigint{live h b} -> len:nat{len <= length b} -> Lemma
  (requires (forall (i:nat). {:pattern (v (get h b i))} i < len ==> v (get h b i) = 0))
  (ensures (eval h b len = 0))
let rec eval_null h  b len =
  match len with
  | 0 -> ()
  | _ -> eval_null h b (len-1)

val max_value_of_null_lemma: h:heap -> b:bigint{live h b /\ length b > 0} -> l:pos{l <= length b} -> Lemma
  (requires (null h b))
  (ensures (maxValue h b l = 0))
let rec max_value_of_null_lemma h b l = 
  match l with
  | 1 -> ()
  | _ -> max_value_of_null_lemma h b (l-1)
