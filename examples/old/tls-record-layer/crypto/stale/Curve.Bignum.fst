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
module Curve.Bignum

open FStar.Mul
open FStar.HST
open FStar.HyperStack
open FStar.Ghost
open FStar.UInt64
open FStar.Buffer
open Math.Lib
open Math.Field
open Curve.Parameters
open Curve.Bigint

module U8  = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module HS = FStar.HyperStack

let w: u32 -> Tot int = U32.v
let vv: u128 -> Tot int  = U128.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub

let heap = HS.mem

assume val nat_to_felem: x:nat{x < reveal prime} -> GTot felem
assume val felem_to_nat: felem -> GTot (x:nat{x < reveal prime})
assume val finite_field_implementation: x:nat{x < reveal prime} -> Lemma (felem_to_nat (nat_to_felem x) = x)
assume val felem_lemma: x:nat -> y:nat -> 
  Lemma (requires (True))
	(ensures (nat_to_felem (x % reveal prime) ^+ nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x + y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^- nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x - y) % reveal prime)
		  /\ nat_to_felem (x % reveal prime) ^* nat_to_felem (y % reveal prime) = 
		  nat_to_felem ((x * y) % reveal prime)))
assume val valueOf: h:heap -> b:bigint{live h b} -> GTot (f:felem{f = nat_to_felem ((eval h b norm_length)%reveal prime)})
assume val valueOf_wide: h:heap -> b:bigint_wide{live h b} -> GTot (f:felem{f = nat_to_felem ((eval_wide h b norm_length)%reveal prime)})

(* Equality in the prime field *)
type eq (ha:heap) (a:bigint) (hb:heap) (b:bigint) = 
  live ha a /\ live hb b /\ valueOf ha a = valueOf hb b

type eq_wide_r (ha:heap) (a:bigint) (hb:heap) (b:bigint_wide) = 
  live ha a /\ live hb b /\ valueOf ha a = valueOf_wide hb b

type eq_wide_l (ha:heap) (a:bigint_wide) (hb:heap) (b:bigint) = 
  live ha a /\ live hb b /\ valueOf_wide ha a = valueOf hb b

type eq_wide (ha:heap) (a:bigint_wide) (hb:heap) (b:bigint_wide) =
  live ha a /\ live hb b /\ valueOf_wide ha a = valueOf_wide hb b

val valueOfBytes: h:heap -> b:bytes -> GTot nat
let valueOfBytes h b = eval_bytes h b bytes_length

val cast_lemma_1: x:u128{U128.v x < pow2 platform_size} -> Lemma (U128.v x % pow2 platform_size = U128.v x)
let cast_lemma_1 x = (* BignumLemmas.modulo_lemma_1 (v x) (pow2 platform_size) *)
  ()

val copy_to_bigint': output:bigint -> input:bigint_wide{disjoint input output} -> idx:u32 -> len:u32 -> 
  ctr:u32{w ctr <= w len} -> STL unit
    (requires (fun h -> live h output /\ live h input /\ w idx+w len <= length output /\ w idx+w len<=length input
      /\ (forall (i:nat). {:pattern (vv (get h input i))} (i >= w idx /\ i < w idx+w len) ==> vv (get h input i) < pow2 platform_size)
      /\ (forall (i:nat). i < w ctr ==> v (get h output (w idx+i)) = vv (get h input (w idx+i))) ))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output
      /\ (forall (i:nat). i < w len ==> v (get h1 output (w idx+i)) = vv (get h0 input (w idx+i)))
      /\ modifies_1 output h0 h1 ))
let rec copy_to_bigint' output b idx len ctr = 
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
    let bi = index b (idx+|ctr) in
    let cast = U128.uint128_to_uint64 bi in
    cast_lemma_1 bi;
    cut (v cast = vv bi /\ True); 
    upd output (idx+|ctr) cast; 
    let h1 = HST.get() in
    (* no_upd_lemma h0 h1 b (only output);  *)
    (* upd_lemma h0 h1 output (idx+|ctr) cast;  *)
    copy_to_bigint' output b idx len (ctr+|1ul)
  end

val norm_bigint_lemma_1: h:heap -> b:bigint_wide{norm_wide h b} -> 
  Lemma (requires (True))
	(ensures (forall (i:nat). {:pattern (vv (get h b i))} i < norm_length ==> vv (get h b i) < pow2 platform_size))
let norm_bigint_lemma_1 h b =
  admit(); // TODO
  parameters_lemma_0 ();
  cut (forall (i:nat). {:pattern (vv (get h b i))} i < norm_length ==> templ i < platform_size); 
  admitP(forall (n:nat) (m:nat). {:pattern (get h b)} m < n ==> pow2 m < pow2 n);
  cut (forall (i:nat). {:pattern (vv (get h b i))} i < norm_length ==> vv (get h b i) < pow2 (templ i)); // TODO
  cut (forall (i:nat). {:pattern (vv (get h b i))} i < norm_length ==> vv (get h b i) < pow2 platform_size)
  
val copy_to_bigint:
  output:bigint -> 
  input:bigint_wide{disjoint input output} -> 
  STL unit
    (requires (fun h -> live h output /\ norm_wide h input)) 
    (ensures (fun h0 _ h1 -> norm h1 output /\ norm_wide h0 input 
      /\ modifies_1 output h0 h1
      /\ eval_wide h0 input norm_length % reveal prime = eval h1 output norm_length % reveal prime
      /\ valueOf h1 output = valueOf_wide h0 input))
let copy_to_bigint output b = 
  admit(); // OK
  let h0 = HST.get() in
  norm_bigint_lemma_1 h0 b;
  copy_to_bigint' output b 0ul nlength 0ul; 
  let h1 = HST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 output (0+i)) = vv (get h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> v (get h1 output i) = vv (get h0 b i));
  (* eval_eq_lemma h0 h1 b output norm_length; *)
  cut (eval_wide h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True); 
  cut (norm h1 output); cut(norm_wide h0 b);
  cut (valueOf_wide h0 b = valueOf h1 output /\ True); 
  cut (modifies_1 output h0 h1)
  
val copy_to_bigint_wide': output:bigint_wide -> input:bigint{disjoint input output} -> idx:u32 -> 
  len:u32 -> ctr:u32{w ctr <= w len} -> STL unit
    (requires (fun h -> live h output /\ live h input /\ w idx+w len <= length output /\ w idx+w len<=length input
      /\ (forall (i:nat). i < w ctr ==> vv (get h output (w idx+i)) = v (get h input (w idx+i))) ))
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output
      /\ (forall (i:nat). i < w len ==> vv (get h1 output (w idx+i)) = v (get h0 input (w idx+i)))
      /\ modifies_1 output h0 h1 ))
let rec copy_to_bigint_wide' output b idx len ctr =
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
    let bi = index b (idx+|ctr) in
    let cast = Int.Cast.uint64_to_uint128 bi in
    cut (vv cast = v bi /\ True);
    upd output (idx+|ctr) cast;
    let h1 = HST.get() in
    (* no_upd_lemma h0 h1 b (only output); *)
    (* upd_lemma h0 h1 output (idx+|ctr) cast; *)
    copy_to_bigint_wide' output b idx len (ctr+|1ul)
  end

val copy_to_bigint_wide: output:bigint_wide -> input:bigint{disjoint input output} -> STL unit
    (requires (fun h -> live h output /\ live h input )) 
    (ensures (fun h0 _ h1 -> live h0 output /\ live h1 output
      /\ (forall (i:nat). i < norm_length ==> vv (get h1 output (i)) = v (get h0 input (i)))
      /\ (eq_wide_l h1 output h0 input)
      /\ (modifies_1 output h0 h1)
      /\ (length output = length output) ))
let copy_to_bigint_wide output b = 
  admit(); // OK
  let h0 = HST.get() in
  copy_to_bigint_wide' output b 0ul nlength 0ul; 
  let h1 = HST.get() in
  cut (forall (i:nat). i < norm_length ==> vv (get h1 output (0+i)) = v (get h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> vv (get h1 output i) = v (get h0 b i));
  (* eval_eq_lemma h0 h1 b output norm_length; *)
  cut (eval h0 b norm_length % reveal prime = eval_wide h1 output norm_length % reveal prime /\ True); 
  cut (live h1 output); cut(live h0 b)

val copy_lemma: h0:heap -> h1:heap -> a:bigint_wide -> b:bigint{disjoint a b} -> 
  Lemma (requires (live h0 a /\ norm h0 b 
    /\ (forall (i:nat). i < norm_length ==> vv (get h1 a (i)) = v (get h0 b (i)))))
	(ensures (norm_wide h1 a))
let copy_lemma h0 h1 a b =
  admit(); // OK
  cut (forall (i:nat). i < norm_length ==> vv (get h1 a (0+i)) = v (get h0 b (0+i)));
  assert(forall (i:nat). i < norm_length ==> vv (get h1 a i) = v (get h0 b i))
  
val erase: b:bigint -> idx:u32 -> len:u32 -> ctr:u32{w ctr <= w len} -> STL unit
    (requires (fun h -> live h b /\ length b >= w idx+w len
      /\ (forall (i:nat). {:pattern (v (get h b i))} (i>= w idx /\ i < w idx+w ctr) ==> v (get h b i) = 0)))
    (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ length b >= w idx+w len
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= w idx /\ i < w idx+w len) ==> v (get h1 b i) = 0)
      (* /\ (EqSub h1 b 0 h0 b 0 idx)  *)
      (* /\ (EqSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len))) *)
      /\ modifies_1 b h0 h1 ))
let rec erase b idx len ctr = 
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
    upd b (idx+|ctr) 0uL; 
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b (idx+|ctr) 0uL; *)
    erase b idx len (ctr+|1ul)
  end

val erase_wide: b:bigint_wide -> idx:u32 -> len:u32 -> ctr:u32{w ctr <= w len} -> STL unit 
    (requires (fun h -> live h b /\ length b >= w idx+w len
      /\ (forall (i:nat). {:pattern (vv (get h b i))} (i>= w idx /\ i < w idx+w ctr) ==> vv (get h b i) = 0))) 
    (ensures (fun h0 _ h1 -> 
      (live h0 b) /\ (live h1 b)
      /\ (length b = length b) /\ (length b >= w idx+w len)
      /\ (forall (i:nat). {:pattern (vv (get h1 b i))} (i >= w idx /\ i < w idx+w len) ==> vv (get h1 b i) = 0)
      (* /\ (EqSub h1 b 0 h0 b 0 idx) /\ (EqSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len))) *)
      /\ (modifies_1 b h0 h1) ))
let rec erase_wide b idx len ctr = 
  admit(); // OK
  let h0 = HST.get() in
  if U32.eq len ctr then ()
  else begin
    upd b (idx+|ctr) (UInt128.of_string "0"); 
    let h1 = HST.get() in
    (* upd_lemma h0 h1 b (idx+|ctr) (UInt128.of_string "0"); *)
    erase_wide b idx len (ctr+|1ul)
  end

let modifies_2 c tmp h0 h1 =
  HyperHeap.modifies_just (Set.union (Set.singleton (frameOf c)) (Set.singleton (frameOf tmp))) h0.h h1.h
  /\ modifies_bufs (frameOf c) (only c ++ only tmp) h0 h1
  /\ modifies_bufs (frameOf tmp) (only c ++ only tmp) h0 h1
  /\ h0.tip = h1.tip

val modulo: output:bigint -> input:bigint_wide{disjoint input output} -> STL unit
    (requires (fun h -> live h input /\ live h output (* /\ satisfies_modulo_constraints h input *)
      /\ length input >= 2*norm_length - 1 )) 
    (ensures (fun h0 _ h1 -> live h0 input /\ length input >= 2*norm_length-1
      /\ norm h1 output /\ live h0 input
      /\ eval h1 output norm_length % reveal prime = eval_wide h0 input (2*norm_length-1) % reveal prime
      /\ modifies_2 output input h0 h1 ))
let modulo output b = 
  admit(); // OK
  let h0 = HST.get() in
  Curve.Modulo.freduce_degree b; 
  Curve.Modulo.freduce_coefficients b; 
  let h = HST.get() in
  (* standardized_eq_norm h b; *)
  copy_to_bigint output b

#reset-options

val fsum_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b)))
let fsum_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

#reset-options

val fsum: a:bigint{templ = templ} -> b:bigint{disjoint a b} -> STL unit
    (requires (fun h -> (norm h a) /\ (norm h b) ))
    (ensures (fun h0 _ h1 -> 
      (norm h0 a) /\ (norm h1 a) /\ (norm h0 b)
      /\ (valueOf h1 a = (valueOf h0 a ^+ valueOf h0 b))
      /\ (modifies_1 a h0 h1) ))
let fsum a b =
  push_frame ();
  admit(); // TODO
  let h0 = HST.get() in
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b;  *)
  Curve.Fsum.fsum' a b; 
  let tmp = create (U128.of_string "0") (9ul) in 
  let h1 = HST.get() in
  copy_to_bigint_wide tmp a; 
  cut (forall (i:nat). {:pattern (v (get h1 a i))} i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i));
  let h2 = HST.get() in 
  cut (forall (i:nat). {:pattern (vv (get h2 tmp i))} i < norm_length ==> vv (get h2 tmp (0+i)) = 
	 v (get h1 a (0+i))); 
  cut (forall (i:nat). {:pattern (vv (get h2 tmp i))} i < norm_length ==> vv (get h2 tmp i) = 
      v (get h0 a i) + v (get h0 b i)); 
  admitP (forall (i:nat). {:pattern (vv (get h2 tmp i))} (i >= norm_length /\ i < length tmp) ==> vv (get h2 tmp i) = 0);
  Curve.Modulo.sum_satisfies_constraints h0 h2 tmp a b; 
  modulo a tmp; 
  let h1 = HST.get() in
  assert(valueOf h1 a = valueOf_wide h2 tmp); 
  cut (True /\ eval h1 a norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime); // TODO
  fsum_lemma h0 h1 a a b;
  cut(modifies_1 a h0 h1);
  pop_frame()

#reset-options

val fdifference_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b))) 
let fdifference_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

#reset-options

val fdifference: a:bigint{templ = templ} -> b:bigint{disjoint a b} -> STL unit 
    (requires (fun h -> (norm h a) /\ (norm h b))) 
    (ensures (fun h0 _ h1 -> 
      (norm h0 a) /\ (norm h0 b) /\ (norm h1 a)
      /\ (valueOf h1 a = (valueOf h0 b ^- valueOf h0 a))
      /\ (modifies_1 a h0 h1)  ))
let fdifference a b = 
  push_frame ();
  admit(); // TODO
  let h0 = HST.get() in
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b; *)
  let b' = create 0uL nlength in
  blit b 0ul b' 0ul nlength;
  (* let b' = Bigint.copy b in  *)
  let h1 = HST.get() in
  Curve.Modulo.add_big_zero b';
  let h2 = HST.get() in
  cut (modifies_1 b' h0 h2); 
  (* no_upd_lemma h0 h2 a (only b');  *)
  cut (norm h2 a); 
  Curve.Fdifference.fdifference' a b'; 
  let h3 = HST.get() in
  let tmp = create (U128.of_string "0") (U32.mul 2ul nlength-|1ul) in 
  let h4 = HST.get() in
  copy_to_bigint_wide tmp a; 
  let h5 = HST.get() in 
  cut(live h5 a /\ (forall (i:nat). (i>=norm_length /\ i < length tmp) ==> vv (get h5 tmp i) = 0));
  Curve.Modulo.difference_satisfies_constraints h2 h5 tmp b' a; 
  modulo a tmp; 
  let h6 = HST.get() in
  cut (True /\ eval h6 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime);
  fdifference_lemma h0 h6 a b a;
  cut (modifies_1 a h0 h6);
  pop_frame()

#reset-options

val fscalar:
    res:bigint -> b:bigint{disjoint res b} -> s:u64{v s < templ 0} -> ST unit
  (requires (fun h -> (live h res) /\ (norm h b)))
  (ensures (fun h0 _ h1 -> 
    (norm h0 b) /\ (live h0 b) /\ (norm h1 res)
    /\ (valueOf h1 res = (v s +* valueOf h0 b))
    /\ (modifies_1 res h0 h1) ))
let fscalar res b s =
  push_frame ();
  admit(); // TODO
  let h0 = HST.get() in
  (* standardized_eq_norm h0 b;  *)
  let tmp = create (U128.of_string "0") (U32.mul 2ul nlength-|1ul) in
  Curve.Fscalar.scalar' tmp b s; 
  let h = HST.get() in
  (* admitP(b2t(satisfies_modulo_constraints h tmp));   *)
  modulo res tmp;
  let h1 = HST.get() in
  admitP(True /\ (valueOf h1 res = (v s +* valueOf h0 b)));
  pop_frame()

#reset-options

// TODO
assume val norm_lemma_2: h:heap -> b:bigint -> 
  Lemma (requires (norm h b))
	(ensures (norm h b /\ maxValueNorm h b < pow2 Curve.Fproduct.max_limb))

val fmul_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))) []
let fmul_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fmul: res:bigint -> a:bigint{disjoint res a} -> b:bigint{disjoint res b} -> STL unit 
    (requires (fun h -> live h res /\ norm h a /\ norm h b)) 
    (ensures (fun h0 _ h1 -> norm h0 a /\ norm h0 b /\ norm h1 res
      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))
      /\ (modifies_1 res h0 h1) ))
let fmul res a b = 
  push_frame ();
  admit(); // TODO
  let h0 = HST.get() in
  (* standardized_eq_norm h0 a; standardized_eq_norm h0 b;  *)
  let tmp = create (U128.of_string "0") (U32.mul 2ul nlength-|1ul) in
  let h1 = HST.get() in  
  (* no_upd_lemma h0 h1 a !{}; *)
  (* no_upd_lemma h0 h1 b !{}; *)
  norm_lemma_2 h1 a; norm_lemma_2 h1 b; 
  (* norm_lemma_3 h1 a; norm_lemma_3 h1 b; *)
  Curve.Fproduct.multiplication tmp a b; 
  let h2 = HST.get() in
  Curve.Modulo.mul_satisfies_constraints h1 h2 tmp a b; 
  modulo res tmp;
  let h3 = HST.get() in
  cut (True /\ eval h3 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime);
  fmul_lemma h0 h3 res a b;
  pop_frame()

val fsquare: res:bigint -> a:bigint{disjoint res a} -> STL unit 
    (requires (fun h -> (live h res) /\ (norm h a))) 
    (ensures (fun h0 _ h1 -> 
      (norm h0 a) /\ (live h0 res) /\ (norm h1 res)
      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 a))
      /\ (modifies_1 res h0 h1)
    ))
let fsquare res a =
  fmul res a a
