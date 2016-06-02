module Bignum.Core

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
open Bignum.Fdifference
open Bignum.Fscalar
open Bignum.Fproduct
open Bignum.Modulo

#set-options "--lax"

// TODO: dummy while proof not rewritten
val valueOf: h:FStar.Heap.heap -> #size:pos -> b:buffer size{live h b} -> GTot nat
let valueOf h #size b = eval h b norm_length % reveal prime

(*
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
assume val valueOf: h:FStar.Heap.heap -> #size:pos -> b:biginteger size{live h b} -> GTot (f:felem{f = nat_to_felem ((eval h #size b norm_length)%reveal prime)})

(* Equality in the prime field *)
type equal (ha:FStar.Heap.heap) (#size_a:pos) (a:biginteger size_a) 
	(hb:FStar.Heap.heap) (#size_b:pos) (b:biginteger size_b) = 
  live ha a /\ live hb b /\ getLength ha a >= norm_length /\ getLength hb b >= norm_length
  /\ valueOf ha a == valueOf hb b
*)

let eq' (ha:FStar.Heap.heap) (#size_a:pos) (a:buffer size_a) (la:pos) (hb:FStar.Heap.heap) (#size_b:pos) (b:buffer size_b) (lb:pos) = 
  live ha a /\ live hb b /\ length a >= la /\ length b >= lb 
  /\ eval ha a la % (reveal prime) = eval hb b lb % (reveal prime)

(* Serialized values, received and sent to other parties *)
abstract let serialized (h:FStar.Heap.heap) (b:buffer 8) = live h b /\ length b = bytes_length

val valueOfBytes: h:FStar.Heap.heap -> b:buffer 8{serialized h b} -> GTot nat
let valueOfBytes h b = eval h b bytes_length

val cast_lemma_1: x:wide{v x < pow2 platform_size} -> Lemma 
  (requires (True)) (ensures (v x % pow2 platform_size = v x)) 
let cast_lemma_1 x = 
  ()
  //BignumLemmas.modulo_lemma_1 (v x) (pow2 platform_size)

(*
val copy_to_bigint':
  output:bigint -> input:bigint_wide{Similar input output} -> idx:nat -> len:nat -> ctr:nat{ctr <= len} ->
  ST unit
    (requires (fun h -> 
      (live h output) /\ (live h input) /\ (idx+len <= length h output) /\ (idx+len<=length h input)
      /\ (forall (i:nat). {:pattern (v (get h input i))} (i >= idx /\ i < idx+len) ==> v (get h input i) < pow2 platform_size) 
      /\ (EqSub h output idx h input idx ctr)
))
    (ensures (fun h0 _ h1 -> 
      live h0 output /\ live h1 output
      /\ (EqSub h1 output idx h0 input idx len)
      /\ (modifies !{getRef output} h0 h1)
      /\ (length h0 output = length h1 output)
    ))
let rec copy_to_bigint' output b idx len ctr = 
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    let bi = index_wide b (idx+ctr) in
    let cast = wide_to_limb bi in
    cast_lemma_1 bi;
    cut (v cast = v bi /\ True); 
    upd_limb output (idx+ctr) cast; 
    let h1 = ST.get() in
    no_upd_lemma h0 h1 b !{getRef output}; 
    upd_lemma h0 h1 output (idx+ctr) cast; 
    copy_to_bigint' output b idx len (ctr+1)

val norm_bigint_lemma_1: h:heap -> b:bigint_wide{norm h b} -> 
  Lemma (requires (True))
	(ensures (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 platform_size))
let norm_bigint_lemma_1 h b =
  parameters_lemma_0 ();
  cut (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> templ i < platform_size); 
  admitP(forall (n:nat) (m:nat). {:pattern (get h b)} m < n ==> pow2 m < pow2 n);
  cut (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 (templ i));
  cut (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 platform_size)
  
val copy_to_bigint:
  output:bigint -> 
  input:bigint_wide{Similar input output} -> 
  ST unit
    (requires (fun h -> (live h output) /\ (norm h input))) 
    (ensures (fun h0 _ h1 -> norm h1 output /\ norm h0 input /\ (modifies !{getRef output} h0 h1)
      /\ eval h0 input norm_length % reveal prime = eval h1 output norm_length % reveal prime
      /\ valueOf h1 output = valueOf h0 input))
let copy_to_bigint output b = 
  let h0 = ST.get() in
  norm_bigint_lemma_1 h0 b;
  copy_to_bigint' output b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 output (0+i)) = v (get h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> v (get h1 output i) = v (get h0 b i));
  eval_eq_lemma h0 h1 b output norm_length;
  cut (eval h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True); 
  cut (norm h1 output); cut(norm h0 b);
  cut (valueOf h0 b = valueOf h1 output /\ True); cut (modifies !{getRef output} h0 h1)
  
val copy_to_bigint_wide':
  output:bigint_wide -> 
  input:bigint{Similar input output} -> idx:nat -> len:nat -> ctr:nat{ctr <= len} ->
  ST unit
    (requires (fun h -> 
      (live h output) /\ (live h input) /\ (idx+len <= length h output) /\ (idx+len<=length h input)
      /\ (EqSub h output idx h input idx ctr) ))
    (ensures (fun h0 _ h1 -> 
      live h0 output /\ live h1 output
      /\ (EqSub h1 output idx h0 input idx len)
      /\ (modifies !{getRef output} h0 h1)
      /\ (length h0 output = length h1 output)
    ))
let rec copy_to_bigint_wide' output b idx len ctr = 
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    let bi = index_limb b (idx+ctr) in
    let cast = limb_to_wide bi in
    cut (v cast = v bi /\ True);
    upd_wide output (idx+ctr) cast;
    let h1 = ST.get() in
    no_upd_lemma h0 h1 b !{getRef output};
    upd_lemma h0 h1 output (idx+ctr) cast;
    copy_to_bigint_wide' output b idx len (ctr+1)

val copy_to_bigint_wide:
  output:bigint_wide -> 
  input:bigint{Similar input output} -> 
  ST unit
    (requires (fun h -> 
      (live h output) /\ (live h input)
    )) 
    (ensures (fun h0 _ h1 -> 
      live h0 output /\ live h1 output
      /\ (EqSub h1 output 0 h0 input 0 norm_length)
      /\ (equal h1 output h0 input)
      /\ (modifies !{getRef output} h0 h1)
      /\ (length h0 output = length h1 output)
    ))
let copy_to_bigint_wide output b = 
  let h0 = ST.get() in
  copy_to_bigint_wide' output b 0 norm_length 0; 
  let h1 = ST.get() in
  cut (forall (i:nat). i < norm_length ==> v (get h1 output (0+i)) = v (get h0 b (0+i))); 
  cut (forall (i:nat). i < norm_length ==> v (get h1 output i) = v (get h0 b i));
  eval_eq_lemma h0 h1 b output norm_length;
  cut (eval h0 b norm_length % reveal prime = eval h1 output norm_length % reveal prime /\ True); 
  cut (live h1 output); cut(live h0 b)

val copy_lemma: h0:heap -> h1:heap -> #sa:pos -> a:biginteger sa -> #sb:pos -> b:biginteger sb{Similar a b} -> 
  Lemma (requires (live h0 a /\ norm h0 b /\ EqSub h1 a 0 h0 b 0 norm_length))
	(ensures (norm h1 a))
let copy_lemma h0 h1 #sa a #sb b =
  cut (forall (i:nat). i < norm_length ==> v (get h1 a (0+i)) = v (get h0 b (0+i)));
  assert(forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 b i)); 
  assert(forall (i:nat). getTemplate b i = getTemplate a i)
*)  

val erase: b:bigint -> idx:nat -> len:nat{length b >= idx+len} -> ctr:nat{ctr <= len} -> ST unit 
    (requires (fun h -> (live h b) 
      /\ (forall (i:nat). {:pattern (v (get h b i))} (i>= idx /\ i < idx+ctr) ==> v (get h b i) = 0))) 
    (ensures (fun h0 _ h1 -> 
      (live h0 b) /\ (live h1 b)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= idx /\ i < idx+len) ==> v (get h1 b i) = 0)
      /\ (equalSub h1 b 0 h0 b 0 idx) /\ (equalSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len)))
      /\ (modifies_buf (only b) h0 h1)
    ))
let rec erase b idx len ctr = 
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    upd b (idx+ctr) zero; 
    let h1 = ST.get() in
//    upd_lemma h0 h1 b (idx+ctr) zero_limb;
    erase b idx len (ctr+1)

val erase_wide: b:bigint_wide -> idx:nat -> len:nat{length b >= idx+len} -> ctr:nat{ctr <= len} -> ST unit 
    (requires (fun h -> (live h b)
      /\ (forall (i:nat). {:pattern (v (get h b i))} (i>= idx /\ i < idx+ctr) ==> v (get h b i) = 0))) 
    (ensures (fun h0 _ h1 -> 
      (live h0 b) /\ (live h1 b)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= idx /\ i < idx+len) ==> v (get h1 b i) = 0)
      /\ (equalSub h1 b 0 h0 b 0 idx) /\ (equalSub h1 b (idx+len) h0 b (idx+len) (length b-(idx+len)))
      /\ (modifies_buf (only b) h0 h1)  ))
let rec erase_wide b idx len ctr = 
  let h0 = ST.get() in
  match len - ctr with
  | 0 -> ()
  | _ -> 
    upd b (idx+ctr) zero_wide; 
    let h1 = ST.get() in
//    upd_lemma h0 h1 b (idx+ctr) zero_wide;
    erase_wide b idx len (ctr+1)

(*
#reset-options

val modulo:
  output:bigint{getTemplate output = templ} -> 
  input:bigint_wide{disjoint input output} -> 
  ST unit
    (requires (fun h -> 
      (live h input) /\ (live h output) /\ (satisfies_modulo_constraints h input)
      /\ length h input >= 2*norm_length - 1
    )) 
    (ensures (fun h0 _ h1 -> (live h0 input) /\ length h0 input >= 2*norm_length-1
      /\ (norm h1 output) /\ (live h0 input)
      /\ eval h1 output norm_length % reveal prime = eval h0 input (2*norm_length-1) % reveal prime
      /\ (modifies_buf !{getRef output, getRef input} h0 h1)
    ))
let modulo output b = 
  let h0 = ST.get() in
  freduce_degree b; 
  freduce_coefficients b; 
  let h = ST.get() in
  standardized_eq_norm h b;
  copy_to_bigint output b

#reset-options

abstract val gfsum_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b))) []
let gfsum_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fsum_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b)))
let fsum_lemma h0 h1 res a b =
  coerce   (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^+ valueOf h0 b))) 
   (fun _ -> gfsum_lemma h0 h1 res a b)
*)

val fsum:
  a:bigint -> b:bigint{disjoint a b} -> ST unit
    (requires (fun h -> (norm h a) /\ (norm h b) ))
    (ensures (fun h0 _ h1 -> (norm h0 a) /\ (norm h1 a) /\ (norm h0 b)
//      /\ (valueOf h1 a = (valueOf h0 a ^+ valueOf h0 b))
      /\ (modifies_buf (only a) h0 h1) ))
let fsum a b =
  let h0 = ST.get() in
//  standardized_eq_norm h0 a; standardized_eq_norm h0 b; 
  Fsum.fsum' a b;
  freduce_coefficients a;
  ()
  (*
  let tmp = create #(platform_wide) (2*norm_length-1) in 
  let h1 = ST.get() in
  copy_to_bigint_wide tmp a; 
  cut (forall (i:nat). {:pattern (v (get h1 a i))} i < norm_length ==> v (get h1 a i) = v (get h0 a i) + v (get h0 b i));
  let h2 = ST.get() in 
  cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp (0+i)) = 
	 v (get h1 a (0+i))); 
  cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp i) = 
      v (get h0 a i) + v (get h0 b i)); 
  admitP (forall (i:nat). {:pattern (v (get h2 tmp i))} (i >= norm_length /\ i < length h2 tmp) ==> v (get h2 tmp i) = 0);
  sum_satisfies_constraints h0 h2 tmp a b; 
  modulo a tmp; 
  let h1 = ST.get() in
  assert(valueOf h1 a = valueOf h2 tmp); 
  cut (True /\ eval h1 a norm_length % reveal prime = (eval h0 a norm_length + eval h0 b norm_length) % reveal prime);
  fsum_lemma h0 h1 a a b;
  cut(modifies_buf !{getRef a} h0 h1)
*)

(*
abstract val gfdifference_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b))) []
let gfdifference_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fdifference_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b)))
let fdifference_lemma h0 h1 res a b =
  coerce   (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length - eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^- valueOf h0 b))) 
   (fun _ -> gfdifference_lemma h0 h1 res a b)
*)

val fdifference:
  a:bigint -> b:bigint{disjoint a b} ->  ST unit 
    (requires (fun h -> (norm h a) /\ (norm h b))) 
    (ensures (fun h0 _ h1 ->  (norm h0 a) /\ (norm h0 b) /\ (norm h1 a)
//      /\ (valueOf h1 a = (valueOf h0 b ^- valueOf h0 a))
      /\ (modifies_buf (only a) h0 h1) ))
let fdifference a b =
  let h0 = ST.get() in
//  standardized_eq_norm h0 a; standardized_eq_norm h0 b; 
  let b' = create #64 zero norm_length in
  blit b 0 b' 0 norm_length;
//  let b' = Bigint.copy b in 
  let h1 = ST.get() in
  add_big_zero b';
  let h2 = ST.get() in
  cut (modifies_buf (only b') h0 h2); 
  eq_lemma h0 h2 a (only b'); 
  cut (norm h2 a); 
  fdifference' a b'; 
  freduce_coefficients a;
  ()

(*
  let h3 = ST.get() in
  let tmp = create_wide (2*norm_length-1) in 
  let h4 = ST.get() in
  copy_to_bigint_wide tmp a; 
  let h5 = ST.get() in 
  admitP(live h5 a /\ (forall (i:nat). (i>=norm_length /\ i < length h5 tmp) ==> v (get h5 tmp i) = 0));
  difference_satisfies_constraints h2 h5 tmp b' a; 
  modulo a tmp; 
  let h6 = ST.get() in
  cut (True /\ eval h6 a norm_length % reveal prime = (eval h0 b norm_length - eval h0 a norm_length) % reveal prime);
  fdifference_lemma h0 h6 a b a;
  admitP (modifies_buf !{getRef a} h0 h6)
*)

val fscalar:
  res:bigint -> b:bigint{disjoint res b} -> #n:nat{n <= ndiff'} -> s:limb{v s < pow2 n} -> ST unit
  (requires (fun h -> (live h res) /\ (norm h b)))
  (ensures (fun h0 _ h1 -> 
    (norm h0 b) /\ (live h0 b) /\ (norm h1 res)
//    /\ (valueOf h1 res = (v s +* valueOf h0 b))
    /\ (modifies_buf (only res) h0 h1) ))
let fscalar res b #n s =
  let h0 = ST.get() in
//  standardized_eq_norm h0 b; 
  let tmp = create #128 zero_wide (2*norm_length-1) in
  scalar_multiplication tmp b s; 
  let h = ST.get() in
//  admitP(b2t(satisfies_modulo_constraints h tmp));  
  modulo res tmp;
  let h1 = ST.get() in ()
  //admitP(True /\ (valueOf h1 res = (v s +* valueOf h0 b)))

(*
assume val norm_lemma_2: h:heap -> b:bigint -> 
  Lemma (requires (norm h b))
	(ensures (norm h b /\ maxValuenorm h b < pow2 Fproduct.max_limb))

val norm_lemma_3: h:heap -> b:bigint -> 
  Lemma (requires (norm h b))
	(ensures (norm h b))
let norm_lemma_3 h b = 
  admit();
  cut(forall (i:nat). i < norm_length ==> bitsize (v (get h b i)) (getTemplate b i));
  admitP (forall (i:nat). {:pattern (v (get h b i))} templ i = getTemplate b i); 
  cut(forall (i:nat). i < norm_length ==> bitsize (v (get h b i)) (templ i))

abstract val gfmul_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> GLemma unit
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))) []
let gfmul_lemma h0 h1 res a b =
  felem_lemma (eval h0 a norm_length) (eval h0 b norm_length)

val fmul_lemma: h0:heap -> h1:heap -> res:bigint -> a:bigint -> b:bigint -> Lemma 
  (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b)))
let fmul_lemma h0 h1 res a b =
  coerce   (requires (norm h0 a /\ norm h0 b /\ norm h1 res
    /\ eval h1 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime ))
  (ensures (norm h0 a /\ norm h0 b /\ norm h1 res
   /\ valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))) 
   (fun _ -> gfmul_lemma h0 h1 res a b)
*)

val fmul: res:bigint -> a:bigint{disjoint res a} -> b:bigint{disjoint res b} -> ST unit 
    (requires (fun h -> (live h res) /\ (norm h a) /\ (norm h b))) 
    (ensures (fun h0 _ h1 -> 
      (norm h0 a) /\ (norm h0 b) /\ (norm h1 res)
//      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 b))
      /\ (modifies_buf (only res) h0 h1)  ))
let fmul res a b =
  let h0 = ST.get() in
//  standardized_eq_norm h0 a; standardized_eq_norm h0 b; 
  let tmp = create #128 zero_wide (2*norm_length-1) in
  let h1 = ST.get() in  
  eq_lemma h0 h1 a empty;
  eq_lemma h0 h1 b empty;
//  norm_lemma_2 h1 a; norm_lemma_2 h1 b; 
//  norm_lemma_3 h1 a; norm_lemma_3 h1 b;
  multiplication tmp a b; 
  let h2 = ST.get() in
//  mul_satisfies_constraints h1 h2 tmp a b; 
  modulo res tmp;
  let h3 = ST.get() in ()
//  cut (True /\ eval h3 res norm_length % reveal prime = (eval h0 a norm_length * eval h0 b norm_length) % reveal prime);
//  fmul_lemma h0 h3 res a b

val fsquare:
  res:bigint -> a:bigint{disjoint res a} -> ST unit 
    (requires (fun h -> (live h res) /\ (norm h a))) 
    (ensures (fun h0 _ h1 -> 
      (norm h0 a) /\ (live h0 res) /\ (norm h1 res)
//      /\ (valueOf h1 res = (valueOf h0 a ^* valueOf h0 a))
      /\ (modifies_buf (only res) h0 h1) ))
let fsquare res a =
  fmul res a a

val loop:
  tmp:bigint -> v:bigint -> ctr:nat -> ST unit (requires (fun h -> True)) (ensures (fun h0 _ h1 -> True))
let rec loop tmp v ctr =
  match ctr with
  | 0 -> ()
  | _ ->
    fsquare tmp v;
    fsquare v tmp;
    loop tmp v (ctr-1);
    ()

val crecip':
  output:bigint -> z:bigint -> St unit
let crecip' output z = 
  let z2 = create #64 zero norm_length in
  let z9 = create #64 zero norm_length in
  let z11 = create #64 zero norm_length in
  let z2_5_0 = create #64 zero norm_length in
  let z2_10_0 = create #64 zero norm_length in
  let z2_20_0 = create #64 zero norm_length in
  let z2_50_0 = create #64 zero norm_length in
  let z2_100_0 = create #64 zero norm_length in
  let t0 = create #64 zero norm_length in
  let t1 = create #64 zero norm_length in
  fsquare z2 z;  (* 2 *)
  fsquare t1 z2;  (* 4 *)
  fsquare t0 t1;   (* 8 *)
  fmul z9 t0 z;  (* 9 *)
  fmul z11 z9 z2;  (* 11 *)
  fsquare t0 z11;  (* 22 *)
  fmul z2_5_0 t0 z9;  (* 2^5 - 2^0 = 31 *)	  
  fsquare t0 z2_5_0;  (* 2^6 - 2^1 *)
  fsquare t1 t0;  (* 2^7 - 2^2 *)
  fsquare t0 t1;  (* 2^8 - 2^3 *)
  fsquare t1 t0;  (* 2^9 - 2^4 *)
  fsquare t0 t1;  (* 2^10 - 2^5 *)
  fmul z2_10_0 t0 z2_5_0;  (* 2^10 - 2^0 *)	  
  fsquare t0 z2_10_0;  (* 2^11 - 2^1 *)
  fsquare t1 t0;  (* 2^12 - 2^2 *)
  loop t0 t1 4;  (* 2^20 - 2^10 *)	  
  fmul z2_20_0 t1 z2_10_0;  (* 2^20 - 2^0 *)   
  fsquare t0 z2_20_0;  (* 2^21 - 2^1 *) 
  fsquare t1 t0;  (* 2^22 - 2^2 *) 
  loop t0 t1 9;  (* 2^40 - 2^20 *)
  fmul t0 t1 z2_20_0;  (* 2^40 - 2^0 *)   
  fsquare t1 t0;  (* 2^41 - 2^1 *) 
  fsquare t0 t1;  (* 2^42 - 2^2 *) 
  loop t1 t0 4;  (* 2^50 - 2^10 *)  
  fmul z2_50_0 t0 z2_10_0;  (* 2^50 - 2^0 *)   
  fsquare t0 z2_50_0;  (* 2^51 - 2^1 *) 
  fsquare t1 t0;  (* 2^52 - 2^2 *) 
  loop t0 t1 24;  (* 2^100 - 2^50 *)  
  fmul z2_100_0 t1 z2_50_0;  (* 2^100 - 2^0 *)   
  fsquare t1 z2_100_0;  (* 2^101 - 2^1 *) 
  fsquare t0 t1;  (* 2^102 - 2^2 *) 
  loop t1 t0 49;  (* 2^200 - 2^100 *)  
  fmul t1 t0 z2_100_0;  (* 2^200 - 2^0 *) 
  fsquare t0 t1;  (* 2^201 - 2^1 *) 
  fsquare t1 t0;  (* 2^202 - 2^2 *) 
  loop t0 t1 24;  (* 2^250 - 2^50 *)  
  fmul t0 t1 z2_50_0;  (* 2^250 - 2^0 *)   
  fsquare t1 t0;  (* 2^251 - 2^1 *) 
  fsquare t0 t1;  (* 2^252 - 2^2 *) 
  fsquare t1 t0;  (* 2^253 - 2^3 *) 
  fsquare t0 t1;  (* 2^254 - 2^4 *) 
  fsquare t1 t0;  (* 2^255 - 2^5 *) 
  fmul output t1 z11;  (* 2^255 - 21 *) 
  ()
