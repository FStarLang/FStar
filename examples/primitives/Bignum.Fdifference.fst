module Bignum.Fdifference

open FStar.Heap
open FStar.Ghost
open IntLib
open Sint
open SBuffer
open FStar.UInt64
open Bignum.Parameters
open Bignum.Bigint

val helper_lemma_1:
  i:nat -> len:nat -> x:erased nat -> 
  Lemma (requires (i < len /\ len <= reveal x)) (ensures (i < reveal x))
let helper_lemma_1 i len v = ()  

#reset-options

val fdifference_aux_1:
  a:bigint -> b:bigint{Disjoint a b} -> ctr:nat{ctr < norm_length} ->
  ST unit
    (requires (fun h -> 
      Live h a /\ Live h b
      /\ (forall (i:nat{ i >= ctr /\ i < norm_length}). {:pattern (v (get h b i))} 
	  v (get h b i) >= v (get h a i))))
    (ensures (fun h0 _ h1 -> 
      Live h0 a /\ Live h1 a /\ Live h0 b /\ Live h1 b /\ Modifies (only a) h0 h1
      /\ (forall (i:nat). (i >= ctr+1 /\ i < norm_length) ==>  
	  (v (get h1 b i) >= v (get h1 a i) /\ v (get h1 a i) = v (get h0 a i))
          /\ (((i<ctr \/ i>=norm_length) /\ i<length a) ==> v (get h1 a i) = v (get h0 a i)))
      /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)))
let fdifference_aux_1 a b ctr =
  admit();
  let h0 = ST.get() in
  let i = ctr in
  Bignum.FdifferenceLemmas.helper_lemma_3 i norm_length; 
  helper_lemma_1 i norm_length (elength a); 
  helper_lemma_1 i norm_length (elength b); 
  let ai = index a i in 
  let bi = index b i in 
  assert(i >= ctr /\ i < norm_length); 
  cut(b2t(v (get h0 b i) >= v (get h0 a i))); 
  let z = bi ^- ai in 
  upd a i z;
  let h1 = ST.get() in
  eq_lemma h0 h1 b (only a)
  
val fdifference_aux_2_0: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma (requires (
      Live h0 a /\ Live h1 a /\ Live h2 a /\ Live h0 b /\ Live h1 b /\ Live h2 b
      /\ Modifies (only a) h0 h1 /\ Modifies (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (Modifies (only a) h1 h2)
      /\ (forall (i:nat).
	  ((i>=ctr+1 /\ i<norm_length) ==> (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==>
	    v (get h1 b i) >= v (get h1 a i) /\ get h1 a i == get h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i))
      /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)))
    (ensures (
      (Live h0 a) /\ (Live h0 b) /\ (Live h2 a) /\ (Live h2 b)
      /\ (Modifies (only a) h0 h2)
      /\ (forall (i:nat). (i>= ctr /\ i<norm_length) ==> (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))
      ))      
let fdifference_aux_2_0 h0 h1 h2 a b ctr =
  admit();
  eq_lemma h0 h1 b (only a);
  assert(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)));  
  assert(forall (i:nat). (i>=ctr+1 /\ i < norm_length) ==> get h1 a i == get h0 a i); 
  assert(get h2 a ctr == get h1 a ctr); 
  assert(v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr));
  cut(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (get h2 a i) = v (get h0 b i) - v (get h0 a i))); 
  cut(True /\ v (get h2 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)); 
  FdifferenceLemmas.helper_lemma_5 ctr norm_length;
  assert(forall (i:nat). (i>=ctr /\ i < norm_length) ==>
	   (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))

#reset-options

val fdifference_aux_2_1:
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma 
    (requires (
      Live h0 a /\ Live h1 a /\ Live h2 a /\ Live h0 b /\ Live h1 b /\ Live h2 b
      /\ Modifies (only a) h0 h1 /\ Modifies (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (Modifies (only a) h1 h2)
      /\ (forall (i:nat).
	  ((i>=ctr+1 /\ i<norm_length) ==> (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==>
	    v (get h1 b i) >= v (get h1 a i) /\ get h1 a i == get h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i))
      /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)))
    (ensures (
      (Live h0 a) /\ (Live h0 b) /\ (Live h2 a) /\ (Live h2 b)
      /\ (Modifies (only a) h0 h2)
      /\ (forall (i:nat). ((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i)) ))
let fdifference_aux_2_1 h0 h1 h2 a b ctr = 
  admit();
  ()
  
val fdifference_aux_2: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{Disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma
    (requires (
      Live h0 a /\ Live h1 a /\ Live h2 a /\ Live h0 b /\ Live h1 b /\ Live h2 b
      /\ Modifies (only a) h0 h1 /\ Modifies (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (Modifies (only a) h1 h2)
      /\ (forall (i:nat). 
	  ((i>= ctr+1 /\ i<norm_length) ==>
	    (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)))
	  /\ (((i<ctr+1 \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h1 a i)))
      // Conditions from fdifference_aux_1
      /\ (forall (i:nat).
	  ((i >= ctr+1 /\ i < norm_length) ==> v (get h1 b i) >= v (get h1 a i)
						/\ get h1 a i == get h0 a i)
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> get h1 a i == get h0 a i))
      /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)))
    (ensures (
      (Live h0 a) /\ (Live h0 b) /\ (Live h2 a) /\ (Live h2 b)
      /\ (Modifies (only a) h0 h2)
      /\ (forall (i:nat).
	  ((i>= ctr /\ i<norm_length) ==> 
	    (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i)))
      ))      
let fdifference_aux_2 h0 h1 h2 a b ctr =
  admit();
  fdifference_aux_2_0 h0 h1 h2 a b ctr;
  fdifference_aux_2_1 h0 h1 h2 a b ctr

#reset-options

val fdifference_aux:
  a:bigint -> b:bigint{Disjoint a b} -> 
  ctr:nat{ ctr <= norm_length } ->
  ST unit
    (requires (fun h ->
      (Live h a) /\ (Live h b)
      /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> (v (get h b i) >= v (get h a i)))
    ))
    (ensures (fun h0 _ h1 -> 
      (Live h0 a) /\ (Live h0 b) /\ (Live h1 a) /\ (Live h1 b)
      /\ (Modifies (only a) h0 h1)
      /\ (forall (i:nat). 
	  ((i>= ctr /\ i<norm_length) ==>  
	    (v (get h1 a i) = v (get h0 b i) - v (get h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h1 a i == get h0 a i)))
    ))
let rec fdifference_aux a b ctr =
  admit();
  let h0 = ST.get() in
  match norm_length - ctr with
  | 0 -> 
    ()
  | _ ->       
      fdifference_aux_1 a b ctr; 
      let h1 = ST.get() in
      eq_lemma h0 h1 b ((only a));
      fdifference_aux a b (ctr+1); 
      let h2 = ST.get() in
      fdifference_aux_2 h0 h1 h2 a b ctr

#reset-options

opaque val gsubtraction_lemma_aux:
  h0:heap ->  h1:heap -> a:bigint{(Live h0 a) /\ (Live h1 a)} -> 
  b:bigint{Live h0 b} ->
  len:pos{len <= length a /\ len <= length b /\ len <= length a
	   /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } ->
  GLemma unit
    (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))) ) )
    (ensures (eval h0 b len - eval h0 a len = eval h1 a len)) []
let gsubtraction_lemma_aux h0 h1 a b len =
  admit();
  assert(eval h1 a len = pow2 (bitweight templ (len-1)) * v (get h1 a (len-1)) + eval h1 a (len-1));
  assert(v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))); 
  distributivity_sub_right (pow2 (bitweight templ (len-1))) (v (get h0 b (len-1)))  (v (get h0 a (len-1))); 
  assert(eval h1 a len = (pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)) - pow2 (bitweight templ (len-1)) * v (get h0 a (len-1))) + eval h1 a (len-1));
  FdifferenceLemmas.helper_lemma_2 
		(pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)))
		(pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)))
		(eval h0 b (len-1))
		(eval h0 a (len-1))

#reset-options

val subtraction_lemma_aux:
  h0:heap ->  h1:heap -> a:bigint{(Live h0 a) /\ (Live h1 a)} -> 
  b:bigint{Live h0 b} ->
  len:pos{len <= length a /\ len <= length b /\ len <= length a
	   /\ (forall (i:nat{ i < len }). v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))) ) )
    (ensures (eval h0 b len - eval h0 a len = eval h1 a len))
let subtraction_lemma_aux h0 h1 a b len =
  coerce
      (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))) ) )
      (ensures (eval h0 b len - eval h0 a len = eval h1 a len))
      (fun _ -> gsubtraction_lemma_aux h0 h1 a b len)

#reset-options

val subtraction_lemma:
  h0:heap -> h1:heap -> a:bigint{Live h0 a /\ Live h1 a} -> b:bigint{Live h0 b} ->
  len:nat{ (len <= length a) /\ (len <= length b) /\ (len <= length a)
	  /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures ( eval h0 b len - eval h0 a len = eval h1 a len ))
let rec subtraction_lemma h0 h1 a b len =
  admit();
  match len with
  | 0 -> ()
  | _ -> subtraction_lemma h0 h1 a b (len-1);
    subtraction_lemma_aux h0 h1 a b len

#reset-options

val subtraction_max_value_lemma:
  h0:heap -> h1:heap -> a:bigint{Live h0 a} -> b:bigint{Live h0 b /\ length a = length b} ->
  c:bigint{Live h1 c /\ length c = length a /\ (forall (i:nat). (i<length c) ==>
		v (get h1 c i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c (length c) <= maxValue h0 b (length b)))
let subtraction_max_value_lemma h0 h1 a b c = 
  admit();
  ()

#reset-options

val max_value_lemma: 
  h:heap -> a:bigint{Live h a} -> m:nat -> Lemma 
    (requires (forall (n:nat). n < length a ==> v (get h a n) <= m))
    (ensures (maxValue h a (length a) <= m))
let max_value_lemma h a m = 
  admit();
  ()

val subtraction_max_value_lemma_extended:
  h0:heap -> h1:heap -> a:bigint{Live h0 a /\ length a >= norm_length} -> b:bigint{Live h0 b} ->
  c:bigint{Live h1 c /\ length a = length c} -> Lemma
    (requires ((forall (i:nat). (i<norm_length) ==> 
		  v (get h1 c i) = v (get h0 b i) - v (get h0 a i))
	       /\ (forall (i:nat). (i < length c /\ i >= norm_length) ==>
		   v (get h1 c i) = v (get h0 a i))))
    (ensures (maxValue h1 c (length c) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b))))
let subtraction_max_value_lemma_extended h0 h1 a b c = 
  admit();
  cut ( forall (i:nat). (i < length c /\ i >= norm_length)
	==> (v (get h1 c i) = v (get h0 a i) /\ v (get h1 c i) <= maxValue h0 a (length a)));
  cut ( forall (i:nat). (i < length c /\ i >= norm_length)
  	==> v (get h1 c i) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b)));	
  assert ( forall (i:nat). (i < norm_length)
	==> v (get h1 c i) = v (get h0 b i) - v (get h0 a i));
  assert(forall (i:nat). (i < norm_length) ==> v (get h1 c i) = v (get h0 b i) - v (get h0 a i) ==> v (get h1 c i) <= v (get h0 b i) ==> v (get h1 c i) <= maxValue h0 b (length b)); 
  cut ( forall (i:nat). (i < norm_length)
	==> v (get h1 c i) <= maxValue h0 b (length b)); 
  cut ( forall (i:nat). (i < norm_length)
	==> (v (get h0 a i) <= maxValue h0 a (length a) /\ v (get h0 b i) <= maxValue h0 b (length b))); 
  cut ( forall (i:nat). (i < norm_length)
	==> v (get h1 c i) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b)))

#reset-options

opaque val gauxiliary_lemma_2: ha:heap -> a:bigint{Norm ha a} -> 
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{Filled hb b} -> i:nat{ i < norm_length} ->
  GLemma unit 
    (requires (True))
    (ensures ((v (get hb b i) - v (get ha a i)) >= 0 /\ (v (get hb b i) - v (get ha a i)) < pow2 max))
    []    
let gauxiliary_lemma_2 ha a min max hb b i =
  admit()
//  assert(True /\ bitsize (v (get hb b i)) max); 
//  Lemmas.pow2_increases_2 min (templ i); 
//  assert(bitsize (v (get ha a i)) (templ i)); 
//  assert(v (get ha a i) < pow2 (templ i)); 
//  cut(True /\ v (get ha a i) < pow2 min); 
//  assert(bitsize (v (get ha a i)) min); 
//  UInt.sub_lemma #max (v (get hb b i)) (v (get ha a i))

#reset-options

(*
val auxiliary_lemma_2: 
  ha:heap -> a:bigint{Norm ha a} -> hb:heap -> b:bigint{Filled hb b} -> i:nat{ i < norm_length} ->
  Lemma 
    (requires (True))
    (ensures (bitsize (v (get hb b i) - v (get ha a i)) max))    
    [SMTPat (bitsize (v (get hb b i) - v (get ha a i))  max)]
let auxiliary_lemma_2 ha a min max hb b i =
  coerce
    (requires (True))
    (ensures (bitsize (v (get hb b i) - v (get ha a i)) max))
    (fun _ -> gauxiliary_lemma_2 ha a min max hb b i)

#reset-options

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{Standardized ha a} -> 
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{Filled hb b min max} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> bitsize (v (get hb b i) - v (get ha a i)) max))
let auxiliary_lemma_0 ha a min max hb b = ()

#reset-options

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> mods:FStar.Set.set aref ->
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  b:bigint{Filled h0 b min max} -> 
  Lemma (requires (Live h1 b /\ Modifies mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (Filled h1 b min max))
let auxiliary_lemma_1 h0 h1 mods min max b = 
  admit();
  assert(FStar.Seq.Eq (sel h0 (getRef b)) (sel h1 (getRef b))); 
  ()
*)
#reset-options

val fdifference':
  a:bigint -> b:bigint{Disjoint a b} -> ST unit
    (requires (fun h -> Norm h a /\ Filled h b))
    (ensures (fun h0 u h1 -> 
      Norm h0 a /\ Filled h0 b /\ Filled h1 b /\ Live h1 a /\ Modifies (only a) h0 h1
      /\ eval h1 a norm_length = eval h0 b norm_length - eval h0 a norm_length
      /\ (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) ))
let fdifference' a b =
  admit();
  let h0 = ST.get() in
//  auxiliary_lemma_0 h0 a min max h0 b; 
  fdifference_aux a b 0; 
  let h1 = ST.get() in
//  auxiliary_lemma_1 h0 h1 ((only a)) min max b ; 
  subtraction_lemma h0 h1 a b norm_length


