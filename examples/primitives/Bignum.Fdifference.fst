module Bignum.Fdifference

open FStar.Heap
open FStar.Ghost
open IntLib
open SInt
open SBuffer
open SInt.UInt64
open Bignum.Parameters
open Bignum.Bigint

#set-options "--lax"

val helper_lemma_1:
  i:nat -> len:nat -> x:erased nat -> 
  Lemma (requires (i < len /\ len <= reveal x)) (ensures (i < reveal x))
let helper_lemma_1 i len v = ()  

val fdifference_aux_1:
  a:bigint -> b:bigint{disjoint a b} -> ctr:nat{ctr < norm_length} ->
  ST unit
    (requires (fun h -> 
      live h a /\ live h b
      /\ (forall (i:nat{ i >= ctr /\ i < norm_length}). {:pattern (v (get h b i))} 
	  v (get h b i) >= v (get h a i))))
    (ensures (fun h0 _ h1 -> 
      live h0 a /\ live h1 a /\ live h0 b /\ live h1 b /\ modifies_buf (only a) h0 h1
      /\ (forall (i:nat). (i >= ctr+1 /\ i < norm_length) ==>  
	  (v (get h1 b i) >= v (get h1 a i) /\ v (get h1 a i) = v (get h0 a i))
          /\ (((i<ctr \/ i>=norm_length) /\ i<length a) ==> v (get h1 a i) = v (get h0 a i)))
      /\ v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)))
let fdifference_aux_1 a b ctr =
  let h0 = ST.get() in
  let i = ctr in
  Bignum.FdifferenceLemmas.helper_lemma_3 i norm_length; 
  helper_lemma_1 i norm_length (elength a); 
  helper_lemma_1 i norm_length (elength b); 
  let ai = index a i in 
  let bi = index b i in 
  assert(i >= ctr /\ i < norm_length); 
  gcut(fun _ -> v (get h0 b i) >= v (get h0 a i)); 
  let z = bi ^- ai in 
  upd a i z;
  let h1 = ST.get() in
  eq_lemma h0 h1 b (only a)
  
val fdifference_aux_2_0: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies_buf (only a) h0 h1 /\ modifies_buf (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (modifies_buf (only a) h1 h2)
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
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (modifies_buf (only a) h0 h2)
      /\ (forall (i:nat). (i>= ctr /\ i<norm_length) ==> (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))
      ))     
let fdifference_aux_2_0 h0 h1 h2 a b ctr =
  eq_lemma h0 h1 b (only a);
  assert(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (get h2 a i) = v (get h1 b i) - v (get h1 a i)));  
  assert(forall (i:nat). (i>=ctr+1 /\ i < norm_length) ==> get h1 a i == get h0 a i); 
  cut(get h2 a ctr == get h1 a ctr); 
  cut(v (get h1 a ctr) = v (get h0 b ctr) - v (get h0 a ctr));
  cut(forall (i:nat). (i>= ctr+1 /\ i<norm_length) ==>
	  (v (get h2 a i) = v (get h0 b i) - v (get h0 a i))); 
  cut(v (get h2 a ctr) = v (get h0 b ctr) - v (get h0 a ctr)); 
  FdifferenceLemmas.helper_lemma_5 ctr norm_length;
  assert(forall (i:nat). (i>=ctr /\ i < norm_length) ==>
	   (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))

val fdifference_aux_2_1:
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma 
    (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies_buf (only a) h0 h1 /\ modifies_buf (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (modifies_buf (only a) h1 h2)
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
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (modifies_buf (only a) h0 h2)
      /\ (forall (i:nat). ((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i)) ))
let fdifference_aux_2_1 h0 h1 h2 a b ctr = 
  ()
  
val fdifference_aux_2: 
  h0:heap -> h1:heap -> h2:heap -> a:bigint -> b:bigint{disjoint a b} -> ctr:nat{ctr < norm_length} ->
  Lemma
    (requires (
      live h0 a /\ live h1 a /\ live h2 a /\ live h0 b /\ live h1 b /\ live h2 b
      /\ modifies_buf (only a) h0 h1 /\ modifies_buf (only a) h1 h2
      // Conditions from fdifference_aux
      /\ (modifies_buf (only a) h1 h2)
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
      (live h0 a) /\ (live h0 b) /\ (live h2 a) /\ (live h2 b)
      /\ (modifies_buf (only a) h0 h2)
      /\ (forall (i:nat).
	  ((i>= ctr /\ i<norm_length) ==> 
	    (v (get h2 a i) = v (get h0 b i) - v (get h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h2 a i == get h0 a i)))
      ))      
let fdifference_aux_2 h0 h1 h2 a b ctr =
  fdifference_aux_2_0 h0 h1 h2 a b ctr;
  fdifference_aux_2_1 h0 h1 h2 a b ctr

val fdifference_aux:
  a:bigint -> b:bigint{disjoint a b} -> 
  ctr:nat{ ctr <= norm_length } ->
  ST unit
    (requires (fun h ->
      (live h a) /\ (live h b)
      /\ (forall (i:nat). (i >= ctr /\ i < norm_length) ==> (v (get h b i) >= v (get h a i)))
    ))
    (ensures (fun h0 _ h1 -> 
      (live h0 a) /\ (live h0 b) /\ (live h1 a) /\ (live h1 b)
      /\ (modifies_buf (only a) h0 h1)
      /\ (forall (i:nat). 
	  ((i>= ctr /\ i<norm_length) ==>  
	    (v (get h1 a i) = v (get h0 b i) - v (get h0 a i)))
	  /\ (((i<ctr \/ i >= norm_length) /\ i<length a) ==> (get h1 a i == get h0 a i)))
    ))
let rec fdifference_aux a b ctr =
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

abstract val gsubtraction_lemma_aux:
  h0:heap ->  h1:heap -> a:bigint{(live h0 a) /\ (live h1 a)} -> 
  b:bigint{live h0 b} ->
  len:pos{len <= length a /\ len <= length b /\ len <= length a
	   /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires ( (eval h0 b (len-1) - eval h0 a (len-1) = eval h1 a (len-1))
		/\ (v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))) ) )
    (ensures (eval h0 b len - eval h0 a len = eval h1 a len))
let subtraction_lemma_aux h0 h1 a b len =
  assert(eval h1 a len = pow2 (bitweight templ (len-1)) * v (get h1 a (len-1)) + eval h1 a (len-1));
  assert(v (get h1 a (len-1)) = v (get h0 b (len-1)) - v (get h0 a (len-1))); 
  distributivity_sub_right (pow2 (bitweight templ (len-1))) (v (get h0 b (len-1)))  (v (get h0 a (len-1))); 
  assert(eval h1 a len = (pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)) - pow2 (bitweight templ (len-1)) * v (get h0 a (len-1))) + eval h1 a (len-1));
  FdifferenceLemmas.helper_lemma_2 
		(pow2 (bitweight templ (len-1)) * v (get h0 b (len-1)))
		(pow2 (bitweight templ (len-1)) * v (get h0 a (len-1)))
		(eval h0 b (len-1))
		(eval h0 a (len-1))

val subtraction_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a /\ live h1 a} -> b:bigint{live h0 b} ->
  len:nat{ (len <= length a) /\ (len <= length b) /\ (len <= length a)
	  /\ (forall (i:nat). i < len ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures ( eval h0 b len - eval h0 a len = eval h1 a len ))
let rec subtraction_lemma h0 h1 a b len =
  match len with
  | 0 -> ()
  | _ -> subtraction_lemma h0 h1 a b (len-1);
    subtraction_lemma_aux h0 h1 a b len

val subtraction_max_value_lemma:
  h0:heap -> h1:heap -> a:bigint{live h0 a} -> b:bigint{live h0 b /\ length a = length b} ->
  c:bigint{live h1 c /\ length c = length a /\ (forall (i:nat). (i<length c) ==>
		v (get h1 c i) = v (get h0 b i) - v (get h0 a i)) } ->
  Lemma
    (requires (True))
    (ensures (maxValue h1 c (length c) <= maxValue h0 b (length b)))
let subtraction_max_value_lemma h0 h1 a b c = 
  ()

val max_value_lemma: 
  h:heap -> a:bigint{live h a} -> m:nat -> Lemma 
    (requires (forall (n:nat). n < length a ==> v (get h a n) <= m))
    (ensures (maxValue h a (length a) <= m))
let max_value_lemma h a m = 
  ()

val subtraction_max_value_lemma_extended:
  h0:heap -> h1:heap -> a:bigint{live h0 a /\ length a >= norm_length} -> b:bigint{live h0 b} ->
  c:bigint{live h1 c /\ length a = length c} -> Lemma
    (requires ((forall (i:nat). (i<norm_length) ==> 
		  v (get h1 c i) = v (get h0 b i) - v (get h0 a i))
	       /\ (forall (i:nat). (i < length c /\ i >= norm_length) ==>
		   v (get h1 c i) = v (get h0 a i))))
    (ensures (maxValue h1 c (length c) <= max (maxValue h0 a (length a)) (maxValue h0 b (length b))))
let subtraction_max_value_lemma_extended h0 h1 a b c = 
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

val auxiliary_lemma_2: ha:heap -> a:bigint{norm ha a} -> 
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{filled hb b} -> i:nat{ i < norm_length} ->
  Lemma 
    (requires (True))
    (ensures ((v (get hb b i) - v (get ha a i)) >= 0 /\ (v (get hb b i) - v (get ha a i)) < pow2 max))
let auxiliary_lemma_2 ha a min max hb b i =
  (* assert(True /\ bitsize (v (get hb b i)) max);  *)
  (* Lemmas.pow2_increases_2 min (templ i);  *)
  (* assert(bitsize (v (get ha a i)) (templ i));  *)
  assert(v (get ha a i) < pow2 (templ i)); 
  cut(True /\ v (get ha a i) < pow2 min);
  (* assert(bitsize (v (get ha a i)) min);  *)
  (* UInt.sub_lemma #max (v (get hb b i)) (v (get ha a i)) *)
  ()

(*
val auxiliary_lemma_2: 
  ha:heap -> a:bigint{norm ha a} -> hb:heap -> b:bigint{filled hb b} -> i:nat{ i < norm_length} ->
  Lemma 
    (requires (True))
    (ensures (bitsize (v (get hb b i) - v (get ha a i)) max))    
    [SMTPat (bitsize (v (get hb b i) - v (get ha a i))  max)]
let auxiliary_lemma_2 ha a min max hb b i =
  coerce
    (requires (True))
    (ensures (bitsize (v (get hb b i) - v (get ha a i)) max))
    (fun _ -> gauxiliary_lemma_2 ha a min max hb b i)

val auxiliary_lemma_0: 
  ha:heap -> a:bigint{Standardized ha a} -> 
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  hb:heap -> b:bigint{filled hb b min max} ->
  Lemma (requires (True))
	(ensures (forall (i:nat). 
	  i < norm_length ==> bitsize (v (get hb b i) - v (get ha a i)) max))
let auxiliary_lemma_0 ha a min max hb b = ()

val auxiliary_lemma_1:
  h0:heap -> h1:heap -> mods:FStar.Set.set aref ->
  min:pos{(forall (i:nat). templ i <= min)} -> max:pos{max <= platform_size} ->
  b:bigint{filled h0 b min max} -> 
  Lemma (requires (live h1 b /\ modifies_buf mods h0 h1 /\ not(FStar.Set.mem (Ref (getRef b)) mods)))
	(ensures (filled h1 b min max))
let auxiliary_lemma_1 h0 h1 mods min max b = 
  admit();
  assert(FStar.Seq.Eq (sel h0 (getRef b)) (sel h1 (getRef b))); 
  ()
*)

val fdifference':
  a:bigint -> b:bigint{disjoint a b} -> ST unit
    (requires (fun h -> norm h a /\ filled h b))
    (ensures (fun h0 u h1 -> 
      norm h0 a /\ filled h0 b /\ filled h1 b /\ live h1 a /\ modifies_buf (only a) h0 h1
      /\ eval h1 a norm_length = eval h0 b norm_length - eval h0 a norm_length
      /\ (forall (i:nat). i < norm_length ==> v (get h1 a i) = v (get h0 b i) - v (get h0 a i)) ))
let fdifference' a b =
  let h0 = ST.get() in
//  auxiliary_lemma_0 h0 a min max h0 b; 
  fdifference_aux a b 0; 
  let h1 = ST.get() in
//  auxiliary_lemma_1 h0 h1 ((only a)) min max b ; 
  subtraction_lemma h0 h1 a b norm_length


