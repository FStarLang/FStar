module Bignum.Modulo

open FStar.Heap
open FStar.Ghost
open IntLib
open SInt
open SBuffer
open SInt.UInt64
open Bignum.Parameters
open Bignum.Bigint

#set-options "--lax"

(** TODO: proof **)
val finalize: b:bigint -> ST unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ norm h1 b
    /\ eval h1 b norm_length = eval h0 b norm_length % reveal prime))
let finalize b =
  admit();
  let mask_51 = (one ^<< 51) ^- one in
  let mask2_51m19 = mask_51 ^- (one ^<< 4) ^- (one ^<< 1) ^- one in
  let b0 = index b 0 in
  let b1 = index b 1 in
  let b2 = index b 2 in
  let b3 = index b 3 in
  let b4 = index b 4 in
  let mask = eq b4 mask_51 in
  let mask = eq b3 mask_51 ^& mask in 
  let mask = eq b2 mask_51 ^& mask in 
  let mask = eq b1 mask_51 ^& mask in 
  let mask = gte b0 mask2_51m19 ^& mask in 
  upd b 0 (b0 ^- (mask ^& mask2_51m19));
  upd b 1 (b1 ^& mask);
  upd b 2 (b2 ^& mask);
  upd b 3 (b3 ^& mask);
  upd b 4 (b4 ^& mask);
  ()

// Specific to 25519
assume val prime_modulo_lemma: unit -> Lemma (pow2 255 % (reveal prime) = 19)

assume val modulo_lemma: a:nat -> b:pos -> Lemma (requires (a < b)) (ensures (a % b = a)) 
  [SMTPat (a % b)]

let satisfiesModuloConstraints (h:heap) (#size:pos) (b:buffer size) = 
  live h b /\ length b >= 2*norm_length-1 /\ maxValue h b (2*norm_length-1) * 6 < pow2 (platform_size-1)

val times_19_wide: x:wide{19 * v x < pow2 platform_wide} -> Tot (y:wide{v y = 19 * v x})
let times_19_wide x = 
  admit();
  (x ^^<< 4) ^^+ (x ^^<< 1) ^^+ x

val times_19: x:limb{19 * v x < pow2 platform_size} -> Tot (y:limb{v y = 19 * v x})
let times_19 x = 
  admit();
  (x ^<< 4) ^+ (x ^<< 1) ^+ x
  
abstract let reducible (h:heap) (#size:pos) (b:buffer size) (ctr:nat{ctr < norm_length-1}) =
  live h b /\ length b >= 2*norm_length-1 
  /\ (forall (i:nat). {:pattern (get h b (i+norm_length))}
      i <= ctr ==> v (get h b i) + 19 * v (get h b (i+norm_length)) < pow2 platform_size)

abstract let times19 (h0:heap) (h1:heap) (#size:pos) (b:buffer size) (ctr:nat{ctr < norm_length - 1}) =
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)}
       i <= ctr ==> v (get h1 b i) = v (get h0 b i) + 19 * (v (get h0 b (i+norm_length))))

abstract let untouched (h0:heap) (h1:heap) (#size:pos) (b:buffer size) (ctr:nat) = 
  live h0 b /\ live h1 b /\ length b >= 2*norm_length-1
  /\ (forall (i:nat). {:pattern (get h1 b i)} (i > ctr /\ i < 2*norm_length-1) ==>  
      v (get h0 b i) = v (get h1 b i))

val pow2_bitweight_lemma_1: ctr:pos -> 
  Lemma (requires (True))
	(ensures (pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (bitweight templ (ctr-1)) * pow2 (bitweight templ norm_length)))
let rec pow2_bitweight_lemma_1 ctr =
  match ctr with
  | 1 -> ()
  | _ -> 
    cut(ctr-1+norm_length = ctr+norm_length-1 /\ ctr+norm_length-1 = (ctr-1) + norm_length
	/\ (ctr+norm_length-1)-1=ctr+norm_length-2); 
    pow2_bitweight_lemma_1 (ctr-1); 
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-2)) = pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    cut (True /\ bitweight templ (ctr+norm_length-1) = bitweight templ (ctr+norm_length-2) + 51); 
    IntLibLemmas.pow2_exp (bitweight templ (ctr+norm_length-2)) 51; 
    cut(True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * pow2 (bitweight templ (ctr+norm_length-2))); 
    cut(True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * (pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)));  
    paren_mul_right (pow2 51) (pow2 (bitweight templ (ctr-2))) (pow2 (bitweight templ norm_length));
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 51 * pow2 (bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)); 
    IntLibLemmas.pow2_exp 51 (bitweight templ (ctr-2));
    cut (True /\ pow2 (bitweight templ (ctr+norm_length-1)) = pow2 (51 + bitweight templ (ctr-2)) * pow2 (bitweight templ norm_length)) 

val bitweight_norm_length_lemma: unit -> Lemma 
  (requires (True)) 
  (ensures (bitweight templ norm_length = 255))
let bitweight_norm_length_lemma () = 
  ()

(* TODO *)
assume val helper_lemma_5: a:nat -> b:nat -> c:nat -> p:pos -> 
  Lemma (requires (True))
	(ensures ( (a*b+c) % p = ((a % p) * b + c)%p))

val lemma_aux_0: a:int -> b:int -> c:int -> d:int -> Lemma (a * b + c - (a * (b + 19 * d) + c) = - 19 * a * d)
let lemma_aux_0 a b c d = ()

val freduce_degree_lemma_2: h0:heap -> h1:heap -> #size:pos -> b:buffer size{live h1 b /\ live h0 b /\ length b >= 2 * norm_length - 1} -> ctr:pos{ctr < norm_length-1} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
	/\ v (get h1 b ctr) = v (get h0 b ctr) + 5 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime)))
let freduce_degree_lemma_2 h0 h1 #size b ctr =
  let prime = reveal prime in 
  cut (ctr+norm_length = norm_length+ctr /\ (norm_length+1+ctr)-1 = norm_length + ctr /\ norm_length+ctr = (ctr+1)+norm_length-1); 
  cut (True /\ eval h0 b (norm_length+1+ctr) = pow2 (bitweight templ (norm_length+ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (ctr+norm_length)); 
  pow2_bitweight_lemma_1 (ctr+1); 
  cut(True /\ pow2 (bitweight templ (norm_length+ctr)) = pow2 130 * pow2 (bitweight templ ctr)); 
  paren_mul_left (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  paren_mul_right (pow2 130) (pow2 (bitweight templ ctr)) (v (get h0 b (norm_length+ctr))); 
  cut (True /\ eval h0 b (norm_length+1+ctr) = (pow2 130 * pow2 (bitweight templ ctr)) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)); 
  helper_lemma_5 (pow2 130) (pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) (eval h0 b (norm_length+ctr)) prime; 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = ((pow2 130 % prime) * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  prime_modulo_lemma (); 
  cut (True /\ eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h0 b (norm_length+ctr)) % prime); 
  eval_eq_lemma h0 h1 b b ctr; 
  cut (True /\ eval h0 b (ctr+1) = pow2 (bitweight templ ctr) * v (get h0 b ctr) + eval h0 b ctr); 
  cut (True /\ eval h1 b (ctr+1) = pow2 (bitweight templ ctr) * (v (get h0 b ctr) + 5 * v (get h0 b (norm_length+ctr))) + eval h0 b ctr); 
  lemma_aux_0 (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (eval h0 b ctr) (v (get h0 b (norm_length+ctr)));
  cut (eval h0 b (ctr+1) - eval h1 b (ctr+1) = - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) /\ True); 
  distributivity_add_right (pow2 (bitweight templ ctr)) (v (get h0 b ctr)) (5 * v (get h0 b (norm_length+ctr))); 
  eval_partial_eq_lemma h0 h1 b b (ctr+1) (norm_length+ctr); 
  cut (eval h0 b (norm_length+ctr) - eval h0 b (ctr+1) = eval h1 b (norm_length+ctr) - eval h1 b (ctr+1) /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) + eval h0 b (ctr+1) - eval h1 b (ctr+1)) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr)) + eval h1 b (norm_length+ctr) - 5 * pow2 (bitweight templ ctr) * v (get h0 b (norm_length+ctr))) % prime /\ True); 
  cut ( eval h0 b (norm_length+1+ctr) % prime = (eval h1 b (norm_length+ctr) ) % prime /\ True)

val freduce_degree_lemma:
  h0:heap -> h1:heap -> #size:pos -> b:buffer size{live h1 b /\ live h0 b /\ length b >= 2 * norm_length - 1} -> ctr:nat{ctr < norm_length-1} -> Lemma
    (requires ((forall (i:nat). {:pattern (v (get h1 b i))}
	(i < length b /\ i <> ctr) ==> v (get h1 b i) = v (get h0 b i)) 
      /\ v (get h1 b ctr) = v (get h0 b ctr) + 19 * v (get h0 b (ctr+norm_length)) ))
    (ensures (eval h0 b (norm_length+1+ctr) % (reveal prime) = eval h1 b (norm_length+ctr) % (reveal prime))) 
let freduce_degree_lemma h0 h1 #size b ctr =
  let prime = reveal prime in
  if ctr = 0 then (
    helper_lemma_5 (pow2 130) (v (get h0 b norm_length)) (eval h0 b norm_length) prime;
    prime_modulo_lemma ();
    cut(eval h0 b 1 = v (get h0 b 0) /\ eval h1 b 1 = v (get h0 b 0) + 5 * v (get h0 b norm_length)); 
    eval_partial_eq_lemma h0 h1 b b 1 norm_length;
    cut(True /\ eval h1 b norm_length - eval h1 b 1 = eval h0 b norm_length - eval h0 b 1)
  ) else (
    freduce_degree_lemma_2 h0 h1 b ctr
  )

val freduce_degree': 
  b:bigint_wide -> ctr:nat{ctr < norm_length - 1} -> ST unit 
    (requires (fun h -> reducible h b ctr)) 
    (ensures (fun h0 _ h1 -> untouched h0 h1 b ctr /\ times19 h0 h1 b ctr
      /\ eval h1 b (norm_length) % reveal prime = eval h0 b (norm_length+1+ctr) % reveal prime
      /\ modifies_buf (only b) h0 h1))
let rec freduce_degree' b ctr' =
  let h0 = ST.get() in
  match ctr' with
  | 0 -> 
    let b5ctr = index b (0+norm_length) in 
    let bctr = index b 0 in
    let b5ctr = times_19_wide b5ctr in
    let bctr = bctr ^^+ b5ctr in 
    upd b 0 bctr;
    let h1 = ST.get() in
    freduce_degree_lemma h0 h1 b 0;
    cut (eval h0 b (norm_length+1+0) % reveal prime = eval h1 b (norm_length+0) % reveal prime);
    cut (eval h0 b (norm_length+1) % reveal prime = eval h1 b (norm_length+0) % reveal prime)
  | _ -> 
    let ctr = ctr' in
    let b5ctr = index b (ctr + norm_length) in 
    let bctr = index b ctr in
    let b5ctr = times_19_wide b5ctr in
    let bctr = bctr ^^+ b5ctr in 
    upd b ctr bctr;
    let h1 = ST.get() in
    freduce_degree_lemma h0 h1 b ctr; 
    cut (eval h0 b (norm_length+1+ctr) % reveal prime = eval h1 b (norm_length+ctr) % reveal prime);
    cut(reducible h1 b (ctr-1)); 
    freduce_degree' b (ctr-1); 
    let h2 = ST.get() in 
    cut (forall (i:nat). {:pattern (v (get h1 b i))} (i > ctr /\ i < 2*norm_length-1) ==>
	   v (get h1 b i) = v (get h0 b i)); 
    cut(untouched h0 h2 b ctr);
    cut (times19 h0 h2 b ctr) ;
    ()

// TODO
assume NormLength: norm_length = 5

val aux_lemma_4': h:heap -> b:bigint_wide -> Lemma
  (requires (satisfiesModuloConstraints h b))
  (ensures (reducible h b (norm_length-2)))
let aux_lemma_4' h b =
  maxValue_lemma_aux h b (2*norm_length-1);
  IntLibLemmas.pow2_increases 64 62

val aux_lemma_5': h0:heap -> h1:heap -> b:bigint_wide -> Lemma
  (requires (live h0 b /\ satisfiesModuloConstraints h0 b /\ times19 h0 h1 b (norm_length-2)
      /\ untouched h0 h1 b (norm_length-2)))
  (ensures (live h0 b /\ satisfiesModuloConstraints h0 b /\ times19 h0 h1 b (norm_length-2)
    /\ (forall (i:nat). i <= norm_length ==> v (get h1 b i) < pow2 62)))
let aux_lemma_5' h0 h1 b = 
  maxValue_lemma_aux h0 b (2*norm_length-1)

val freduce_degree: b:bigint_wide -> ST unit 
  (requires (fun h -> live h b /\ satisfiesModuloConstraints h b)) 
  (ensures (fun h0 _ h1 -> live h0 b /\ live h1 b /\ satisfiesModuloConstraints h0 b
    /\ modifies_buf (only b) h0 h1
    /\ (forall (i:nat). {:pattern (v (get h1 b i))} i <= norm_length ==> 
	v (get h1 b i) < pow2 platform_size)
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime))
let freduce_degree b = 
  let h0 = ST.get() in
  aux_lemma_4' h0 b; 
  freduce_degree' b (norm_length-2); 
  let h1 = ST.get() in
  aux_lemma_5' h0 h1 b

val pow2_bitweight_lemma: ctr:nat -> Lemma 
    (requires (True)) 
    (ensures (pow2 (bitweight templ (ctr+1)) = pow2 (bitweight templ ctr) * pow2 (templ ctr))) 
let pow2_bitweight_lemma ctr =
  IntLibLemmas.pow2_exp (bitweight templ ctr) (templ ctr)

val helper_lemma_2: pb:nat -> pc:pos -> a0:nat -> b:nat ->
  Lemma  (ensures ((pb*pc) * a0/pc + (pb * (a0 % pc) + b) = pb * a0 + b))
let helper_lemma_2 pb pc a0 b = ()

val eval_carry_lemma: ha:heap -> a:bigint_wide{live ha a /\ length a >= norm_length+1} -> 
  hb:heap -> b:bigint_wide{live hb b /\ length b >= norm_length+1} -> ctr:nat{ctr < norm_length} -> Lemma
    (requires (v (get hb b ctr) = v (get ha a ctr) % pow2 (templ ctr)
      /\ v (get hb b (ctr+1)) = v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)
      /\ (forall (i:nat). {:pattern (v (get hb b i))}
	  (i < norm_length+1 /\ i <> ctr /\ i <> ctr+1) ==> v (get hb b i) = v (get ha a i)) ))
    (ensures (eval hb b (norm_length+1) = eval ha a (norm_length+1)))
let eval_carry_lemma ha a hb b ctr =
  eval_eq_lemma ha hb a b ctr;
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + eval hb b (ctr+1)); 
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * v (get hb b (ctr+1)) + (pow2 (bitweight templ ctr) * v (get hb b ctr) + eval hb b ctr));  
  cut(True /\ eval hb b (ctr+2) = pow2 (bitweight templ (ctr+1)) * (v (get ha a (ctr+1)) + v (get ha a ctr) / pow2 (templ ctr)) + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr)); 
  distributivity_add_right (pow2 (bitweight templ (ctr+1))) (v (get ha a (ctr+1))) (v (get ha a ctr) / pow2 (templ ctr));
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1))
	      + pow2 (bitweight templ (ctr+1)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  pow2_bitweight_lemma ctr; 
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * pow2 (templ ctr)) * v (get ha a ctr) / pow2 (templ ctr) 
	      + (pow2 (bitweight templ ctr) * (v (get ha a ctr) % pow2 (templ ctr)) + eval hb b ctr));
  helper_lemma_2 (pow2 (bitweight templ ctr)) (pow2 (templ ctr)) (v (get ha a ctr)) (eval hb b ctr); 
  cut(True /\ eval hb b (ctr+2) = 
	      pow2 (bitweight templ (ctr+1)) * v (get ha a (ctr+1)) 
	      + (pow2 (bitweight templ ctr) * v (get ha a ctr) + eval hb b ctr));  
  cut(True /\ eval hb b (ctr+2) = eval ha a (ctr+2)); 
  eval_partial_eq_lemma ha hb a b (ctr+2) (norm_length+1)

val helper_lemma_4: a:nat -> b:nat -> c:pos -> size:pos{size > c} ->
  Lemma (requires (a < pow2 (size-1) /\ b < pow2 (size-c)))
	(ensures (a + b < pow2 size))
let helper_lemma_4 a b c size = 
  if size-1 > size - c then IntLibLemmas.pow2_increases (size-1) (size-c) else ()

assume Platform_size: platform_size = 64

val auxiliary_lemma_1': bip1:limb -> c:limb -> Lemma
    (requires (v bip1 < pow2 63 /\ v c < pow2 (platform_size - 51)))
    (ensures (v bip1 + v c < pow2 platform_size))
let auxiliary_lemma_1' bip1 c =
  helper_lemma_4 (v bip1) (v c) 51 64

val mod2_51_wide: a:wide -> Tot (b:wide{v b = v a % pow2 51})
let mod2_51_wide a = 
  let mask = one_wide ^^<< 51 in
  cut (v mask = pow2 51 % pow2 64 /\ pow2 51 >= 1); 
  IntLibLemmas.pow2_increases 64 51; 
  let mask = mask ^^- one_wide in
  let res = a ^^& mask in
  SInt.ulogand_lemma_4 #64 a 51 mask;
  res

val mod2_51: a:limb -> Tot (b:limb{v b = v a % pow2 51})
let mod2_51 a = 
  let mask = shift_left one 51 in
  cut (v mask = pow2 51 % pow2 64 /\ pow2 51 >= 1); 
  IntLibLemmas.pow2_increases 64 51; 
  let mask = mask ^- one in
  let res = a ^& mask in
  SInt.ulogand_lemma_4 #64 a 51 mask;
  res

abstract let carriable (h:heap) (#size:pos) (b:buffer size) (ctr:nat{ctr <= norm_length}) =
  live h b /\ length b >= norm_length + 1  
  /\ (forall (i:nat). {:pattern (v (get h b i))}
      (i > ctr /\ i <= norm_length) ==> v (get h b i) < pow2 (platform_size - 1))

abstract let carried (h1:heap) (#size:pos) (b:buffer size) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} i < ctr ==> v (get h1 b i) < pow2 (templ ctr))
  /\ (ctr <> norm_length ==> v (get h1 b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h1 b norm_length) < pow2 (platform_wide - 51))
  
abstract let carried' (h1:heap) (#size:pos) (b:buffer size) (ctr:nat{ctr <= norm_length}) =
  live h1 b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i >= ctr /\ i < norm_length) ==> v (get h1 b i) < pow2 (templ ctr))
  /\ v (get h1 b norm_length) < pow2 (platform_wide - 51)
  
abstract let untouched_2 (h0:heap) (h1:heap) (#size:pos) (b:buffer size) (ctr:nat) =
  live h0 b /\ live h1 b /\ length b >= norm_length+1 
  /\ (forall (i:nat). {:pattern (get h1 b i)}
      ((i < ctr \/ i >= norm_length+1) /\ i < length b) ==> v (get h0 b i) = v (get h1 b i))

val carry: b:bigint_wide -> ctr:nat{ctr <= norm_length} -> ST unit
    (requires (fun h -> carriable h b ctr /\ carried h b ctr))
    (ensures (fun h0 _ h1 -> carried h1 b norm_length /\ untouched_2 h0 h1 b ctr
      /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
      /\ modifies_buf (only b) h0 h1 ))
let rec carry b i =
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in
    let ri = mod2_51_wide bi in
    cut(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^^>> 51) in
    cut (v bi < pow2 64 /\ v c = IntLib.div (v bi) (pow2 51)); 
    IntLibLemmas.pow2_div 64 51;
    (* TODO *)
    assume (v c < pow2 (64 - 51)); 
    let bip1 = index b (i+1) in
    cut(v bip1 = v (get h1 b (i+1))); 
    cut(v bip1 < pow2 (64 - 1)); 
//    auxiliary_lemma_1' bip1 c; 
    let z = bip1 ^^+ c in
    upd b (i+1) z;
    let h2 = ST.get() in
    eval_carry_lemma h0 b h2 b i; 
    carry b (i+1)

val carry_top_to_0: b:bigint_wide -> ST unit
    (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1
      /\ v (get h b 0) + 5 * v (get h b norm_length) < pow2 62))
    (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carried' h1 b 1
      /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime)
      /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (get h1 b i) = v (get h0 b i))
      /\ modifies_buf (only b) h0 h1))
let carry_top_to_0 b =
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  let btop_5 = times_19_wide btop in  
    upd b 0 (b0 ^^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0

abstract let carriable2 (h:heap) (#size:pos) (b:buffer size) (ctr:pos{ctr<=norm_length}) =
  live h b /\ length b >= norm_length + 1
  /\ (forall (i:nat). {:pattern (v (get h b i))} i < ctr ==> v (get h b i) < pow2 51)
  /\ (forall (i:nat). {:pattern (v (get h b i))} (i > ctr /\ i < norm_length) ==> v (get h b i) < pow2 51)
  /\ (ctr < norm_length ==> v (get h b norm_length) = 0)
  /\ (ctr = norm_length ==> v (get h b norm_length) < 2)
  /\ v (get h b ctr) < pow2 51 + pow2 15
  /\ (v (get h b ctr) >= pow2 51 ==> (
      forall (i:nat). {:pattern (v (get h b i))} ( i < ctr /\ i > 0) ==> v (get h b i) < pow2 15))
  /\ ((ctr = norm_length /\ v (get h b norm_length) = 1) ==> 
      (forall (i:nat). {:pattern (v (get h b i))} (i > 0 /\ i < norm_length) ==> v (get h b i) < pow2 15))

val lemma_aux: a:nat -> b:pos -> Lemma (IntLib.div a b > 0 ==> a >= b)
let lemma_aux a b = 
  ()

(* TODO *)
assume val lemma_aux_2: a:limb -> Lemma ((v a < pow2 51+pow2 15 /\ v a >= pow2 51) ==> v a % pow2 51 < pow2 15)

val carry2_aux: b:bigint_wide -> ctr:pos{ctr <= norm_length} -> ST unit
  (requires (fun h -> carriable2 h b ctr))
  (ensures (fun h0 _ h1 -> carriable2 h0 b ctr /\ carriable2 h1 b norm_length
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ modifies_buf (only b) h0 h1 ))
let rec carry2_aux b i = 
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in 
    let ri = mod2_51_wide bi in
//    lemma_aux_2 bi;
    cut(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^^>> 51) in
    // In the spec of >>, TODO
    assume(v c < 2); 
    let bip1 = index b (i+1) in
//    auxiliary_lemma_2 bip1 c; 
    IntLibLemmas.pow2_increases 64 27;
    IntLibLemmas.pow2_doubles 51;
    IntLibLemmas.pow2_increases 51 15;
    let z = bip1 ^^+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51); 
    cut (v z >= pow2 51 ==> v c = 1); 
    cut (v c > 0 ==> IntLib.div (v (get h0 b i)) (pow2 51) > 0 ==> v (get h0 b i) >= pow2 51); 
    cut (v z >= pow2 51 ==> v (get h1 b i) < pow2 15); 
    upd b (i+1) z;
    let h2 = ST.get() in 
    cut (v z >= pow2 51 ==> v c = 1 /\ True); 
    eval_carry_lemma h0 b h2 b i; 
    carry2_aux b (i+1)

val pow2_3_lemma: unit -> Lemma (pow2 3 = 8)
let pow2_3_lemma () = 
  ()

val carry2: b:bigint_wide -> ST unit
  (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carriable2 h1 b norm_length 
    /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_buf (only b) h0 h1))
let rec carry2 b = 
  let h0 = ST.get() in
  pow2_3_lemma ();
  IntLibLemmas.pow2_exp 3 37;
  IntLibLemmas.pow2_increases 40 37;
  IntLibLemmas.pow2_increases 40 51;
  IntLibLemmas.pow2_doubles 40;
  IntLibLemmas.pow2_increases 62 41;
  carry_top_to_0 b;
  let h1 = ST.get() in
  upd b norm_length zero_wide;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b (norm_length)); 
  let bi = index b 0 in 
  let ri = mod2_51_wide bi in
  cut(v ri < pow2 51); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^^>> 51) in
  cut (v bi < pow2 41); 
  // In the spec of >>, TODO
  assume(v c < pow2 15); 
  let bip1 = index b 1 in 
//  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 64 27;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 51 15; 
  let z = bip1 ^^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut(carriable2 h4 b 1);
  carry2_aux b 1

val last_carry: b:bigint_wide -> ST unit
  (requires (fun h -> carriable2 h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carriable2 h0 b norm_length /\ norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_buf (only b) h0 h1))
let last_carry b =
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  cut (v b0 < pow2 51 /\ v btop < 2); 
  pow2_3_lemma ();
  cut (5 * v btop < pow2 3 /\ True); 
  IntLibLemmas.pow2_increases 51 3;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 64 27;
  cut(v b0 + 5 * v btop < pow2 27 /\ True); 
  let btop_5 = times_19_wide btop in  
  upd b 0 (b0 ^^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0;
  upd b norm_length zero_wide;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length);
  let bi = index b 0 in 
  let ri = mod2_51_wide bi in
  cut(v ri < pow2 51); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^^>> 51) in
  cut (v bi < pow2 51 + 5); 
  cut (v bi >= pow2 51 ==> v (get h3 b 1) < pow2 15); 
  // In the spec of >>, TODO
  assume(v bi >= pow2 51 ==> v c = 1); 
  let bip1 = index b 1 in 
//  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 64 27;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 51 15; 
  let z = bip1 ^^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
  eval_carry_lemma h2 b h4 b 0; 
  cut (v (get h4 b 1) < pow2 51); 
  cut (norm h4 b)

val copy_to_bigint: dest:bigint -> src:bigint_wide -> len:nat -> St unit
let rec copy_to_bigint dest src len = 
  match len with
  | 0 -> ()
  | _ -> 
    upd dest (len-1) (SInt.Cast.uint128_to_uint64 (index src (len-1)));
    copy_to_bigint dest src (len-1)

val modulo: res:bigint -> b:bigint_wide -> ST unit
  (requires (fun h -> live h b /\ satisfiesModuloConstraints h b))
  (ensures (fun h0 _ h1 -> live h0 b /\ satisfiesModuloConstraints h0 b /\ norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (2*norm_length-1) % reveal prime 
    /\ modifies_buf (only b) h0 h1))
let modulo res b =
  let h0 = ST.get() in
  freduce_degree b; 
  let h1 = ST.get() in
  upd b norm_length zero_wide;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length);
  carry b 0; 
  let h3 = ST.get() in
  carry2 b; 
  let h4 = ST.get() in
  last_carry b;
  copy_to_bigint res b norm_length

(* TODO completely *)
val carry_limb: b:bigint -> ctr:nat{ctr <= norm_length} -> ST unit
    (requires (fun h -> carriable h b ctr /\ carried h b ctr))
    (ensures (fun h0 _ h1 -> carried h1 b norm_length /\ untouched_2 h0 h1 b ctr
      /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
      /\ modifies_buf (only b) h0 h1 ))
let rec carry_limb b i =
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in
    let ri = mod2_51 bi in
    cut(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^>> 51) in
    cut (v bi < pow2 64 /\ v c = IntLib.div (v bi) (pow2 51)); 
    IntLibLemmas.pow2_div 64 51;
    (* TODO *)
    assume (v c < pow2 (64 - 51)); 
    let bip1 = index b (i+1) in
    cut(v bip1 = v (get h1 b (i+1))); 
    cut(v bip1 < pow2 (64 - 1)); 
    auxiliary_lemma_1' bip1 c; 
    let z = bip1 ^+ c in
    upd b (i+1) z;
    let h2 = ST.get() in
//    eval_carry_lemma h0 b h2 b i; 
    carry_limb b (i+1)


val carry2_aux_limb: b:bigint -> ctr:pos{ctr <= norm_length} -> ST unit
  (requires (fun h -> carriable2 h b ctr))
  (ensures (fun h0 _ h1 -> carriable2 h0 b ctr /\ carriable2 h1 b norm_length
    /\ eval h1 b (norm_length+1) = eval h0 b (norm_length+1)
    /\ modifies_buf (only b) h0 h1 ))
let rec carry2_aux_limb b i = 
  let h0 = ST.get() in
  match norm_length - i with
  | 0 -> ()
  | _ -> 
    let bi = index b i in 
    let ri = mod2_51 bi in
    lemma_aux_2 bi;
    cut(v ri < pow2 (templ i)); 
    upd b i ri; 
    let h1 = ST.get() in
    let c = (bi ^>> 51) in
    // In the spec of >>, TODO
    assume(v c < 2); 
    let bip1 = index b (i+1) in
//    auxiliary_lemma_2 bip1 c; 
    IntLibLemmas.pow2_increases 64 27;
    IntLibLemmas.pow2_doubles 51;
    IntLibLemmas.pow2_increases 51 15;
    let z = bip1 ^+ c in 
    cut (v z = v bip1 + v c /\ v c < 2 /\ v bip1 < pow2 51); 
    cut (v z >= pow2 51 ==> v c = 1); 
    cut (v c > 0 ==> IntLib.div (v (get h0 b i)) (pow2 51) > 0 ==> v (get h0 b i) >= pow2 51); 
    cut (v z >= pow2 51 ==> v (get h1 b i) < pow2 15); 
    upd b (i+1) z;
    let h2 = ST.get() in 
    cut (v z >= pow2 51 ==> v c = 1 /\ True); 
//    eval_carry_lemma h0 b h2 b i; 
    carry2_aux_limb b (i+1)

val carry_top_to_0_limb: b:bigint -> ST unit
    (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1
      /\ v (get h b 0) + 5 * v (get h b norm_length) < pow2 62))
    (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carried' h1 b 1
      /\ eval h1 b norm_length % (reveal prime) = eval h0 b (norm_length+1) % (reveal prime)
      /\ v (get h1 b 0) = v (get h0 b 0) + 5 * v (get h0 b norm_length)
      /\ (forall (i:nat). {:pattern (v (get h1 b i))} (i > 0 /\ i < length b) ==> 
	  v (get h1 b i) = v (get h0 b i))
      /\ modifies_buf (only b) h0 h1))
let carry_top_to_0_limb b =
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  let btop_5 = times_19 btop in  
    upd b 0 (b0 ^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0

val carry2_limb: b:bigint  -> ST unit
  (requires (fun h -> carried h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carried h0 b norm_length /\ carriable2 h1 b norm_length 
    /\ eval h1 b (norm_length+1) % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_buf (only b) h0 h1))
let rec carry2_limb b = 
  let h0 = ST.get() in
  pow2_3_lemma ();
  IntLibLemmas.pow2_exp 3 37;
  IntLibLemmas.pow2_increases 40 37;
  IntLibLemmas.pow2_increases 40 51;
  IntLibLemmas.pow2_doubles 40;
  IntLibLemmas.pow2_increases 62 41;
  carry_top_to_0_limb b;
  let h1 = ST.get() in
  upd b norm_length zero;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b (norm_length)); 
  let bi = index b 0 in 
  let ri = mod2_51 bi in
//  assert(v ri < pow2 51); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^>> 51) in
  cut (v bi < pow2 41); 
  // In the spec of >>, TODO
  assume (v c < pow2 15); 
  let bip1 = index b 1 in 
//  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 64 27;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 51 15; 
  let z = bip1 ^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
//  eval_carry_lemma h2 b h4 b 0; 
  cut(carriable2 h4 b 1);
  carry2_aux_limb b 1
  
val last_carry_limb: b:bigint -> ST unit
  (requires (fun h -> carriable2 h b norm_length /\ length b >= 2*norm_length-1))
  (ensures (fun h0 _ h1 -> carriable2 h0 b norm_length /\ norm h1 b
    /\ eval h1 b norm_length % reveal prime = eval h0 b (norm_length+1) % reveal prime
    /\ modifies_buf (only b) h0 h1))
let last_carry_limb b =
  let h0 = ST.get() in
  let b0 = index b 0 in
  let btop = index b norm_length in 
  cut (v b0 < pow2 51 /\ v btop < 2); 
  pow2_3_lemma ();
  cut (5 * v btop < pow2 3 /\ True); 
  IntLibLemmas.pow2_increases 51 3;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 64 27;
  cut(v b0 + 5 * v btop < pow2 27 /\ True); 
  let btop_5 = times_19 btop in  
  upd b 0 (b0 ^+ btop_5); 
  let h1 = ST.get() in
  freduce_degree_lemma h0 h1 b 0;
  upd b norm_length zero;
  let h2 = ST.get() in
  eval_eq_lemma h1 h2 b b norm_length;
  cut (eval h2 b (norm_length+1) = eval h1 b norm_length);
  let bi = index b 0 in 
  let ri = mod2_51 bi in
  cut(v ri < pow2 51); 
  upd b 0 ri; 
  let h3 = ST.get() in
  let c = (bi ^>> 51) in
  cut (v bi < pow2 51 + 5); 
  cut (v bi >= pow2 51 ==> v (get h3 b 1) < pow2 15); 
  // In the spec of >>, TODO
  assume (v bi >= pow2 51 ==> v c = 1); 
  let bip1 = index b 1 in 
//  auxiliary_lemma_2 bip1 c; 
  IntLibLemmas.pow2_increases 64 27;
  IntLibLemmas.pow2_doubles 51;
  IntLibLemmas.pow2_increases 51 15; 
  let z = bip1 ^+ c in 
  upd b 1 z;
  let h4 = ST.get() in 
//  eval_carry_lemma h2 b h4 b 0; 
  cut (v (get h4 b 1) < pow2 51); 
  cut (norm h4 b)

val freduce_coefficients: b:bigint -> ST unit
  (requires (fun h -> live h b  
    /\ (forall (i:nat). {:pattern (v (get h b i))} i < norm_length ==> v (get h b i) < pow2 (platform_size-1))))
  (ensures (fun h0 _ h1 -> live h0 b /\ norm h1 b 
    /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime
    /\ modifies_buf (only b) h0 h1))
let freduce_coefficients b = 
  let h0 = ST.get() in
  // Hardcoding size
  let tmp = create #64 zero (norm_length+1) in 
  let h1 = ST.get() in
//  eq_lemma h0 h1 b empty; 
//  eval_eq_lemma h0 h1 b b norm_length; 
  blit b 0 tmp 0 norm_length;
  let h2 = ST.get() in
//  eval_eq_lemma h1 h2 b tmp norm_length;
//  cut (forall (i:nat). {:pattern (v (get h2 tmp i))} i < norm_length ==> v (get h2 tmp i) = v (get h0 b i)); 
  carry_limb tmp 0; 
  carry2_limb tmp; 
  last_carry_limb tmp; 
  let h = ST.get() in
  blit tmp 0 b 0 norm_length; 
  let h' = ST.get() in
  eval_eq_lemma h h' tmp b norm_length; 
  cut (forall (i:nat). {:pattern (v (get h tmp i))} i < norm_length ==> v (get h tmp i) < pow2 51); 
  cut (forall (i:nat). {:pattern (v (get h' b i))} i < norm_length ==> v (get h' b (0+i)) = v (get h tmp (0+i)))

val add_big_zero_core: b:bigint -> ST unit
  (requires (fun h -> norm h b))
  (ensures (fun h0 _ h1 -> norm h0 b /\ live h1 b /\ length b = length b
			 /\ filled h1 b
			 /\ v (get h1 b 0) = v (get h0 b 0) + (pow2 52 - 38)
			 /\ v (get h1 b 1) = v (get h0 b 1) + (pow2 52 - 2)
			 /\ v (get h1 b 2) = v (get h0 b 2) + (pow2 52 - 2)
			 /\ v (get h1 b 3) = v (get h0 b 3) + (pow2 52 - 2)
			 /\ v (get h1 b 4) = v (get h0 b 4) + (pow2 52 - 2)
			 /\ modifies_buf (only b) h0 h1))
let add_big_zero_core b =
  let h0 = ST.get() in
  let two52m38 = of_string "0xfffffffffffda" in // pow2 52 - 38
  let two52m2 =  of_string "0xffffffffffffe" in // pow2 52 - 2
  assume (v two52m38 = pow2 52 - 38 /\ v two52m2 = pow2 52 - 2); 
  let b0 = index b 0 in 
  (* cut(True /\ v b0 = v (get h0 b 0));  *)
  (* cut(forall (i:nat). {:pattern (v (get h0 b i))} i < norm_length ==> bitsize (v (get h0 b i)) (templ i));  *)
  (* cut(forall (i:nat). i < norm_length ==> v (get h0 b i) < pow2 (templ i));  *)
  (* cut (v b0 < pow2 51 /\ v two52m38 < pow2 52);  *)
  (* addition_lemma b0 51 two52m38 52; *)
  (* Lemmas.pow2_increases_1 platform_size 53;  *)
  upd b 0 (b0 ^+ two52m38); 

  let h1 = ST.get() in
//  upd_lemma h0 h1 b 0 (b0 ^+ two52m38); 
  let b1 = index b 1 in
//  cut (v b1 = v (get h0 b 1) /\ v b1 < pow2 51 /\ v two52m2 < pow2 52); 
//  addition_lemma b1 51 two52m2 52;
//  Lemmas.pow2_increases_1 platform_size 53; 
  upd b 1 (b1 ^+ two52m2); 
  
  let h2 = ST.get() in
//  upd_lemma h1 h2 b 1 (b1 ^+ two52m2); 
  let b2 = index b 2 in
//  cut (v b2 = v (get h1 b 2) /\ v (get h1 b 2) = v (get h0 b 2) /\ v b2 < pow2 51);
//  addition_lemma b2 51 two52m2 52;
//  Lemmas.pow2_increases_1 platform_size 53; 
  upd b 2 (b2 ^+ two52m2); 

  let h3 = ST.get() in
//  upd_lemma h2 h3 b 2 (add_limb b2 two52m2); 
  let b3 = index b 3 in
//  cut (v b3 = v (get h2 b 3) /\ v (get h2 b 3) = v (get h1 b 3) /\ v (get h1 b 3) = v (get h0 b 3) /\ v b3 < pow2 51);
//  addition_lemma b3 51 two52m2 52;
//  Lemmas.pow2_increases_1 platform_size 53; 
  upd b 3 (b3 ^+ two52m2); 
  
  let h4 = ST.get() in
//  upd_lemma h3 h4 b 3 (b3 ^+ two52m2); 
  let b4 = index b 4 in
//  cut (v b4 = v (get h3 b 4) /\ v (get h3 b 4) = v (get h2 b 4) /\ v (get h2 b 4) = v (get h1 b 4) /\ v (get h1 b 4) = v (get h0 b 4) /\ v b4 < pow2 51);
//  addition_lemma b4 51 two52m2 52;
//  Lemmas.pow2_increases_1 platform_size 53; 
  upd b 4 (b4 ^+ two52m2);
  let h5 = ST.get() in 
//  upd_lemma h4 h5 b 4 (b4 ^+ two52m2);
  (* cut (v (get h5 b 0) = v (get h0 b 0) + (pow2 52 - 38) /\ True);  *)
  (* cut (v (get h5 b 1) = v (get h0 b 1) + (pow2 52 - 2) /\ True);  *)
  (* cut (v (get h5 b 2) = v (get h0 b 2) + (pow2 52 - 2) /\ True);  *)
  (* cut (v (get h5 b 3) = v (get h0 b 3) + (pow2 52 - 2) /\ True);  *)
  (* cut (v (get h5 b 4) = v (get h0 b 4) + (pow2 52 - 2) /\ True);  *)
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) < pow2 ndiff);  *)
//  aux_lemma_1 (); 
  (* cut (forall (i:nat). {:pattern (v (get h5 b i))} i < 5 ==> v (get h5 b i) >= pow2 ndiff');  *)
  (* cut (norm_length = 5 /\ True);  *)
  (* cut(filled h5 b ) *)
  ()

(*
val aux_lemma_2: a:int -> b:int -> c:int -> d:int -> e:int ->
  Lemma (pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) =
	 pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 256 - 38)
let aux_lemma_2 a b c d e =
  let v = pow2 204 * (a + pow2 52 - 2) + pow2 153 * (b + pow2 52 - 2) + pow2 102 * (c + pow2 52 - 2) 
	 + pow2 51 * (d + pow2 52 - 2) + (e + pow2 52 - 38) in
  cut (True /\ v = pow2 204 * a + pow2 153 * b + pow2 102 * c + pow2 51 * d + e + pow2 204 * pow2 52 - pow2 204 * 2 + pow2 153 * pow2 52 - pow2 153 * 2 + pow2 102 * pow2 52 - pow2 102 * 2 + pow2 51 * pow2 52 - pow2 51 * 2 + pow2 52 - 38); 
  cut (True /\ pow2 1 = 2)//; 
//  Lemmas.pow2_exp_1 204 52; Lemmas.pow2_exp_1 204 2; 
//  Lemmas.pow2_exp_1 153 52; Lemmas.pow2_exp_1 153 2; 
//  Lemmas.pow2_exp_1 102 52; Lemmas.pow2_exp_1 102 2; 
//  Lemmas.pow2_exp_1 51 52; Lemmas.pow2_exp_1 51 2

*)

// Missing modulo spec, TODO: add to axioms
val modulo_lemma_2: a:int -> b:pos -> Lemma ( (a + 2 * b) % b = a % b)
let modulo_lemma_2 a b = admit(); ()

val aux_lemma_3: a:int -> Lemma (requires (True)) (ensures ((a + pow2 256 - 38) % reveal prime = a % reveal prime))
let aux_lemma_3 a =
//  Lemmas.pow2_double_mult 255;
  cut (True /\ 2 * reveal prime = pow2 256 - 38);
  modulo_lemma_2 a (reveal prime)

val add_big_zero_lemma: h0:heap -> h1:heap -> b:bigint -> 
  Lemma (requires (norm h0 b /\ live h1 b /\ length b = length b 
		  /\ filled h1 b 
		  /\ v (get h1 b 0) = v (get h0 b 0) + (pow2 52 - 38)
		  /\ v (get h1 b 1) = v (get h0 b 1) + (pow2 52 - 2)
		  /\ v (get h1 b 2) = v (get h0 b 2) + (pow2 52 - 2)
		  /\ v (get h1 b 3) = v (get h0 b 3) + (pow2 52 - 2)
		  /\ v (get h1 b 4) = v (get h0 b 4) + (pow2 52 - 2) ))
	(ensures (norm h0 b /\ live h1 b /\ length b = length b
		 /\ eval h1 b norm_length % reveal prime = eval h0 b norm_length % reveal prime))
let add_big_zero_lemma h0 h1 b =
  cut (bitweight templ 0 = 0 /\ bitweight templ 1 = 51 /\ bitweight templ 2 = 102 /\ bitweight templ 3 = 153 /\ bitweight templ 4 = 204); 
  cut (True /\ eval h1 b norm_length = pow2 204 * (v (get h0 b 4) + pow2 52 - 2) + eval h1 b 4); 
  cut (True /\ eval h1 b 4 = pow2 153 * (v (get h0 b 3) + pow2 52 - 2) + eval h1 b 3); 
  cut (True /\ eval h1 b 3 = pow2 102 * (v (get h0 b 2) + pow2 52 - 2) + eval h1 b 2); 
  cut (True /\ eval h1 b 2 = pow2 51 * (v (get h0 b 1) + pow2 52 - 2) + eval h1 b 1); 
  cut (True /\ eval h1 b 1 = (v (get h0 b 0) + pow2 52 - 38)); 
  cut (eval h1 b norm_length = 
	    pow2 204 * (v (get h0 b 4) + pow2 52 - 2) 
	    + pow2 153 * (v (get h0 b 3) + pow2 52 - 2) 
	    + pow2 102 * (v (get h0 b 2) + pow2 52 - 2) 
	    + pow2 51 * (v (get h0 b 1) + pow2 52 - 2) 
	    + (v (get h0 b 0) + pow2 52 - 38) /\ True); 
  cut (True /\ eval h0 b norm_length = pow2 204 * v (get h0 b 4)  + eval h0 b 4); 
  cut (True /\ eval h0 b 4 = pow2 153 * v (get h0 b 3)  + eval h0 b 3); 
  cut (True /\ eval h0 b 3 = pow2 102 * v (get h0 b 2) + eval h0 b 2); 
  cut (True /\ eval h0 b 2 = pow2 51 * v (get h0 b 1) + eval h0 b 1); 
  cut (True /\ eval h0 b 1 = v (get h0 b 0) ); 
  cut (True /\ eval h0 b norm_length = pow2 204 * v (get h0 b 4) + pow2 153 * v (get h0 b 3)  
			       + pow2 102 * v (get h0 b 2) + pow2 51 * v (get h0 b 1) 
			       + v (get h0 b 0)); 
//  aux_lemma_2 (v (get h0 b 4)) (v (get h0 b 3)) (v (get h0 b 2)) (v (get h0 b 1)) (v (get h0 b 0));
  let a = pow2 204 * v (get h0 b 4) + pow2 153 * v (get h0 b 3)  
			       + pow2 102 * v (get h0 b 2) + pow2 51 * v (get h0 b 1) 
			       + v (get h0 b 0) in
  aux_lemma_3 a			       

val add_big_zero: bigint -> St unit
let add_big_zero b =
  let h0 = ST.get() in
  add_big_zero_core b;
  let h1 = ST.get() in
  add_big_zero_lemma h0 h1 b
