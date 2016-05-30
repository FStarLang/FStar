(* Implementation of Poly1305 based on the rfc7539 *)
module Poly

open FStar.Heap
open FStar.Ghost
open Axioms
open IntLib
open SInt
open SInt.UInt63
open SInt.Cast
open SBytes
open SBuffer
open Bigint
open Parameters
open Bignum

(* Auxiliary lemmas and functions *)

val max_value_increases: h:heap -> b:bigint{live h b} -> n:pos -> m:pos{m>=n /\ m <= length b} -> Lemma
  (maxValue h b n <= maxValue h b m)
let rec max_value_increases h b n m =
  match (m-n) with
  | 0 -> () | _ -> max_value_increases h b n (m-1)

val pow2_5_lemma: unit -> Lemma (requires (True)) (ensures (pow2 5 = 32))
let pow2_5_lemma () = 
  ()

val satisfies_constraints_after_multiplication: h:heap -> b:bigint{live h b /\ length b >= 2*norm_length-1 /\ maxValue h b (length b) <= norm_length * pow2 53} -> Lemma (requires (True))
  (ensures (satisfiesModuloConstraints h b)) 
let satisfies_constraints_after_multiplication h b =
  max_value_increases h b (2*norm_length-1) (length b);
  pow2_5_lemma ();
  cut (maxValue h b (2*norm_length-1) * 6 <= 30 * pow2 53 /\ 30 * pow2 53 < pow2 5 * pow2 53);  
  IntLibLemmas.pow2_exp 5 53;
  IntLibLemmas.pow2_increases 63 58

assume val aux_lemma': a:nat -> n:nat{n <= 32} -> Lemma (requires True) (ensures ((((a * pow2 (32 - n)) % pow2 63) % pow2 26) % pow2 (32 - n) = 0 ))
(* let aux_lemma' a n =  *)
(*   if 32-n > 26 then ( *)
(*     IntLibLemmas.pow2_exp (32-n-26) 26; *)
(*     IntLibLemmas.modulo_lemma (a * pow2 (32-n-26)) (pow2 26) ) *)
(*   else if 32 - n = 26 then  *)
(*     IntLibLemmas.modulo_lemma a (pow2 26) *)
(*   else () *)

val aux_lemma: x:uint63{v x < pow2 32} -> y:uint63{v y < pow2 32} -> n:nat{n >= 7 /\ n < 32} -> Lemma
  (requires (True))
  (ensures (IntLib.div (v x) (pow2 n) + (((v y * pow2 (32 - n)) % pow2 63) % pow2 26) < pow2 26)) 
let aux_lemma x y n =
  IntLibLemmas.div_pow2_inequality (v x) 32;
  IntLibLemmas.pow2_increases 26 (32-n);
  aux_lemma' (v y) n;
  let a = IntLib.div (v x) (pow2 n) in
  let b = ((v y * pow2 (32 - n)) % pow2 63) % pow2 26 in
  let n1 = 26 in
  let n2 = 32 - n in 
  IntLibLemmas.div_positive (v x) (pow2 n); 
  IntLibLemmas.pow2_disjoint_ranges a b n1 n2

val aux_lemma_1: x:uint63{v x < pow2 32} -> Lemma (requires (True)) (ensures (v (x ^>> 8) < pow2 24)) 
let aux_lemma_1 x = IntLibLemmas.div_pow2_inequality (v x) 32  

val aux_lemma_2: b:bigint -> Lemma (requires (True)) (ensures ((arefs (only b)) = !{content b})) 
let aux_lemma_2 b = 
  FStar.Set.lemma_equal_intro (arefs (only b)) !{content b};
  cut (True /\ arefs (only b) = !{content b})

val aux_lemma_3: h0:heap -> h1:heap -> b:bigint -> Lemma (requires (modifies (arefs (only b)) h0 h1))
  (ensures (modifies !{content b} h0 h1))
let aux_lemma_3 h0 h1 b = 
  aux_lemma_2 b; ()

(*** Poly1305 code ***)

(* Bigint to bytes serializing function *)
val num_to_le_bytes: s:sbytes{length s >= 16} -> b:bigint{disjoint b s} -> ST unit
  (requires (fun h -> norm h b /\ SBuffer.live h s))
  (ensures (fun h0 _ h1 -> SBuffer.live h1 s /\ modifies_buf (only s) h0 h1))
let num_to_le_bytes s b =
  let h0 = ST.get() in
  let b0 = index b 0 in
  let b1 = index b 1 in
  let b2 = index b 2 in
  let b3 = index b 3 in
  let b4 = index b 4 in 
  upd s 0 (SInt.Cast.uint63_to_uint8 b0);  // 0 
  upd s 1 (SInt.Cast.uint63_to_uint8 (b0 ^>> 8)); //8
  upd s 2 (SInt.Cast.uint63_to_uint8 (b0 ^>> 16)); //16
  upd s 3 (SInt.UInt8.add_mod (SInt.Cast.uint63_to_uint8 (b0 ^>> 24)) // 24 
			       (SInt.Cast.uint63_to_uint8 (b1 ^<< 2))); 
  upd s 4 (SInt.Cast.uint63_to_uint8 (b1 ^>> 6)); // 32
  upd s 5 (SInt.Cast.uint63_to_uint8 (b1 ^>> 14)); // 40
  upd s 6 (SInt.UInt8.add_mod (SInt.Cast.uint63_to_uint8 (b1 ^>> 22)) 
			       (SInt.Cast.uint63_to_uint8 (b2 ^<< 4))); // 48
  upd s 7 (SInt.Cast.uint63_to_uint8 (b2 ^>> 4)); // 56
  upd s 8 (SInt.Cast.uint63_to_uint8 (b2 ^>> 12)); // 64
  upd s 9 (SInt.UInt8.add_mod (SInt.Cast.uint63_to_uint8 (b2 ^>> 20)) 
			       (SInt.Cast.uint63_to_uint8 (b3 ^<< 6))); // 72
  upd s 10 (SInt.Cast.uint63_to_uint8 (b3 ^>> 2)); // 80 
  upd s 11 (SInt.Cast.uint63_to_uint8 (b3 ^>> 10)); // 88
  let h = ST.get() in
  cut (SBuffer.live h s /\ modifies_buf (only s) h0 h); 
  upd s 12 (SInt.Cast.uint63_to_uint8 (b3 ^>> 18)); // 96
  upd s 13 (SInt.Cast.uint63_to_uint8 (b4)); // 104
  upd s 14 (SInt.Cast.uint63_to_uint8 (b4 ^>> 8)); // 112 
  upd s 15 (SInt.Cast.uint63_to_uint8 (b4 ^>> 16)); // 120 
  ()

(* Bytes to bigint deserializing functions *)
val le_bytes_to_num: b:bigint -> s:sbytes{length s = 16 /\ disjoint b s} -> ST unit
  (requires (fun h -> live h b /\ SBuffer.live h s))
  (ensures (fun h0 _ h1 -> norm h1 b /\ modifies_buf (only b) h0 h1  /\ v (get h1 b 4) < pow2 24))
let le_bytes_to_num b s =
  admit(); // TODO
  IntLibLemmas.pow2_increases 63 26;
  IntLibLemmas.pow2_increases 63 32;
  IntLibLemmas.pow2_increases 26 24;
  let mask_26 = SInt.UInt63.sub (SInt.UInt63.one ^<< 26) SInt.UInt63.one in 
  cut (v mask_26 = v one * pow2 26 - v one /\ v one = 1); 
  cut (v mask_26 = pow2 26 - 1); 
  let s0 = sub s 0  4 in
  let s1 = sub s 4  4 in
  let s2 = sub s 8  4 in
  let s3 = sub s 12 4 in
  let n0 = uint32_to_uint63 (SBytes.uint32_of_sbytes s0) in 
  let n1 = uint32_to_uint63 (SBytes.uint32_of_sbytes s1) in
  let n2 = uint32_to_uint63 (SBytes.uint32_of_sbytes s2) in
  let n3 = uint32_to_uint63 (SBytes.uint32_of_sbytes s3) in 
  ulogand_lemma_4 #63 n0 26 mask_26;
  ulogand_lemma_4 #63 (n1 ^<< 6) 26 mask_26; 
  ulogand_lemma_4 #63 (n2 ^<< 12) 26 mask_26; 
  ulogand_lemma_4 #63 (n3 ^<< 18) 26 mask_26;  
  aux_lemma n0 n1 26; 
  aux_lemma n1 n2 20;
  aux_lemma n2 n3 14;  
  aux_lemma_1 n3; 
  let n0' = n0 ^& mask_26 in
  let n1' = (n0 ^>> 26) ^+ ((n1 ^<< 6) ^& mask_26) in 
  let n2' = (n1 ^>> 20) ^+ ((n2 ^<< 12) ^& mask_26) in
  let n3' = (n2 ^>> 14) ^+ ((n3 ^<< 18) ^& mask_26) in 
  let n4' = (n3 ^>> 8) in 
  upd b 0 n0'; 
  upd b 1 n1';
  upd b 2 n2'; 
  upd b 3 n3';
  upd b 4 n4';
  ()

(* Runs "Acc = ((Acc+block)*r) % p." *)
val add_and_multiply: acc:bigint -> block:bigint{disjoint acc block} -> r:bigint{disjoint acc r /\ disjoint block r} -> ST unit
  (requires (fun h -> norm h acc /\ norm h block /\ norm h r))
  (ensures (fun h0 _ h1 -> norm h0 acc /\ norm h0 block /\ norm h0 r /\ norm h1 acc
    /\ modifies_buf (only acc) h0 h1
    /\ eval h1 acc norm_length % reveal prime = 
    ((eval h0 acc norm_length + eval h0 block norm_length) * eval h0 r norm_length) % reveal prime))
let add_and_multiply acc block r =
  let h0 = ST.get() in
  fsum' acc block; 
  let h1 = ST.get() in
  let tmp = create #63 SInt.UInt63.zero (2*norm_length-1) in 
  let h2 = ST.get() in 
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) = v (get h1 acc i));
  cut (forall (i:nat). {:pattern (v (get h1 acc i))} i < norm_length ==> v (get h1 acc i) = v (get h0 acc (i+0)) + v (get h0 block (i+0)));
  cut (forall (i:nat). {:pattern (v (get h0 acc i))} i < norm_length ==> v (get h0 acc i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h0 block i))} i < norm_length ==> v (get h0 block i) < pow2 26);
  IntLibLemmas.pow2_doubles 26;
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) < pow2 27);
  cut (bound27 h2 acc); 
  eq_lemma h0 h2 r (only acc); 
  cut (null h2 tmp); 
  multiplication tmp acc r; 
  let h3 = ST.get() in
  satisfies_constraints_after_multiplication h3 tmp;
  modulo tmp; 
  let h4 = ST.get() in
  blit tmp 0 acc 0 norm_length;
  let h5 = ST.get() in
  cut (modifies_buf (only acc) h0 h5); 
  cut (forall (i:nat). {:pattern (v (get h5 acc i))} i < norm_length ==> v (get h5 acc (0+i)) = v (get h4 tmp (0+i))); 
  cut (norm h5 acc); 
  eval_eq_lemma h4 h5 tmp acc norm_length;
  eval_eq_lemma h1 h2 acc acc norm_length;
  eval_eq_lemma h0 h2 r r norm_length;
  ()

val clamp: r:sbytes{length r = 16} -> ST unit
  (requires (fun h -> SBuffer.live h r))
  (ensures (fun h0 _ h1 -> SBuffer.live h1 r /\ modifies_buf (only r) h0 h1))
let clamp r =
  let mask_15 = SInt.UInt8.of_int 15 in
  let mask_252 = SInt.UInt8.of_int 252 in
  upd r 3  (SInt.UInt8.op_Hat_Amp (index r 3 ) mask_15);
  upd r 7  (SInt.UInt8.op_Hat_Amp (index r 7 ) mask_15);
  upd r 11 (SInt.UInt8.op_Hat_Amp (index r 11) mask_15);
  upd r 15 (SInt.UInt8.op_Hat_Amp (index r 15) mask_15);
  upd r 4  (SInt.UInt8.op_Hat_Amp (index r 4 ) mask_252);
  upd r 8  (SInt.UInt8.op_Hat_Amp (index r 8 ) mask_252);
  upd r 12 (SInt.UInt8.op_Hat_Amp (index r 12) mask_252);
  ()

#reset-options "--z3timeout 20"

val poly1305_step: msg:sbytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> ctr:nat{length msg >= 16 * ctr} ->
  ST unit
    (requires (fun h -> SBuffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> SBuffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_buf (only acc) h0 h1))
let rec poly1305_step msg acc r ctr =
  let h0 = ST.get() in
  match ctr with
  | 0 -> ()
  | _ -> 
    let n = sub msg 0 16 in
    let msg = offset msg 16 in
    //    let n, msg = SBytes.split msg 16 in 
    let h = ST.get() in
    let block = create #63 SInt.UInt63.zero norm_length in 
    let h' = ST.get() in
    le_bytes_to_num block n; 
    let b4 = index block 4 in
    IntLibLemmas.pow2_doubles 24; IntLibLemmas.pow2_increases 26 25;
    IntLibLemmas.pow2_increases 63 26; 
    upd block 4 (b4 ^+ (SInt.UInt63.one ^<< 24)); 
    let h1 = ST.get() in
    eq_lemma h0 h1 r (empty); 
    eq_lemma h0 h1 acc empty;
    add_and_multiply acc block r; 
    let h2 = ST.get() in 
    disjoint_only_lemma msg acc; 
    eq_lemma h1 h2 r (only acc); 
    eq_lemma h h2 msg (only acc); 
    cut (modifies_buf (only acc) h0 h2); 
    aux_lemma_2 acc;
    cut (modifies (arefs (only acc)) h0 h2); 
    aux_lemma_3 h0 h2 acc;
    cut (modifies !{content acc} h0 h2); 
    cut (SBuffer.live h2 msg); 
    poly1305_step msg acc r (ctr-1);
    ()

#reset-options "--z3timeout 100"

val poly1305_last: msg:sbytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> len:nat{len <= length msg} ->
  ST unit
    (requires (fun h -> SBuffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> SBuffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_buf (only acc) h0 h1))
let poly1305_last msg acc r len =
  let h0 = ST.get() in
  let l = len % 16 in
  if l = 0 then ()
  else (
    let n = create SInt.UInt8.zero 16 in
    blit msg (len - l) n 0 l; 
    upd n l (SInt.UInt8.of_int 1);
    let h1 = ST.get() in
    let block = create #63 SInt.UInt63.zero norm_length in 
    let h2 = ST.get() in
    le_bytes_to_num block n; 
    let b4 = index block 4 in
    IntLibLemmas.pow2_doubles 24; IntLibLemmas.pow2_increases 26 25;
    IntLibLemmas.pow2_increases 63 26; 
    let h3 = ST.get() in
    eq_lemma h0 h3 r (empty); 
    eq_lemma h0 h3 acc empty;     
    add_and_multiply acc block r;
    let h4 = ST.get() in 
    disjoint_only_lemma msg acc; 
    eq_lemma h3 h4 r (only acc); 
    eq_lemma h1 h4 msg (only acc); 
    aux_lemma_2 acc;
    aux_lemma_3 h0 h4 acc;
    () )

val poly1305_mac: hash:sbytes{length hash >= 16} -> msg:sbytes{disjoint hash msg} -> 
  len:nat{len <= length msg} -> key:sbytes{length key = 32 /\ disjoint msg key /\ disjoint hash key} -> 
  ST unit
    (requires (fun h -> SBuffer.live h msg /\ SBuffer.live h key /\ SBuffer.live h hash))
    (ensures (fun h0 _ h1 -> SBuffer.live h1 hash /\ modifies_buf (only hash) h0 h1))
let poly1305_mac hash msg len key =
  let h0 = ST.get() in
  let r' = sub key 0 16 in
  let s = sub key 16 16 in
  let r = create SInt.UInt8.zero 16 in
  blit r' 0 r 0 16;
  let h0' = ST.get() in
  clamp r; 
  let h0'' = ST.get() in
  let bigint_r = create #63 SInt.UInt63.zero norm_length in
  let bigint_s = create #63 SInt.UInt63.zero norm_length in 
  le_bytes_to_num bigint_r r; 
  let h1 = ST.get() in
  disjoint_only_lemma s r; 
  le_bytes_to_num bigint_s s; 
  let h2 = ST.get() in
  cut (modifies_buf (only r) h0'' h2); 
  let acc = create #63 SInt.UInt63.zero norm_length in 
  let h2' = ST.get() in
  let ctr = len / 16 in
  let rest = len % 16 in 
  eq_lemma h1 h2' bigint_r (only bigint_s); 
  disjoint_only_lemma bigint_r bigint_s;
  disjoint_only_lemma msg bigint_s;
  assume (norm h2' bigint_r);  // TODO
  assume (SBuffer.live h0' msg); // TODO
  disjoint_only_lemma msg r; 
  cut (SBuffer.live h0'' msg); 
  poly1305_step msg acc bigint_r ctr; 
  let h3 = ST.get() in
  poly1305_last msg acc bigint_r len;
  let h3' = ST.get() in
  eq_lemma h2 h3' bigint_s empty; 
  fsum' acc bigint_s; 
  let h4 = ST.get() in
  IntLibLemmas.pow2_doubles 26;
  IntLibLemmas.pow2_increases 62 27; 
  cut (forall (i:nat). {:pattern (v (get h3' acc i))} i < norm_length ==> v (get h3' acc i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h3' bigint_s i))} i < norm_length ==> v (get h3' bigint_s i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) = v (get h3' acc (i+0)) + v (get h3' bigint_s (i+0))); 
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) < pow2 27);
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) < pow2 63);
  freduce_coefficients acc; 
  let h45 = ST.get() in
  finalize acc;
  disjoint_only_lemma hash r;  
  let h5 = ST.get() in
  disjoint_only_lemma hash bigint_r;  
  disjoint_only_lemma hash bigint_s;  
  disjoint_only_lemma hash acc;  
  cut (SBuffer.live h5 hash); 
  num_to_le_bytes hash acc; 
  let h6 = ST.get() in
  cut (modifies_buf (only hash) h0 h6);
  ()
