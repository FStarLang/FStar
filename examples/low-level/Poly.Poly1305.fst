(* Implementation of Poly1305 based on the rfc7539 *)
module Poly.Poly1305

open FStar.Mul
open FStar.HyperStack
open FStar.HST
open FStar.Ghost
open Math.Axioms
open Math.Lib
open Math.Lemmas
open FStar.UInt64
open FStar.Buffer
open Poly.Bigint
open Poly.Parameters
open Poly.Bignum

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

let u32 = UInt32.t

let w: u32 -> Tot int = U32.v

let op_Plus_Bar = U32.add
let op_Subtraction_Bar = U32.sub
let op_Hat_Star = U64.mul
let op_Hat_Less_Less = U64.op_Less_Less_Hat
let op_Hat_Greater_Greater = U64.op_Greater_Greater_Hat
let op_Hat_Subtraction = U64.op_Subtraction_Hat
let op_Hat_Amp = U64.op_Amp_Hat

let op_Hat_Bar_Hat = U32.op_Bar_Hat
let op_Bar_Less_Less = U32.op_Less_Less_Hat

let heap = HS.mem

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
  (* IntLibLemmas.pow2_exp 5 53; *)
  (* IntLibLemmas.pow2_increases 63 58; *)
  ()

assume val aux_lemma': a:nat -> n:nat{n <= 32} -> Lemma (requires True) (ensures ((((a * pow2 (32 - n)) % pow2 63) % pow2 26) % pow2 (32 - n) = 0 ))
(* let aux_lemma' a n =  *)
(*   if 32-n > 26 then ( *)
(*     IntLibLemmas.pow2_exp (32-n-26) 26; *)
(*     IntLibLemmas.modulo_lemma (a * pow2 (32-n-26)) (pow2 26) ) *)
(*   else if 32 - n = 26 then  *)
(*     IntLibLemmas.modulo_lemma a (pow2 26) *)
(*   else () *)

val aux_lemma: x:u64{v x < pow2 32} -> y:u64{v y < pow2 32} -> n:nat{n >= 7 /\ n < 32} -> Lemma
  (requires (True))
  (ensures (Math.Lib.div (v x) (pow2 n) + (((v y * pow2 (32 - n)) % pow2 63) % pow2 26) < pow2 26)) 
let aux_lemma x y n =
  (* IntLibLemmas.div_pow2_inequality (v x) 32; *)
  (* IntLibLemmas.pow2_increases 26 (32-n); *)
  aux_lemma' (v y) n;
  let a = Math.Lib.div (v x) (pow2 n) in
  let b = ((v y * pow2 (32 - n)) % pow2 63) % pow2 26 in
  let n1 = 26 in
  let n2 = 32 - n in 
  (* IntLibLemmas.div_positive (v x) (pow2 n);  *)
  (* IntLibLemmas.pow2_disjoint_ranges a b n1 n2; *)
  ()

val aux_lemma_1: x:u64{v x < pow2 32} -> Lemma (requires (True)) (ensures (v (x ^>> 8ul) < pow2 24)) 
let aux_lemma_1 x = 
  (* IntLibLemmas.div_pow2_inequality (v x) 32; *)
  ()
  

(* val aux_lemma_2: b:bigint -> Lemma (requires (True)) (ensures ((arefs (only b)) = !{content b}))  *)
(* let aux_lemma_2 b =  *)
(*   FStar.Set.lemma_equal_intro (arefs (only b)) !{content b}; *)
(*   cut (True /\ arefs (only b) = !{content b}) *)

(* val aux_lemma_3: h0:heap -> h1:heap -> b:bigint -> Lemma (requires (modifies (arefs (only b)) h0 h1)) *)
(*   (ensures (modifies !{content b} h0 h1)) *)
(* let aux_lemma_3 h0 h1 b =  *)
(*   aux_lemma_2 b; () *)

(*** Poly1305 code ***)

(* Bigint to bytes serializing function *)
val num_to_le_bytes: s:bytes{length s >= 16} -> b:bigint{disjoint b s} -> ST unit
  (requires (fun h -> norm h b /\ Buffer.live h s))
  (ensures (fun h0 _ h1 -> Buffer.live h1 s /\ modifies_1 s h0 h1))
let num_to_le_bytes s b =
  let h0 = HST.get() in
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in 
  upd s 0ul (Int.Cast.uint64_to_uint8 b0);  // 0 
  upd s 1ul (Int.Cast.uint64_to_uint8 (b0 ^>> 8ul)); //8
  upd s 2ul (Int.Cast.uint64_to_uint8 (b0 ^>> 16ul)); //16
  upd s 3ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b0 ^>> 24ul)) // 24 
			       (Int.Cast.uint64_to_uint8 (b1 ^<< 2ul))); 
  upd s 4ul (Int.Cast.uint64_to_uint8 (b1 ^>> 6ul)); // 32
  upd s 5ul (Int.Cast.uint64_to_uint8 (b1 ^>> 14ul)); // 40
  upd s 6ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b1 ^>> 22ul)) 
			       (Int.Cast.uint64_to_uint8 (b2 ^<< 4ul))); // 48
  upd s 7ul (Int.Cast.uint64_to_uint8 (b2 ^>> 4ul)); // 56
  upd s 8ul (Int.Cast.uint64_to_uint8 (b2 ^>> 12ul)); // 64
  upd s 9ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b2 ^>> 20ul)) 
			       (Int.Cast.uint64_to_uint8 (b3 ^<< 6ul))); // 72
  upd s 10ul (Int.Cast.uint64_to_uint8 (b3 ^>> 2ul)); // 80 
  upd s 11ul (Int.Cast.uint64_to_uint8 (b3 ^>> 10ul)); // 88
  let h = HST.get() in
  cut (Buffer.live h s /\ modifies_1 s h0 h); 
  upd s 12ul (Int.Cast.uint64_to_uint8 (b3 ^>> 18ul)); // 96
  upd s 13ul (Int.Cast.uint64_to_uint8 (b4)); // 104
  upd s 14ul (Int.Cast.uint64_to_uint8 (b4 ^>> 8ul)); // 112 
  upd s 15ul (Int.Cast.uint64_to_uint8 (b4 ^>> 16ul)); // 120 
  ()

let uint32_of_sbytes (s:bytes{length s >= 4}) : STL u32
  (requires (fun h -> Buffer.live h s))
  (ensures (fun h0 b h1 -> h0 == h1 ))
  = let s0 = index s 0ul in
    let s0 = Int.Cast.uint8_to_uint32 s0 in
    let s1 = index s 1ul in
    let s1 = Int.Cast.uint8_to_uint32 s1 in
    let s2 = index s 2ul in
    let s2 = Int.Cast.uint8_to_uint32 s2 in
    let s3 = index s 3ul in
    let s3 = Int.Cast.uint8_to_uint32 s3 in
    (s0 ^|^ (s1 |<< 8ul) ^|^ (s2 |<< 16ul) ^|^ (s3 |<< 24ul))

(* Bytes to bigint deserializing functions *)
val le_bytes_to_num: b:bigint -> s:bytes{length s = 16 /\ disjoint b s} -> ST unit
  (requires (fun h -> live h b /\ Buffer.live h s))
  (ensures (fun h0 _ h1 -> norm h1 b /\ modifies_1 b h0 h1  /\ v (get h1 b 4) < pow2 24))
let le_bytes_to_num b s =
  admit(); // TODO
  (* IntLibLemmas.pow2_increases 63 26; *)
  (* IntLibLemmas.pow2_increases 63 32; *)
  (* IntLibLemmas.pow2_increases 26 24; *)
  let mask_26 = U64.sub (1UL ^<< 26ul) 1UL in 
  (* cut (v mask_26 = v one * pow2 26 - v one /\ v one = 1);  *)
  cut (v mask_26 = pow2 26 - 1); 
  let s0 = sub s 0ul  4ul in
  let s1 = sub s 4ul  4ul in
  let s2 = sub s 8ul  4ul in
  let s3 = sub s 12ul 4ul in
  let n0 =  (uint32_of_sbytes s0) in 
  let n1 =  (uint32_of_sbytes s1) in
  let n2 =  (uint32_of_sbytes s2) in
  let n3 =  (uint32_of_sbytes s3) in 
  let n0 = Int.Cast.uint32_to_uint64 n0 in
  let n1 = Int.Cast.uint32_to_uint64 n1 in
  let n2 = Int.Cast.uint32_to_uint64 n2 in
  let n3 = Int.Cast.uint32_to_uint64 n3 in
  (* ulogand_lemma_4 #63 n0 26 mask_26; *)
  (* ulogand_lemma_4 #63 (n1 ^<< 6) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n2 ^<< 12) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n3 ^<< 18) 26 mask_26;   *)
  aux_lemma n0 n1 26; 
  aux_lemma n1 n2 20;
  aux_lemma n2 n3 14;  
  aux_lemma_1 n3; 
  let n0' = n0 ^& mask_26 in
  let n1' = (n0 ^>> 26ul) +^ ((n1 ^<< 6ul) ^& mask_26) in 
  let n2' = (n1 ^>> 20ul) +^ ((n2 ^<< 12ul) ^& mask_26) in
  let n3' = (n2 ^>> 14ul) +^ ((n3 ^<< 18ul) ^& mask_26) in 
  let n4' = (n3 ^>> 8ul) in 
  upd b 0ul n0'; 
  upd b 1ul n1';
  upd b 2ul n2'; 
  upd b 3ul n3';
  upd b 4ul n4';
  ()

(* Runs "Acc = ((Acc+block)*r) % p." *)
val add_and_multiply: acc:bigint -> block:bigint{disjoint acc block} -> r:bigint{disjoint acc r /\ disjoint block r} -> ST unit
  (requires (fun h -> norm h acc /\ norm h block /\ norm h r))
  (ensures (fun h0 _ h1 -> norm h0 acc /\ norm h0 block /\ norm h0 r /\ norm h1 acc
    /\ modifies_1 acc h0 h1
    /\ eval h1 acc norm_length % reveal prime = 
    ((eval h0 acc norm_length + eval h0 block norm_length) * eval h0 r norm_length) % reveal prime))
let add_and_multiply acc block r =
  let h0 = HST.get() in
  fsum' acc block; 
  let h1 = HST.get() in
  let tmp = create 0UL (U32.mul 2ul nlength-|1ul) in 
  let h2 = HST.get() in 
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) = v (get h1 acc i));
  cut (forall (i:nat). {:pattern (v (get h1 acc i))} i < norm_length ==> v (get h1 acc i) = v (get h0 acc (i+0)) + v (get h0 block (i+0)));
  cut (forall (i:nat). {:pattern (v (get h0 acc i))} i < norm_length ==> v (get h0 acc i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h0 block i))} i < norm_length ==> v (get h0 block i) < pow2 26);
  (* IntLibLemmas.pow2_doubles 26; *)
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) < pow2 27);
  cut (bound27 h2 acc); 
  (* eq_lemma h0 h2 r (only acc);  *)
  cut (null h2 tmp); 
  multiplication tmp acc r; 
  let h3 = HST.get() in
  satisfies_constraints_after_multiplication h3 tmp;
  modulo tmp; 
  let h4 = HST.get() in
  blit tmp 0ul acc 0ul nlength;
  let h5 = HST.get() in
  cut (modifies_1 acc h0 h5); 
  cut (forall (i:nat). {:pattern (v (get h5 acc i))} i < norm_length ==> v (get h5 acc (0+i)) = v (get h4 tmp (0+i))); 
  cut (norm h5 acc); 
  eval_eq_lemma h4 h5 tmp acc norm_length;
  eval_eq_lemma h1 h2 acc acc norm_length;
  eval_eq_lemma h0 h2 r r norm_length;
  ()

val clamp: r:bytes{length r = 16} -> ST unit
  (requires (fun h -> Buffer.live h r))
  (ensures (fun h0 _ h1 -> Buffer.live h1 r /\ modifies_1 r h0 h1))
let clamp r =
  let mask_15 = 15uy in
  let mask_252 = 252uy in
  upd r 3ul  (U8.op_Amp_Hat (index r 3ul ) mask_15);
  upd r 7ul  (U8.op_Amp_Hat (index r 7ul ) mask_15);
  upd r 11ul (U8.op_Amp_Hat (index r 11ul) mask_15);
  upd r 15ul (U8.op_Amp_Hat (index r 15ul) mask_15);
  upd r 4ul  (U8.op_Amp_Hat (index r 4ul ) mask_252);
  upd r 8ul  (U8.op_Amp_Hat (index r 8ul ) mask_252);
  upd r 12ul (U8.op_Amp_Hat (index r 12ul) mask_252);
  ()

#reset-options "--z3timeout 20"

val poly1305_step: msg:bytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> ctr:u32{length msg >= 16 * w ctr} ->
  STL unit
    (requires (fun h -> Buffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> Buffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_1 acc h0 h1))
let rec poly1305_step msg acc r ctr =
  let h0 = HST.get() in
  if U32.eq ctr 0ul then ()
  else begin
    let n = sub msg 0ul 16ul in
    let msg = offset msg 16ul in
    //    let n, msg = SBytes.split msg 16 in 
    let h = HST.get() in
    let block = create 0UL nlength in 
    let h' = HST.get() in
    le_bytes_to_num block n; 
    let b4 = index block 4ul in
    (* IntLibLemmas.pow2_doubles 24; IntLibLemmas.pow2_increases 26 25; *)
    (* IntLibLemmas.pow2_increases 63 26;  *)
    upd block 4ul (b4 +^ (1UL ^<< 24ul)); 
    let h1 = HST.get() in
    (* eq_lemma h0 h1 r (empty);  *)
    (* eq_lemma h0 h1 acc empty; *)
    add_and_multiply acc block r; 
    let h2 = HST.get() in 
    disjoint_only_lemma msg acc; 
    (* eq_lemma h1 h2 r (only acc);  *)
    (* eq_lemma h h2 msg (only acc);  *)
    cut (modifies_1 acc h0 h2); 
    (* aux_lemma_2 acc; *)
    cut (modifies_1 acc h0 h2); 
    (* aux_lemma_3 h0 h2 acc; *)
    cut (Buffer.live h2 msg); 
    poly1305_step msg acc r (ctr-|1ul);
    ()
  end

#reset-options "--z3timeout 100"

val poly1305_last: msg:bytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> len:u32{w len <= length msg} ->
  ST unit
    (requires (fun h -> Buffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> Buffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_1 acc h0 h1))
let poly1305_last msg acc r len =
  let h0 = HST.get() in
  let l = U32.rem len 16ul in
  if U32.eq l 0ul then ()
  else (
    let n = create 0uy 16ul in
    blit msg (len -| l) n 0ul l; 
    upd n l 1uy;
    let h1 = HST.get() in
    let block = create 0UL nlength in 
    let h2 = HST.get() in
    le_bytes_to_num block n; 
    let b4 = index block 4ul in
    (* IntLibLemmas.pow2_doubles 24; IntLibLemmas.pow2_increases 26 25; *)
    (* IntLibLemmas.pow2_increases 63 26;  *)
    let h3 = HST.get() in
    (* eq_lemma h0 h3 r (empty);  *)
    (* eq_lemma h0 h3 acc empty;      *)
    add_and_multiply acc block r;
    let h4 = HST.get() in 
    disjoint_only_lemma msg acc; 
    (* eq_lemma h3 h4 r (only acc);  *)
    (* eq_lemma h1 h4 msg (only acc);  *)
    (* aux_lemma_2 acc; *)
    (* aux_lemma_3 h0 h4 acc; *)
    () )

val poly1305_mac: hash:bytes{length hash >= 16} -> msg:bytes{disjoint hash msg} -> 
  len:u32{w len <= length msg} -> key:bytes{length key = 32 /\ disjoint msg key /\ disjoint hash key} -> 
  STL unit
    (requires (fun h -> Buffer.live h msg /\ Buffer.live h key /\ Buffer.live h hash))
    (ensures (fun h0 _ h1 -> Buffer.live h1 hash /\ modifies_1 hash h0 h1))
let poly1305_mac hash msg len key =
  let h0 = HST.get() in
  let r' = sub key 0ul 16ul in
  let s = sub key 16ul 16ul in
  let r = create 0uy 16ul in
  blit r' 0ul r 0ul 16ul;
  let h0' = HST.get() in
  clamp r; 
  let h0'' = HST.get() in
  let bigint_r = create 0UL nlength in
  let bigint_s = create 0UL nlength in 
  le_bytes_to_num bigint_r r; 
  let h1 = HST.get() in
  disjoint_only_lemma s r; 
  le_bytes_to_num bigint_s s; 
  let h2 = HST.get() in
  cut (modifies_1 r h0'' h2); 
  let acc = create 0UL nlength in 
  let h2' = HST.get() in
  let ctr = U32.div len 16ul in
  let rest = U32.rem len 16ul in 
  (* eq_lemma h1 h2' bigint_r (only bigint_s);  *)
  disjoint_only_lemma bigint_r bigint_s;
  disjoint_only_lemma msg bigint_s;
  assume (norm h2' bigint_r);  // TODO
  assume (Buffer.live h0' msg); // TODO
  disjoint_only_lemma msg r; 
  cut (Buffer.live h0'' msg); 
  poly1305_step msg acc bigint_r ctr; 
  let h3 = HST.get() in
  poly1305_last msg acc bigint_r len;
  let h3' = HST.get() in
  (* eq_lemma h2 h3' bigint_s empty;  *)
  fsum' acc bigint_s; 
  let h4 = HST.get() in
  (* IntLibLemmas.pow2_doubles 26; *)
  (* IntLibLemmas.pow2_increases 62 27;  *)
  cut (forall (i:nat). {:pattern (v (get h3' acc i))} i < norm_length ==> v (get h3' acc i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h3' bigint_s i))} i < norm_length ==> v (get h3' bigint_s i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) = v (get h3' acc (i+0)) + v (get h3' bigint_s (i+0))); 
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) < pow2 27);
  cut (forall (i:nat). {:pattern (v (get h4 acc i))} i < norm_length ==> v (get h4 acc i) < pow2 63);
  freduce_coefficients acc; 
  let h45 = HST.get() in
  finalize acc;
  disjoint_only_lemma hash r;  
  let h5 = HST.get() in
  disjoint_only_lemma hash bigint_r;  
  disjoint_only_lemma hash bigint_s;  
  disjoint_only_lemma hash acc;  
  cut (Buffer.live h5 hash); 
  num_to_le_bytes hash acc; 
  let h6 = HST.get() in
  cut (modifies_1 hash h0 h6);
  ()
