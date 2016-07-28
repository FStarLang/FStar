(* Implementation of Poly1305 based on the rfc7539 *)
module Poly.Poly1305_wip

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

(****************************************)
(*    Auxiliary lemmas and functions    *)
(****************************************)
let op_Hat_Bar_Hat = UInt32.logor
let op_Bar_Less_Less = UInt32.shift_left

open FStar.Int.Cast

assume MaxU8: pow2 8 = 256
assume MaxU32: pow2 32 = 4294967296

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
  Math.Lib.pow2_exp_lemma 5 53;
  Math.Lib.pow2_increases_lemma 63 58;
  ()

assume val aux_lemma': a:nat -> n:nat{n <= 32} -> Lemma (requires True) (ensures ((((a * pow2 (32 - n)) % pow2 63) % pow2 26) % pow2 (32 - n) = 0 ))
(* let aux_lemma' a n =  *)
(*   if 32-n > 26 then ( *)
(*     Math.Lib.pow2_exp_lemma (32-n-26) 26; *)
(*     IntLibLemmas.modulo_lemma (a * pow2 (32-n-26)) (pow2 26) ) *)
(*   else if 32 - n = 26 then  *)
(*     IntLibLemmas.modulo_lemma a (pow2 26) *)
(*   else () *)

assume val aux_lemma: x:u64{v x < pow2 32} -> y:u64{v y < pow2 32} -> n:nat{n >= 7 /\ n < 32} -> Lemma
  (requires (True))
  (ensures (Math.Lib.div (v x) (pow2 n) + (((v y * pow2 (32 - n)) % pow2 63) % pow2 26) < pow2 26)) 
(* let aux_lemma x y n = *)
  (* IntLibLemmas.div_pow2_inequality (v x) 32; *)
(*   Math.Lib.pow2_increases_lemma 26 (32-n); *)
(*   aux_lemma' (v y) n; *)
(*   let a = Math.Lib.div (v x) (pow2 n) in *)
(*   let b = ((v y * pow2 (32 - n)) % pow2 63) % pow2 26 in *)
(*   let n1 = 26 in *)
(*   let n2 = 32 - n in  *)
  (* IntLibLemmas.div_positive (v x) (pow2 n);  *)
  (* IntLibLemmas.pow2_disjoint_ranges a b n1 n2; *)
(*   () *)

assume val aux_lemma_1: x:u64{v x < pow2 32} -> Lemma (requires (True)) (ensures (v (x ^>> 8ul) < pow2 24)) 
(* let aux_lemma_1 x =  *)
(*   (\* IntLibLemmas.div_pow2_inequality (v x) 32; *\) *)
(*   () *)
  

assume val aux_lemma_2: b:bigint -> Lemma (requires (True)) (ensures ((arefs (only b)) = !{as_ref b}))
(* let aux_lemma_2 b =  *)
(*   FStar.Set.lemma_equal_intro (arefs (only b)) !{content b}; *)
(*   cut (True /\ arefs (only b) = !{content b}) *)

(* assume val aux_lemma_3: h0:heap -> h1:heap -> b:bigint -> Lemma (requires (modifies_1 (arefs (only b)) h0 h1)) *)
(*   (ensures (modifies !{content b} h0 h1)) *)
(* let aux_lemma_3 h0 h1 b =  *)
(*   aux_lemma_2 b; () *)


val uint32_of_bytes: b:bytes{length b >= 4} -> STL u32
  (requires (fun h -> Buffer.live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ Buffer.live h0 b))
let uint32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = (index b 0ul) in
  let b1 = (index b 1ul) in
  let b2 = (index b 2ul) in
  let b3 = (index b 3ul) in
  let r = UInt32.add_mod (UInt32.add_mod (UInt32.add_mod (UInt32.op_Less_Less_Hat (uint8_to_uint32 b3) 24ul)
							 (UInt32.op_Less_Less_Hat (uint8_to_uint32 b2) 16ul))
					 (UInt32.op_Less_Less_Hat (uint8_to_uint32 b1) 8ul))
			 (uint8_to_uint32 b0) in
  r
(****************************************)


(** ************************************ **)
(**             Poly1305 code            **)
(** ************************************ **)

(* Bigint to bytes serializing function *)
val num_to_le_bytes: s:bytes{length s >= 16} -> b:bigint{disjoint b s} -> STL unit
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

(* Bytes to bigint deserializing functions *)
val le_bytes_to_num: b:bigint -> s:bytes{length s = 16 /\ disjoint b s} -> STL unit
  (requires (fun h -> live h b /\ Buffer.live h s))
  (ensures (fun h0 _ h1 -> norm h1 b /\ modifies_1 b h0 h1  /\ v (get h1 b 4) < pow2 24))
let le_bytes_to_num b s =
  Math.Lib.pow2_increases_lemma 64 26;
  Math.Lib.pow2_increases_lemma 64 32;
  Math.Lib.pow2_increases_lemma 26 24;
  let mask_26 = U64.sub (1UL ^<< 26ul) 1UL in 
  cut (v mask_26 = v 1UL * pow2 26 - v 1UL /\ v 1UL = 1);
  cut (v mask_26 = pow2 26 - 1);
  let s0 = sub s 0ul  4ul in
  let s1 = sub s 4ul  4ul in
  let s2 = sub s 8ul  4ul in
  let s3 = sub s 12ul 4ul in
  let n0 = (uint32_of_bytes s0) in 
  let n1 = (uint32_of_bytes s1) in
  let n2 = (uint32_of_bytes s2) in
  let n3 = (uint32_of_bytes s3) in 
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
  let n1' = (n0 ^>> 26ul) |^ ((n1 ^<< 6ul) ^& mask_26) in 
  let n2' = (n1 ^>> 20ul) |^ ((n2 ^<< 12ul) ^& mask_26) in
  let n3' = (n2 ^>> 14ul) |^ ((n3 ^<< 18ul) ^& mask_26) in 
  let n4' = (n3 ^>> 8ul) in 
  upd b 0ul n0'; 
  upd b 1ul n1';
  upd b 2ul n2'; 
  upd b 3ul n3';
  upd b 4ul n4';
  let h = HST.get() in
  assume (v (get h b 4) < pow2 24);
  assume (norm h b)

(* Clamps the key, see RFC *)
val clamp: r:bytes{length r = 16} -> STL unit
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

(* Runs "Acc = ((Acc+block)*r) % p." on the accumulator, the well formatted block of the message 
   and the clamped part of the key *)
val add_and_multiply: acc:bigint -> block:bigint{disjoint acc block} -> r:bigint{disjoint acc r /\ disjoint block r} -> STL unit
  (requires (fun h -> norm h acc /\ norm h block /\ norm h r))
  (ensures (fun h0 _ h1 -> norm h0 acc /\ norm h0 block /\ norm h0 r /\ norm h1 acc
    /\ modifies_1 acc h0 h1
    /\ eval h1 acc norm_length % reveal prime = 
    ((eval h0 acc norm_length + eval h0 block norm_length) * eval h0 r norm_length) % reveal prime))
let add_and_multiply acc block r =
  let hinit = HST.get() in
  push_frame();
  let h0 = HST.get() in
  eq_lemma_fresh hinit h0 acc;
  eq_lemma_fresh hinit h0 block;
  eq_lemma_fresh hinit h0 r;
  fsum' acc block;
  let h1 = HST.get() in
  assert(modifies_1 acc h0 h1);
  let tmp = create 0UL (U32.mul 2ul nlength-|1ul) in
  let h2 = HST.get() in
  assert (modifies_0 h1 h2);
  lemma_modifies_1_0 acc h0 h1 h2;
  assert(modifies_2_1 acc h0 h2); (* WIP *)
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) = v (get h1 acc i));
  cut (forall (i:nat). {:pattern (v (get h1 acc i))} i < norm_length ==> v (get h1 acc i) = v (get h0 acc (i+0)) + v (get h0 block (i+0)));
  cut (forall (i:nat). {:pattern (v (get h0 acc i))} i < norm_length ==> v (get h0 acc i) < pow2 26); 
  cut (forall (i:nat). {:pattern (v (get h0 block i))} i < norm_length ==> v (get h0 block i) < pow2 26);
  Math.Lemmas.pow2_double_sum 26;
  cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) < pow2 27);
  cut (bound27 h2 acc); 
  eq_lemma_1 h0 h2 acc r;
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
  pop_frame();
  let hfin = HST.get() in
  admit()


(* Initialization function:
   - zeros the accumulator
   - clamp the first half of the key
   - stores the key well formatted in 'r' and 's' *)
val poly1305_init: acc:bigint -> bigint_r:bigint -> bigint_s:bigint -> key:bytes -> STL unit
  (requires (fun h -> True))
  (ensures  (fun h0 _ h1 -> True))
let poly1305_init acc bigint_r bigint_s key =
  push_frame();
  (* Zero the accumulator *)
  upd acc 0ul 0UL;
  upd acc 1ul 0UL;
  upd acc 2ul 0UL;
  upd acc 3ul 0UL;
  upd acc 4ul 0UL;
  (* Format the keys *)
  let r' = sub key 0ul 16ul in
  let s = sub key 16ul 16ul in
  let r = create 0uy 16ul in // Needs to be done on bigint_r instead to avoid copies
  blit r' 0ul r 0ul 16ul;
  clamp r; 
  le_bytes_to_num bigint_r r;
  le_bytes_to_num bigint_s s;
  pop_frame()

(* Update function:
   - takes a message block, appends '1' to it and formats it to bigint format    
   - runs acc = ((acc*block)+r) % p *)
val poly1305_update: msg:bytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> STL unit
    (requires (fun h -> Buffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> Buffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_1 acc h0 h1))
let poly1305_update msg acc r =
  let hinit = HST.get() in
  push_frame();
  let h0 = HST.get() in
  let n = sub msg 0ul 16ul in
  let msg = offset msg 16ul in
  let h = HST.get() in
  let block = create 0UL nlength in 
  let h' = HST.get() in
  le_bytes_to_num block n; 
  let b4 = index block 4ul in
  Math.Lemmas.pow2_double_sum 24; 
  Math.Lib.pow2_increases_lemma 26 25;
  Math.Lib.pow2_increases_lemma 64 26;
  upd block 4ul (b4 +^ (1UL ^<< 24ul)); 
  let h1 = HST.get() in
  eq_lemma_0 h0 h1 r;
  eq_lemma_0 h0 h1 acc;
  add_and_multiply acc block r; 
  let h2 = HST.get() in 
  disjoint_only_lemma msg acc; 
  eq_lemma_1 h1 h2 acc r;
  eq_lemma_1 h h2 acc msg;
  cut (modifies_1 acc h0 h2); 
  aux_lemma_2 acc;
  cut (modifies_1 acc h0 h2); 
  cut (Buffer.live h2 msg); 
  pop_frame();
  let hfin = HST.get() in
  ()

(* Loop over Poly1305_upadte *)
val poly1305_step: msg:bytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> ctr:u32{length msg >= 16 * w ctr} ->
  STL unit
    (requires (fun h -> Buffer.live h msg /\ norm h acc /\ norm h bigint_r))
    (ensures (fun h0 _ h1 -> Buffer.live h1 msg /\ norm h1 acc /\ norm h1 bigint_r
      /\ modifies_1 acc h0 h1))
let rec poly1305_step msg acc r ctr =
  if U32.eq ctr 0ul then ()
  else begin
    poly1305_update msg acc r;
    let msg = offset msg 16ul in
    poly1305_step msg acc r (ctr-|1ul)
  end

(* Performs the last step if there is an incomplete block *)
val poly1305_last: msg:bytes -> acc:bigint{disjoint msg acc} -> 
  bigint_r:bigint{disjoint msg bigint_r /\ disjoint acc bigint_r} -> len:u32{w len <= length msg} ->
  STL unit
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
    Math.Lemmas.pow2_double_sum 24; Math.Lib.pow2_increases_lemma 26 25;
    Math.Lib.pow2_increases_lemma 64 26;
    let h3 = HST.get() in
    eq_lemma_0 h0 h3 r;
    eq_lemma_0 h0 h3 acc;
    add_and_multiply acc block r;
    let h4 = HST.get() in 
    disjoint_only_lemma msg acc; 
    eq_lemma_1 h3 h4 acc r;
    eq_lemma_1 h1 h4 acc msg;
    aux_lemma_2 acc;
    () )

(* Finish function, with final accumulator value *)
val poly1305_finish: hash:bytes -> acc:bigint -> bigint_s:bigint -> STL unit
  (requires (fun h -> Buffer.live h hash /\ live h acc /\ live h bigint_s 
    /\ disjoint hash acc /\ disjoint hash bigint_s /\ disjoint acc bigint_s))
  (ensures  (fun h0 _ h1 -> modifies_2 hash acc h0 h1 /\ live h1 acc /\ Buffer.live h1 hash))
let poly1305_finish hash acc bigint_s =
  fsum' acc bigint_s; 
  freduce_coefficients acc;
  finalize acc;
  num_to_le_bytes hash acc

val poly1305_mac: hash:bytes{length hash >= 16} -> msg:bytes{disjoint hash msg} -> 
  len:u32{w len <= length msg} -> key:bytes{length key = 32 /\ disjoint msg key /\ disjoint hash key} -> 
  STL unit
    (requires (fun h -> Buffer.live h msg /\ Buffer.live h key /\ Buffer.live h hash))
    (ensures (fun h0 _ h1 -> Buffer.live h1 hash /\ modifies_1 hash h0 h1))
let poly1305_mac hash msg len key =
  push_frame();
  (* Create buffers for the 2 parts of the key and the accumulator *)
  let bigint_r = create 0UL nlength in
  let bigint_s = create 0UL nlength in 
  let acc      = create 0UL nlength in
  (* Initializes the accumulator and the keys values *)
  poly1305_init acc bigint_r bigint_s key;
  (* Compute the number of 'plain' blocks *)
  let ctr = U32.div len 16ul in
  let rest = U32.rem len 16ul in 
  (* Run the poly1305_update function ctr times *)
  poly1305_step msg acc bigint_r ctr;
  poly1305_last msg acc bigint_r rest;
  (* Finish *)
  poly1305_finish hash acc bigint_s;
  pop_frame()
