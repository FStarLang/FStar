(* Implementation of Poly1305 based on the rfc7539 *)
module Crypto.Symmetric.Poly1305

open FStar.Mul
open FStar.Ghost
open FStar.Seq
(** Machine integers *)
open FStar.UInt8
open FStar.UInt64
open FStar.Int.Cast
(** Effects and memory layout *)
open FStar.HyperStack
open FStar.HST
(** Buffers *)
open FStar.Buffer
(** Mathematical definitions *)
open Math.Axioms
open Math.Lib
open Math.Lemmas
(** Helper functions for buffers *)
open Buffer.Utils

open Crypto.Symmetric.Poly1305.Parameters
open Crypto.Symmetric.Poly1305.Bigint
open Crypto.Symmetric.Poly1305.Bignum
open Crypto.Symmetric.Poly1305.Lemmas

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HS = FStar.HyperStack

#set-options "--lax"

(* Poly1305 prime *)
let p_1305 () = reveal prime


(** *********************************************)
(**            Type definitions                 *)
(** *********************************************)
type elem = n:nat{n < p_1305()} // Element of the group Z/p_1305.Z
type elemB = bigint        // Mutable big integer representation (5 64-bit limbs)

type word = b:seq byte{Seq.length b <= 16} // Pure representation of the 16-bit words on which 
					  // poly1305 computation is run
type wordB = b:bytes{length b <= 16}  // Concrete (mutable) representation of those words

type log = seq (w:word{Seq.length w = 16})


(** *********************************************)
(**            Group operators                  *)
(** *********************************************)
val group_add: elem -> elem -> GTot elem
let group_add a b = (a + b) % p_1305 ()
val group_mul: elem -> elem -> GTot elem
let group_mul a b = (a * b) % p_1305 ()
(* Infix operators for readability *)
let op_Plus_At = group_add
let op_Star_At = group_mul


(** *********************************************)
(**  Mappings from stateful types to pure types *)
(** *********************************************)
(* From the current memory state, returns the word corresponding to a wordB *)
let sel_word (h:mem) (b:wordB{live h b}) : GTot word
  = as_seq h b
assume val esel_word:h:mem -> b:wordB{live h b} -> Tot (erased word)

(* From the current memory state, returns the group element corresponding to a elemB *)
let sel_elem (h:mem) (b:elemB{live h b}) : GTot elem
  = eval h b norm_length % p_1305 ()

(* From the current memory state, returns the integer corresponding to a elemB, (before 
   computing the modulo) *)
let sel_int (h:mem) (b:elemB{live h b}) : GTot elem
  = eval h b norm_length

(* Little endian integer value of a sequence of bytes *)
let rec little_endian (b:word) : GTot (n:nat{n < pow2 128}) (decreases (Seq.length b))
  = if Seq.length b = 0 then 0
    else U8.v (Seq.index b (Seq.length b - 1)) + 
	 pow2 8 * little_endian (Seq.slice b 1 (Seq.length b))


(** *********************************************)
(**        Poly1305 functional invariant        *)
(** *********************************************)
(* TODO: chose a definition *)
(* First possible definition *)
val poly: vs:seq (w:word{Seq.length w = 16}) -> r:elem -> GTot (a:elem)
let rec poly vs r =
  if Seq.length vs = 0 then 0
  else (pow2 128 +@ little_endian (Seq.index vs 0)) *@ r +@ poly (Seq.slice vs 1 (Seq.length vs)) r 
(* Second possible definition *)
val poly': vs:seq (w:word{Seq.length w = 16}) -> r:elem -> GTot (a:elem)
let rec poly' vs r =
  if Seq.length vs = 0 then 0
  else (little_endian (Seq.index vs 0 @| (Seq.create 1 1uy))) *@ r +@ poly' (Seq.slice vs 1 (Seq.length vs)) r

(** *********************************************)
(**            Encoding functions               *)
(** *********************************************)
(* Formats a wordB into an elemB *)
val toGroup: a:elemB -> b:wordB{length b = 16 /\ disjoint a b} -> STL unit
  (requires (fun h -> live h a /\ live h b))
  (ensures  (fun h0 _ h1 -> 
    live h0 b /\ // Initial post condition
    norm h1 a /\ // the elemB 'a' is in a 'workable' state
    modifies_1 a h0 h1 /\ // Only a was modified
    sel_int h1 a = little_endian (sel_word h0 b)
    ))
let toGroup b s =
  (* Math.Lib.pow2_increases_lemma 64 26; *)
  (* Math.Lib.pow2_increases_lemma 64 32; *)
  (* Math.Lib.pow2_increases_lemma 26 24; *)
  let mask_26 = U64.sub (1UL <<^ 26ul) 1UL in 
  (* cut (v mask_26 = v 1UL * pow2 26 - v 1UL /\ v 1UL = 1); *)
  (* cut (v mask_26 = pow2 26 - 1); *)
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
  (* ulogand_lemma_4 #63 (n1 <<^ 6) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n2 <<^ 12) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n3 <<^ 18) 26 mask_26;   *)
  (* aux_lemma n0 n1 26;  *)
  (* aux_lemma n1 n2 20; *)
  (* aux_lemma n2 n3 14;   *)
  (* aux_lemma_1 n3;  *)
  let n0' = n0 &^ mask_26 in
  let n1' = (n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26) in 
  let n2' = (n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26) in
  let n3' = (n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26) in 
  let n4' = (n3 >>^ 8ul) in 
  upd b 0ul n0'; 
  upd b 1ul n1';
  upd b 2ul n2'; 
  upd b 3ul n3';
  upd b 4ul n4'(* ; *)
  (* let h = HST.get() in *)
  (* assume (v (get h b 4) < pow2 24); *)
  (* assume (norm h b) *)

(* Formats a wordB into an elemB *)
val toGroup_plus_2_128: a:elemB -> b:wordB{length b = 16 /\ disjoint a b} -> STL unit
  (requires (fun h -> live h a /\ live h b))
  (ensures  (fun h0 _ h1 -> 
    live h0 b /\ // Initial post condition
    norm h1 a /\ // the elemB 'a' is in a 'workable' state
    modifies_1 a h0 h1 /\ // Only a was modified
    (* TODO: Choose between the following 2 (equivalent) formulations *)
    sel_int h1 a = little_endian (sel_word h0 b @| Seq.create 1 1uy) /\ // Expressed with sequences
    sel_int h1 a = pow2 128 + little_endian (sel_word h0 b) // Expressed arithmetically
    ))
let toGroup_plus_2_128 b s =
  (* Math.Lib.pow2_increases_lemma 64 26; *)
  (* Math.Lib.pow2_increases_lemma 64 32; *)
  (* Math.Lib.pow2_increases_lemma 26 24; *)
  let mask_26 = U64.sub (1UL <<^ 26ul) 1UL in 
  (* cut (v mask_26 = v 1UL * pow2 26 - v 1UL /\ v 1UL = 1); *)
  (* cut (v mask_26 = pow2 26 - 1); *)
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
  (* ulogand_lemma_4 #63 (n1 <<^ 6) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n2 <<^ 12) 26 mask_26;  *)
  (* ulogand_lemma_4 #63 (n3 <<^ 18) 26 mask_26;   *)
  (* aux_lemma n0 n1 26;  *)
  (* aux_lemma n1 n2 20; *)
  (* aux_lemma n2 n3 14;   *)
  (* aux_lemma_1 n3;  *)
  let n0' = n0 &^ mask_26 in
  let n1' = (n0 >>^ 26ul) |^ ((n1 <<^ 6ul) &^ mask_26) in 
  let n2' = (n1 >>^ 20ul) |^ ((n2 <<^ 12ul) &^ mask_26) in
  let n3' = (n2 >>^ 14ul) |^ ((n3 <<^ 18ul) &^ mask_26) in 
  let n4' = (n3 >>^ 8ul) +^ (1uL <<^ 24ul) in 
  upd b 0ul n0'; 
  upd b 1ul n1';
  upd b 2ul n2'; 
  upd b 3ul n3';
  upd b 4ul n4'(* ; *)
  (* let h = HST.get() in *)
  (* assume (v (get h b 4) < pow2 24); *)
  (* assume (norm h b) *)

val trunc1305: a:elemB -> b:wordB{disjoint a b} -> STL unit
  (requires (fun h -> norm h a /\ live h b))
  (ensures  (fun h0 _ h1 -> live h1 b /\ norm h0 a
    /\ modifies_1 b h0 h1
    /\ sel_elem h0 a % pow2 128 = little_endian (sel_word h1 b) ))
let trunc1305 b s =
  let h0 = HST.get() in
  (* Full reduction of b:
     - before finalization sel_int h b < pow2 130
     - alfter finalization sel_int h b = sel_elem h b *)
  finalize b;
  (* Copy of the 128 first bits of b into s *)
  let b0 = index b 0ul in
  let b1 = index b 1ul in
  let b2 = index b 2ul in
  let b3 = index b 3ul in
  let b4 = index b 4ul in
  upd s 0ul (Int.Cast.uint64_to_uint8 b0);  // 0 
  upd s 1ul (Int.Cast.uint64_to_uint8 (b0 >>^ 8ul)); //8
  upd s 2ul (Int.Cast.uint64_to_uint8 (b0 >>^ 16ul)); //16
  upd s 3ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b0 >>^ 24ul)) // 24 
			       (Int.Cast.uint64_to_uint8 (b1 <<^ 2ul))); 
  upd s 4ul (Int.Cast.uint64_to_uint8 (b1 >>^ 6ul)); // 32
  upd s 5ul (Int.Cast.uint64_to_uint8 (b1 >>^ 14ul)); // 40
  upd s 6ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b1 >>^ 22ul)) 
			       (Int.Cast.uint64_to_uint8 (b2 <<^ 4ul))); // 48
  upd s 7ul (Int.Cast.uint64_to_uint8 (b2 >>^ 4ul)); // 56
  upd s 8ul (Int.Cast.uint64_to_uint8 (b2 >>^ 12ul)); // 64
  upd s 9ul (U8.add_mod (Int.Cast.uint64_to_uint8 (b2 >>^ 20ul)) 
			       (Int.Cast.uint64_to_uint8 (b3 <<^ 6ul))); // 72
  upd s 10ul (Int.Cast.uint64_to_uint8 (b3 >>^ 2ul)); // 80 
  upd s 11ul (Int.Cast.uint64_to_uint8 (b3 >>^ 10ul)); // 88
  let h = HST.get() in
  cut (live h s /\ modifies_1 s h0 h); 
  upd s 12ul (Int.Cast.uint64_to_uint8 (b3 >>^ 18ul)); // 96
  upd s 13ul (Int.Cast.uint64_to_uint8 (b4)); // 104
  upd s 14ul (Int.Cast.uint64_to_uint8 (b4 >>^ 8ul)); // 112 
  upd s 15ul (Int.Cast.uint64_to_uint8 (b4 >>^ 16ul)); // 120 
  ()

(* Clamps the key, see RFC *)
val clamp: r:wordB{length r = 16} -> STL unit
  (requires (fun h -> live h r))
  (ensures (fun h0 _ h1 -> live h1 r /\ modifies_1 r h0 h1))
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


(** *********************************************)
(**          Encoding-related lemmas            *)
(** *********************************************)
val lemma_little_endian_is_injective: b:word -> b':word -> Lemma
  (requires (little_endian b = little_endian b'))
  (ensures  (b == b'))
let lemma_little_endian_is_injective b b' =
  (* TODO *)
  admit()

val lemma_toGroup_is_injective: ha:mem -> hb:mem -> a:elemB -> b:elemB ->
  Lemma (requires (norm ha a /\ norm hb b /\ sel_int ha a = sel_int hb b))
	(ensures  (as_seq ha a == as_seq hb b))
let lemma_toGroup_is_injective ha hb a b =
  (* TODO *)
  admit()


(** *********************************************)
(**        Polynomial computation step          *)
(** *********************************************)
(* Runs "Acc = ((Acc+block)*r) % p." on the accumulator, the well formatted block of the message 
   and the clamped part of the key *)
val add_and_multiply: acc:elemB -> block:elemB{disjoint acc block} -> r:elemB{disjoint acc r /\ disjoint block r} -> STL unit
  (requires (fun h -> norm h acc /\ norm h block /\ norm h r))
  (ensures (fun h0 _ h1 -> norm h0 acc /\ norm h0 block /\ norm h0 r 
    /\ norm h1 acc // the accumulation is back in a workable states
    /\ modifies_1 acc h0 h1 // It was the only thing modified
    /\ sel_elem h1 acc = (sel_elem h0 acc +@ sel_elem h0 block) *@ sel_elem h0 r // Functional
						// specification of the operation at that step
    ))
let add_and_multiply acc block r =
  (* let hinit = HST.get() in *)
  push_frame();
  (* let h0 = HST.get() in *)
  (* eq_lemma_fresh hinit h0 acc; *)
  (* eq_lemma_fresh hinit h0 block; *)
  (* eq_lemma_fresh hinit h0 r; *)
  fsum' acc block;
  (* let h1 = HST.get() in *)
  (* assert(modifies_1 acc h0 h1); *)
  let tmp = create 0UL (U32.mul 2ul nlength-|1ul) in
  (* let h2 = HST.get() in *)
  (* assert (modifies_0 h1 h2); *)
  (* lemma_modifies_1_0 acc h0 h1 h2; *)
  (* assert(modifies_2_1 acc h0 h2); (\* WIP *\) *)
  (* cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) = v (get h1 acc i)); *)
  (* cut (forall (i:nat). {:pattern (v (get h1 acc i))} i < norm_length ==> v (get h1 acc i) = v (get h0 acc (i+0)) + v (get h0 block (i+0))); *)
  (* cut (forall (i:nat). {:pattern (v (get h0 acc i))} i < norm_length ==> v (get h0 acc i) < pow2 26);  *)
  (* cut (forall (i:nat). {:pattern (v (get h0 block i))} i < norm_length ==> v (get h0 block i) < pow2 26); *)
  (* Math.Lemmas.pow2_double_sum 26; *)
  (* cut (forall (i:nat). {:pattern (v (get h2 acc i))} i < norm_length ==> v (get h2 acc i) < pow2 27); *)
  (* cut (bound27 h2 acc);  *)
  (* eq_lemma_1 h0 h2 acc r; *)
  (* cut (null h2 tmp);  *)
  multiplication tmp acc r; 
  (* let h3 = HST.get() in *)
  (* satisfies_constraints_after_multiplication h3 tmp; *)
  modulo tmp; 
  (* let h4 = HST.get() in *)
  blit tmp 0ul acc 0ul nlength;
  (* let h5 = HST.get() in *)
  (* cut (modifies_1 acc h0 h5);  *)
  (* cut (forall (i:nat). {:pattern (v (get h5 acc i))} i < norm_length ==> v (get h5 acc (0+i)) = v (get h4 tmp (0+i)));  *)
  (* cut (norm h5 acc);  *)
  (* eval_eq_lemma h4 h5 tmp acc norm_length; *)
  (* eval_eq_lemma h1 h2 acc acc norm_length; *)
  (* eval_eq_lemma h0 h2 r r norm_length; *)
  pop_frame()(* ; *)
  (* let hfin = HST.get() in *)
  (* admit() *)

(* Sets the accumulator to the value '0' *)
val zeroB: a:elemB -> STL unit
  (requires (fun h -> live h a))
  (ensures  (fun h0 _ h1 -> norm h1 a /\ modifies_1 a h0 h1 
    /\ sel_elem h1 a = 0 ))
let zeroB a =
  upd a 0ul 0UL;
  upd a 1ul 0UL;
  upd a 2ul 0UL;
  upd a 3ul 0UL;
  upd a 4ul 0UL

(* Initialization function:
   - zeros the accumulator
   - clamp the first half of the key
   - stores the well-formatted first half of the key in 'r' *)
val poly1305_init: acc:elemB -> // Accumulator
  r:elemB{disjoint acc r} -> // First half of the key, on which the polynome is evaluated
  key:bytes{length key >= 32 /\ disjoint acc key /\ disjoint r key} ->
  STL (erased log)
  (requires (fun h -> live h acc /\ live h r /\ live h key))
  (ensures  (fun h0 log h1 -> norm h1 acc /\ norm h1 r /\ modifies_2 acc r h0 h1
    /\ reveal log = (Seq.createEmpty #word)
    /\ sel_elem h1 acc = poly (reveal log) (sel_elem h1 r) // Poly invariant
    ))
let poly1305_init acc r key =
  push_frame();
  (* Zero the accumulator *)
  zeroB acc;
  (* Format the keys *)
  let r' = sub key 0ul 16ul in
  (* Make a copy of the first half of the key to clamp it *)
  let r'' = create 0uy 16ul in
  blit r' 0ul r'' 0ul 16ul;
  (* Clamp r *)
  clamp r'';
  (* Format r to elemB *)
  toGroup r r'';
  pop_frame();
  hide (Seq.createEmpty #word)

val update_log: 
  l:erased log -> 
  msg:erased word{Seq.length (reveal msg) = 16} -> 
  Tot (l':erased log{reveal l' == (reveal l @| Seq.create 1 (reveal msg))})
let update_log l msg =
  elift2 (fun l msg ->  (l @| Seq.create 1 msg)) l msg

(* Update function:
   - takes a ghost log
   - takes a message block, appends '1' to it and formats it to bigint format    
   - runs acc = ((acc*block)+r) % p *)
val poly1305_update: 
  current_log:erased log -> 
  msg:wordB ->
  acc:elemB{disjoint msg acc} -> 
  r:elemB{disjoint msg r /\ disjoint acc r} -> STL (erased log)
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r
      /\ poly (reveal current_log) (sel_elem h r) = sel_elem h acc // Incremental step of poly 
      ))
    (ensures (fun h0 updated_log h1 -> norm h1 acc /\ norm h0 r
      /\ modifies_1 acc h0 h1
      /\ reveal updated_log = (reveal current_log) @| Seq.create 1 (sel_word h1 msg)
      /\ sel_elem h1 acc = poly (reveal updated_log) (sel_elem h0 r) ))
let poly1305_update log msg acc r =
  push_frame();
  let n = sub msg 0ul 16ul in // Select the message to update
  (* TODO: pass the buffer for the block rather that create a fresh one to avoid 
     too many copies *)
  let block = create 0UL nlength in 
  (* let h' = HST.get() in *)
  toGroup_plus_2_128 block n;
  add_and_multiply acc block r;
  let h = HST.get() in
  let msg = esel_word h msg in
  let updated_log = update_log log msg in
  pop_frame();
  updated_log

(* Loop over Poly1305_update *)
val poly1305_loop: current_log:erased log -> msg:bytes -> acc:elemB{disjoint msg acc} -> 
  r:elemB{disjoint msg r /\ disjoint acc r} -> ctr:u32{length msg >= 16 * w ctr} ->
  STL (erased log)
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r))
    (ensures (fun h0 _ h1 -> live h1 msg /\ norm h1 acc /\ norm h1 r
      /\ modifies_1 acc h0 h1))
let rec poly1305_loop log msg acc r ctr =
  if U32.eq ctr 0ul then log
  else begin
    let updated_log = poly1305_update log msg acc r in
    let msg = offset msg 16ul in
    let h = HST.get() in
    let word = esel_word h msg in
    poly1305_loop (update_log log word) msg acc r (ctr-|1ul)
  end

(* Performs the last step if there is an incomplete block *)
val poly1305_last: msg:wordB -> acc:elemB{disjoint msg acc} -> 
  r:elemB{disjoint msg r /\ disjoint acc r} -> len:u32{w len <= length msg} ->
  STL unit
    (requires (fun h -> live h msg /\ norm h acc /\ norm h r))
    (ensures (fun h0 _ h1 -> live h1 msg /\ norm h1 acc /\ norm h1 r
      /\ modifies_1 acc h0 h1))
let poly1305_last msg acc r len =
  push_frame();
  let h0 = HST.get() in
  if U32.eq len 0ul then ()
  else (    
    let n = create 0uy 16ul in
    blit msg 0ul n 0ul len;
    upd n len 1uy;
    let block = create 0UL nlength in
    toGroup block n;
    add_and_multiply acc block r);
  pop_frame()

(* TODO: certainly a more efficient, better implementation of that *)
val add_word: a:wordB{length a = 16} -> b:wordB{length b = 16} -> STL unit
  (requires (fun h -> live h a /\ live h b))
  (ensures  (fun h0 _ h1 -> live h1 a /\ modifies_1 a h0 h1
    /\ little_endian (sel_word h1 a) = 
	(little_endian (sel_word h0 a) + little_endian (sel_word h0 b)) % pow2 128 ))
let add_word a b =
  let carry = 0ul in
  let a04:u64 = let (x:u32) = uint32_of_bytes a in uint32_to_uint64 x  in
  let a48:u64 = let (x:u32) = uint32_of_bytes (offset a 4ul) in uint32_to_uint64 x in
  let a812:u64 = let (x:u32) = uint32_of_bytes (offset a 8ul) in uint32_to_uint64 x in
  let a1216:u64 = let (x:u32) = uint32_of_bytes (offset a 12ul) in uint32_to_uint64 x in
  let b04:u64 = let (x:u32) = uint32_of_bytes b in uint32_to_uint64 x  in
  let b48:u64 = let (x:u32) = uint32_of_bytes (offset b 4ul) in uint32_to_uint64 x in
  let b812:u64 = let (x:u32) = uint32_of_bytes (offset b 8ul) in uint32_to_uint64 x in
  let b1216:u64 = let (x:u32) = uint32_of_bytes (offset b 12ul) in uint32_to_uint64 x in
  let open FStar.UInt64 in
  let z0 = a04 +^ b04 in
  let z1 = a48 +^ b48 +^ (z0 >>^ 32ul) in
  let z2 = a812 +^ b812 +^ (z1 >>^ 32ul) in
  let z3 = a1216 +^ b1216 +^ (z2 >>^ 32ul) in
  bytes_of_uint32 (Buffer.sub a 0ul 4ul) (uint64_to_uint32 z0);
  bytes_of_uint32 (Buffer.sub a 4ul 4ul) (uint64_to_uint32 z1);
  bytes_of_uint32 (Buffer.sub a 8ul 4ul) (uint64_to_uint32 z2);
  bytes_of_uint32 (Buffer.sub a 12ul 4ul) (uint64_to_uint32 z3)

(* Finish function, with final accumulator value *)
val poly1305_finish: tag:wordB{length tag = 16} -> 
  acc:elemB -> 
  s:wordB -> STL unit
  (requires (fun h -> live h tag /\ live h acc /\ live h s 
    /\ disjoint tag acc /\ disjoint tag s /\ disjoint acc s))
  (ensures  (fun h0 _ h1 -> modifies_2 tag acc h0 h1 /\ live h1 acc /\ live h1 tag
    // TODO: add some functional correctness
  ))
let poly1305_finish tag acc s =  
  trunc1305 acc tag;
  add_word tag s

val poly1305_mac: tag:wordB{length tag >= 16} -> msg:bytes{disjoint tag msg} ->
  len:u32{w len <= length msg} -> key:bytes{length key = 32 /\ disjoint msg key /\ disjoint tag key} ->
  STL unit
    (requires (fun h -> live h msg /\ live h key /\ live h tag))
    (ensures (fun h0 _ h1 -> live h1 tag /\ modifies_1 tag h0 h1))
let poly1305_mac tag msg len key =
  push_frame();
  (* Create buffers for the 2 parts of the key and the accumulator *)
  let tmp = create 0UL 10ul in
  let acc = sub tmp 0ul 5ul in
  let r   = sub tmp 5ul 5ul in
  (* Initializes the accumulator and the keys values *)
  let log = poly1305_init acc r key in
  (* Compute the number of 'plain' blocks *)
  let ctr = U32.div len 16ul in
  let rest = U32.rem len 16ul in 
  (* Run the poly1305_update function ctr times *)
  let _ = poly1305_loop log msg acc r ctr in
  (* Run the poly1305_update function one more time on the incomplete block *)
  let last_block = sub msg (FStar.UInt32 (ctr *^ 16ul)) rest in
  poly1305_last last_block acc r rest;
  (* Finish *)
  poly1305_finish tag acc (sub key 16ul 16ul);
  pop_frame()
