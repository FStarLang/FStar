(* --build-config
  options:--admit_fsi FStar.Set --verify_module Chacha20 --z3timeout 50;
  other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Seq.fst FStar.SeqProperties.fst FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.Array.fst FStar.Ghost.fst axioms.fst intlib.fst lemmas.fst sint.fst FStar.UInt8.fst FStar.UInt32.fst sbuffer.fst FStar.SBytes.fst;
  --*)

module Chacha

open FStar.Ghost
open FStar.Heap
open Sint
open FStar.UInt8
open FStar.UInt32
open FStar.SBytes
open SBuffer

(** Infix operators and helping lemmas **)
val aux_lemma: #t:pos -> a:buffer t -> #t':pos -> b:buffer t' -> #t'':pos -> c:buffer t'' -> 
  Lemma (requires (Disjoint a b /\ Disjoint a c))
	(ensures (DisjointSet a (only b ++ c)))
let aux_lemma #t a #t' b #t'' c = ()

val aux_lemma': #t:pos -> a:buffer t -> #t':pos -> b:buffer t' -> 
  Lemma (requires (Disjoint a b))
	(ensures (DisjointSet a (only b)))
let aux_lemma' #t a #t' b = ()

val aux_lemma'': #t:pos -> a:buffer t -> #t':pos -> a':buffer t' -> 
  Lemma (FStar.Set.Equal (only a ++ a') (only a' ++ a))
let aux_lemma'' #t a #t' a' = ()  

val empty_lemma: #t:pos -> b:buffer t -> Lemma (FStar.Set.Equal (empty ++ b) (only b))
let empty_lemma #t b = ()

#reset-options

(* Chacha 20 code *)

val quarter_round: 
  m:uint32s{length m = 16} -> a:nat{a < 16} -> b:nat{b<16} -> c:nat{c<16} -> d:nat{d<16} -> 
  ST unit 
    (requires (fun h -> Live h m)) 
    (ensures (fun h0 _ h1 -> Live h1 m /\ Modifies (only m) h0 h1))
let quarter_round m a b c d =
  upd m a (index m a ^+ index m b); 
  upd m d (index m d ^^ index m a);
  let (tmp:uint32) = index m d in 
  upd m d (tmp <<< 16); 
  upd m c (index m c ^+ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< 12);
  upd m a (index m a ^+ index m b); 
  upd m d (index m d ^^ index m a); 
  let tmp = index m d in
  upd m d (tmp <<< 8);
  upd m c (index m c ^+ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< 7);
  ()
 
#reset-options

(* Chacha20 block function *)
val column_round: m:uint32s{length m = 16} -> ST unit
    (requires (fun h -> Live h m))
    (ensures (fun h0 _ h1 -> Live h1 m /\ Modifies (only m) h0 h1))
let column_round m =
  quarter_round m 0 4 8 12;
  quarter_round m 1 5 9 13;
  quarter_round m 2 6 10 14;
  quarter_round m 3 7 11 15;
  ()

val diagonal_round: m:uint32s{length m = 16} -> ST unit
    (requires (fun h -> Live h m))
    (ensures (fun h0 _ h1 -> Live h1 m /\ Modifies (only m) h0 h1))
let diagonal_round m =
  quarter_round m 0 5 10 15;
  quarter_round m 1 6 11 12;
  quarter_round m 2 7 8 13;
  quarter_round m 3 4 9 14;
  ()

#reset-options

val initialize_state: state:uint32s{length state = 16} -> key:sbytes{length key = 32 /\ Disjoint state key} -> counter:uint32 -> nonce:sbytes{length nonce = 12 /\ Disjoint key nonce /\ Disjoint state nonce} -> ST unit
  (requires (fun h -> Live h state /\ Live h key /\ Live h nonce))
  (ensures (fun h0 _ h1 -> Modifies (only state) h0 h1 /\ Live h1 state))
let initialize_state state key counter nonce =
  //admit();
  (* Constant part *)
  upd state 0 (of_string "0x61707865");
  upd state 1 (of_string "0x3320646e");
  upd state 2 (of_string "0x79622d32");
  upd state 3 (of_string "0x6b206574");  
  (* Key part *)
  let k0 = sub key 0  4  in
  let k1 = sub key 4  4  in
  let k2 = sub key 8  4 in
  let k3 = sub key 12 4 in 
  let k4 = sub key 16 4 in 
  let k5 = sub key 20 4 in
  let k6 = sub key 24 4 in
  let k7 = sub key 28 4 in
  (* Nonce part *)
  let n0 = sub nonce 0 4  in 
  let n1 = sub nonce 4 4  in 
  let n2 = sub nonce 8 4 in 
  (* Update with key *)
  upd state 4 (uint32_of_sbytes k0); 
  upd state 5 (uint32_of_sbytes k1); 
  upd state 6 (uint32_of_sbytes k2); 
  upd state 7 (uint32_of_sbytes k3); 
  upd state 8 (uint32_of_sbytes k4);
  upd state 9 (uint32_of_sbytes k5);
  upd state 10 (uint32_of_sbytes k6);
  upd state 11 (uint32_of_sbytes k7); 
  (* Block counter part *)
  upd state 12 counter; 
  (* Update with nonces *)
  upd state 13 (uint32_of_sbytes n0);
  upd state 14 (uint32_of_sbytes n1);
  upd state 15 (uint32_of_sbytes n2);
  ()

#reset-options

val sum_matrixes: new_state:uint32s{length new_state = 16} -> old_state:uint32s{length old_state = 16 /\ Disjoint new_state old_state} -> ST unit
  (requires (fun h -> Live h new_state /\ Live h old_state))
  (ensures (fun h0 _ h1 -> Live h1 new_state /\ Modifies (only new_state) h0 h1))
let sum_matrixes m m0 =
  //admit();
  upd m 0 (index m 0 ^+ index m0 0); 
  upd m 1 (index m 1 ^+ index m0 1);
  upd m 2 (index m 2 ^+ index m0 2);
  upd m 3 (index m 3 ^+ index m0 3);
  upd m 4 (index m 4 ^+ index m0 4);
  upd m 5 (index m 5 ^+ index m0 5);
  upd m 6 (index m 6 ^+ index m0 6);
  upd m 7 (index m 7 ^+ index m0 7); 
  upd m 8 (index m 8 ^+ index m0 8);
  upd m 9 (index m 9 ^+ index m0 9); 
  upd m 10 (index m 10 ^+ index m0 10);
  upd m 11 (index m 11 ^+ index m0 11);
  upd m 12 (index m 12 ^+ index m0 12);
  upd m 13 (index m 13 ^+ index m0 13);
  upd m 14 (index m 14 ^+ index m0 14);
  upd m 15 (index m 15 ^+ index m0 15);
  ()

#reset-options

val chacha20_block: output:sbytes{length output = 64} -> state:uint32s{length state = 16 /\ Disjoint state output} -> key:sbytes{length key = 32 /\ Disjoint state key /\ Disjoint output key} -> counter:uint32 -> nonce:sbytes{length nonce = 12 /\ Disjoint key nonce /\ Disjoint state nonce /\ Disjoint nonce output} -> ST unit
    (requires (fun h -> Live h state /\ Live h output /\ Live h key /\ Live h nonce))
    (ensures (fun h0 _ h1 -> Live h1 output /\ Live h1 state /\ Modifies (only output ++ state) h0 h1))
let chacha20_block output m key counter nonce =
  //admit();
    let h0 = ST.get() in
  (* Initialize internal state *)
  initialize_state m key counter nonce;
    let h1 = ST.get() in
  (* Initial state *) 
  let m0 = create #32 FStar.UInt32.zero 16 in
  blit m 0 m0 0 16;
    let h1' = ST.get() in cut (Modifies (only m) h0 h1 /\ Modifies empty h1 h1'); 
  (* 20 rounds *)
  column_round m; diagonal_round m; 
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m;
  column_round m; diagonal_round m; 
    let h2 = ST.get() in
    cut (Live h2 m /\ Modifies (only m) h0 h2); 
  (* Sum the matrixes *)
  sum_matrixes m m0;
    let h3 = ST.get() in 
    aux_lemma' output m; eq_lemma h0 h3 output (only m); 
  (* Serialize the state into byte stream *)
  sbytes_of_uint32s output m 16;
    let h4 = ST.get() in
    aux_lemma' m output; eq_lemma h3 h4 m (only output);
    ()

#reset-options

val chacha20_encrypt_loop: 
  state:uint32s{length state = 16} -> key:sbytes{length key = 32 /\ Disjoint state key} -> 
  counter:uint32 -> nonce:sbytes{length nonce = 12 /\ Disjoint state nonce /\ Disjoint key nonce} -> 
  plaintext:sbytes{Disjoint state plaintext /\ Disjoint key plaintext /\ Disjoint nonce plaintext} -> 
  ciphertext:sbytes{Disjoint state ciphertext /\ Disjoint key ciphertext /\ Disjoint nonce ciphertext /\ Disjoint plaintext ciphertext} -> j:nat -> max:nat{j <= max} -> 
  ST unit
    (requires (fun h -> Live h state /\ Live h key /\ Live h nonce /\ Live h plaintext  /\ Live h ciphertext
      /\ length plaintext >= (max-j) * 64  /\ length ciphertext >= (max-j) * 64 ))
    (ensures (fun h0 _ h1 -> Live h1 ciphertext /\ Live h1 state 
      /\ Modifies (only ciphertext ++ state) h0 h1))
let rec chacha20_encrypt_loop state key counter nonce plaintext ciphertext j max =
  //admit();
  let h0 = ST.get() in
  if j = max then ()
  else 
    begin
      (* Generate new state for block *)
      let cipher_block = sub ciphertext 0 64 in
      let ciphertext' = offset ciphertext 64 in
      let plain_block = sub plaintext 0 64 in
      let plaintext' = offset plaintext 64 in
      chacha20_block cipher_block state key (counter ^+ (of_int j)) nonce; 
	(** Lemmas **)
	let h1 = ST.get() in
	aux_lemma plain_block cipher_block state;
	eq_lemma h0 h1 plain_block (only cipher_block ++ state); 
	(** End lemmas **)
      (* XOR the key stream with the plaintext *)
      xor_bytes cipher_block cipher_block plain_block 64; 
	(** Lemmas **)
	let h2 = ST.get() in
	eq_lemma h1 h2 plain_block (only cipher_block ++ state); 
	aux_lemma' state cipher_block; 
	eq_lemma h1 h2 state (only cipher_block); 
	aux_lemma nonce cipher_block state;
	eq_lemma h0 h2 nonce (only cipher_block ++ state); 
	aux_lemma key cipher_block state;
	eq_lemma h0 h2 key (only cipher_block ++ state); 
	aux_lemma plaintext' cipher_block state;
	eq_lemma h0 h2 plaintext' (only cipher_block ++ state); 
	aux_lemma ciphertext' cipher_block state;
	eq_lemma h0 h2 ciphertext' (only cipher_block ++ state); 
	(** End lemmas **)
      (* Apply Chacha20 to the next blocks *)
      chacha20_encrypt_loop state key counter nonce plaintext' ciphertext' (Prims.op_Addition j 1) max;
	(** Lemmas **)
	let h3 = ST.get() in
	aux_lemma'' state cipher_block;
	aux_lemma'' state ciphertext';
	aux_lemma'' state ciphertext;
	modifies_subbuffer_lemma h0 h2 (only state) cipher_block ciphertext;
	modifies_subbuffer_lemma h2 h3 (only state) ciphertext' ciphertext
	(** End lemmas **)
    end

val chacha20_encrypt: 
  ciphertext:sbytes -> key:sbytes{length key = 32 /\ Disjoint ciphertext key} -> counter:uint32 -> 
  nonce:sbytes{length nonce = 12 /\ Disjoint ciphertext nonce /\ Disjoint key nonce} -> 
  plaintext:sbytes{Disjoint ciphertext plaintext /\ Disjoint key plaintext /\ Disjoint nonce plaintext} -> len:nat{length ciphertext >= len /\ length plaintext >= len} -> ST unit
    (requires (fun h -> Live h ciphertext /\ Live h key /\ Live h nonce /\ Live h plaintext))
    (ensures (fun h0 _ h1 -> Modifies (only ciphertext) h0 h1 /\ Live h1 ciphertext))
let chacha20_encrypt ciphertext key counter nonce plaintext len = 
  //admit();
  let h0 = ST.get() in
  (* Allocate the internal state *)
  let state = create #32 FStar.UInt32.zero 16  in
  (* Compute number of iterations *)
  let max = (len / 64) in 
  let rem = len % 64 in
    (** Lemmas **)
    cut (length ciphertext >= len /\ length ciphertext >= max * 64); 
    cut (length plaintext >= len /\ length plaintext >= max * 64); 
    let h1 = ST.get() in
    (** End lemmas **)    
  (* Apply Chacha20 max times **)  
  chacha20_encrypt_loop state key counter nonce plaintext ciphertext 0 max; 
    (** Lemmas **)
    let h2 = ST.get() in
    modifies_fresh h0 h2 (only ciphertext) state;
    (** End lemmas **)
  if rem = 0 then 
    begin
      (** Lemmas **)
      modifies_fresh_lemma h0 h2 (only ciphertext) state
      (** End lemmas **)
    end
  else 
    begin 
	(** Lemmas **)
	eq_lemma h1 h2 plaintext (only ciphertext ++ state); 
	eq_lemma h1 h2 key (only ciphertext ++ state); 
	eq_lemma h1 h2 nonce (only ciphertext ++ state); 
	(** End lemmas **)
      (* Apply Chacha20 to last block *)
      let cipher_block = create FStar.UInt8.zero 64 in
      let cipher_block' = offset ciphertext (max*64) in
      let plain_block = offset plaintext (max*64) in
      chacha20_block cipher_block state key (counter ^+ (of_int max)) nonce; 
	(** Lemmas **)
	let h3 = ST.get() in
	cut (rem < 64 /\ length cipher_block >= rem /\ len = Prims.op_Addition (max * 64) rem); 
	cut (True /\ length plain_block >= len - (max * 64)); 
	(** End lemmas **)	
      (* XOR the key stream with the plaintext *)
      xor_bytes cipher_block' cipher_block plain_block rem;
	(** Lemmas **)
	let h4 = ST.get() in 
	aux_lemma'' state cipher_block;
	modifies_fresh h2 h3 (only state) cipher_block; 
	modifies_subbuffer_lemma h3 h4 empty cipher_block' ciphertext; 
	empty_lemma ciphertext;
	modifies_fresh h0 h4 (only ciphertext) state
	(** End lemmas **)	
    end
    
