module Chacha

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HST
open FStar.Int.Cast
open FStar.UInt8
open FStar.UInt32
open FStar.Buffer

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let u32 = UInt32.t
let u8 = UInt8.t
let uint32s = buffer u32
let bytes = buffer u8

(** Infix operators and helping lemmas **)
// Needs to be instanciated differently
assume MaxUint32: FStar.UInt.max_int 32 = 4294967295

val aux_lemma: #t:Type -> #t':Type -> #t'':Type -> a:buffer t -> b:buffer t' -> c:buffer t'' -> 
  Lemma (requires (disjoint a b /\ disjoint a c))
	(ensures (disjointSet a (only b ++ c)))
let aux_lemma #t #t' #t'' a b c = ()

val aux_lemma': #t:Type -> a:buffer t -> #t':Type -> b:buffer t' -> 
  Lemma (requires (disjoint a b))
	(ensures (disjointSet a (only b)))
let aux_lemma' #t a #t' b = ()

val aux_lemma'': #t:Type -> a:buffer t -> #t':Type -> a':buffer t' -> 
  Lemma (Set.equal (only a ++ a') (only a' ++ a))
let aux_lemma'' #t a #t' a' = ()  

val empty_lemma: #t:Type -> b:buffer t -> Lemma (Set.equal (empty ++ b) (only b))
let empty_lemma #t b = ()

let op_Greater_Greater_Greater (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in
  (op_Greater_Greater_Hat a s) |^ (a <<^ (m -^ s))

let op_Less_Less_Less (a:u32) (s:u32{v s <= 32}) =
  let (m:u32{v m = 32}) = 32ul in  
  (op_Less_Less_Hat a s) |^ (op_Greater_Greater_Hat a (m -^ s))

(* Chacha 20 code *)
val quarter_round: m:uint32s{length m = 16} -> 
  a:u32{v a < 16} -> b:u32{v b<16} -> c:u32{v c<16} -> d:u32{v d<16} -> ST unit 
  (requires (fun h -> live h m)) 
  (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1))
let quarter_round m a b c d =
  upd m a (index m a +%^ index m b);
  upd m d (index m d ^^ index m a);
  let (tmp:u32) = index m d in 
  upd m d (tmp <<< UInt32.uint_to_t 16); 
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 12);
  upd m a (index m a +%^ index m b); 
  upd m d (index m d ^^ index m a); 
  let tmp = index m d in
  upd m d (tmp <<< UInt32.uint_to_t 8);
  upd m c (index m c +%^ index m d); 
  upd m b (index m b ^^ index m c); 
  let tmp = index m b in
  upd m b (tmp <<< UInt32.uint_to_t 7)
 
(* Chacha20 block function *)
val column_round: m:uint32s{length m = 16} -> ST unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let column_round m =
  quarter_round m 0ul 4ul 8ul 12ul;
  quarter_round m 1ul 5ul 9ul 13ul;
  quarter_round m 2ul 6ul 10ul 14ul;
  quarter_round m 3ul 7ul 11ul 15ul

val diagonal_round: m:uint32s{length m = 16} -> ST unit
    (requires (fun h -> live h m))
    (ensures (fun h0 _ h1 -> live h1 m /\ modifies_1 m h0 h1 ))
let diagonal_round m =
  quarter_round m 0ul 5ul 10ul 15ul;
  quarter_round m 1ul 6ul 11ul 12ul;
  quarter_round m 2ul 7ul 8ul 13ul;
  quarter_round m 3ul 4ul 9ul 14ul

val uint32_of_bytes: b:bytes{length b >= 4} -> STL u32
  (requires (fun h -> live h b))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 b
    /\ v r = UInt8.v (get h0 b 0) * pow2 8 * UInt8.v (get h0 b 1)
      + pow2 16 * UInt8.v (get h0 b 2) + pow2 24 * UInt8.v (get h0 b 3)))
let uint32_of_bytes (b:bytes{length b >= 4}) =
  let b0 = (index b 0ul) in
  let b1 = (index b 1ul) in
  let b2 = (index b 2ul) in
  let b3 = (index b 3ul) in
  let r = (op_Less_Less_Hat (uint8_to_uint32 b3) 24ul)
	+%^ (op_Less_Less_Hat (uint8_to_uint32 b2) 16ul)
	+%^ (op_Less_Less_Hat (uint8_to_uint32 b1) 8ul)
	+%^ uint8_to_uint32 b0 in
  (* TODO *)
  assume (v r = UInt8.v b0 * pow2 8 * UInt8.v b1  + pow2 16 * UInt8.v b2 + pow2 24 * UInt8.v b3);
  r

let op_Hat_Greater_Greater = op_Greater_Greater_Hat
let op_Hat_Star = op_Star_Hat

#reset-options "--z3timeout 20"

val bytes_of_uint32s: output:bytes -> m:uint32s{disjoint output m} -> len:u32{op_Multiply 4 (v len)<=length output /\ v len<=length m} -> STL unit
  (requires (fun h -> live h output /\ live h m))
  (ensures (fun h0 _ h1 -> live h0 output /\ live h0 m /\ live h1 output /\ live h1 m
    /\ modifies_1 output h0 h1 ))
let rec bytes_of_uint32s output m len =
  if len =^ 0ul then ()
  else 
    begin
      let l = len -^ 1ul in
      let x = index m l in
      let b0 = uint32_to_uint8 (x &^ 255ul) in
      let b1 = uint32_to_uint8 ((x ^>> 8ul) &^ 255ul) in
      let b2 = uint32_to_uint8 ((x ^>> 16ul) &^ 255ul) in
      let b3 = uint32_to_uint8 ((x ^>> 24ul) &^ 255ul) in
      let l4 = l ^* 4ul in
      upd output l4 b0; 
      upd output (l4 +^ 1ul) b1;
      upd output (l4 +^ 2ul) b2;
      upd output (l4 +^ 3ul) b3;
      bytes_of_uint32s output m l
    end

#reset-options

val xor_bytes: output:bytes -> in1:bytes -> in2:bytes{disjoint in1 in2 /\ disjoint in1 output /\ disjoint in2 output} -> len:u32{v len <= length output /\ v len <= length in1 /\ v len <= length in2} -> STL unit
  (requires (fun h -> live h output /\ live h in1 /\ live h in2))
  (ensures  (fun h0 _ h1 -> live h0 output /\ live h0 in1 /\ live h0 in2 
    /\ live h1 output /\ live h1 in1 /\ live h1 in2
    /\ modifies_1 output h0 h1
    (* /\ (forall (i:nat). i < v len ==> get h1 output i = (UInt8.logxor (get h0 in1 i) (get h0 in2 i))) *)
   )) 
let rec xor_bytes output in1 in2 len =
  let h0 = HST.get() in
  if len =^ 0ul then ()
  else
    begin
      let i = len -^ 1ul in 
      let in1i = index in1 i in
      let in2i = index in2 i in
      let oi = UInt8.logxor in1i in2i in
      upd output i oi; 
      let h1 = HST.get() in
      no_upd_lemma_1 h0 h1 output in1;
      no_upd_lemma_1 h0 h1 output in2;
      xor_bytes output in1 in2 i
    end

#set-options "--lax" // TODO

val initialize_state: state:uint32s{length state = 16} -> 
  key:bytes{length key = 32 /\ disjoint state key} -> counter:u32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint key nonce /\ disjoint state nonce} -> STL unit
  (requires (fun h -> live h state /\ live h key /\ live h nonce))
  (ensures (fun h0 _ h1 -> live h1 state /\ modifies_1 state h0 h1))
let initialize_state state key counter nonce =
  (* Constant part *)
  upd state 0ul (of_string "0x61707865");
  upd state 1ul (of_string "0x3320646e");
  upd state 2ul (of_string "0x79622d32");
  upd state 3ul (of_string "0x6b206574");
  (* Key part *)
  let k0 = sub key 0ul  4ul in 
  let k1 = sub key 4ul  4ul in 
  let k2 = sub key 8ul  4ul in 
  let k3 = sub key 12ul 4ul in 
  let k4 = sub key 16ul 4ul in 
  let k5 = sub key 20ul 4ul in 
  let k6 = sub key 24ul 4ul in 
  let k7 = sub key 28ul 4ul in
  (* let k0 = sub key 0ul 4ul  in  *)
  (* let k1 = sub key 4ul 4ul  in *)
  (* let k2 = sub key 8ul 4ul  in *)
  (* let k3 = sub key 12ul 4ul in  *)
  (* let k4 = sub key 16ul 4ul in  *)
  (* let k5 = sub key 20ul 4ul in *)
  (* let k6 = sub key 24ul 4ul in *)
  (* let k7 = sub key 28ul 4ul in  *)
  (* Nonce part *)
  let n0 = sub nonce 0ul 4ul in 
  let n1 = sub nonce 4ul 4ul in 
  let n2 = sub nonce 8ul 4ul in
  (* Update with key *)
  upd state 4ul  (uint32_of_bytes k0); 
  upd state 5ul  (uint32_of_bytes k1); 
  upd state 6ul  (uint32_of_bytes k2); 
  upd state 7ul  (uint32_of_bytes k3); 
  upd state 8ul  (uint32_of_bytes k4);
  upd state 9ul  (uint32_of_bytes k5);
  upd state 10ul (uint32_of_bytes k6);
  upd state 11ul (uint32_of_bytes k7);
  (* Block counter part *)
  upd state 12ul counter; 
  (* Update with nonces *)
  upd state 13ul (uint32_of_bytes n0);
  upd state 14ul (uint32_of_bytes n1);
  upd state 15ul (uint32_of_bytes n2)

#reset-options

val sum_matrixes: new_state:uint32s{length new_state = 16} -> old_state:uint32s{length old_state = 16 /\ disjoint new_state old_state} -> ST unit
  (requires (fun h -> live h new_state /\ live h old_state))
  (ensures (fun h0 _ h1 -> live h1 new_state /\ modifies_1 new_state h0 h1))
let sum_matrixes m m0 =
  upd m 0ul (index m 0ul +%^ index m0 0ul); 
  upd m 1ul (index m 1ul +%^ index m0 1ul);
  upd m 2ul (index m 2ul +%^ index m0 2ul);
  upd m 3ul (index m 3ul +%^ index m0 3ul);
  upd m 4ul (index m 4ul +%^ index m0 4ul);
  upd m 5ul (index m 5ul +%^ index m0 5ul);
  upd m 6ul (index m 6ul +%^ index m0 6ul);
  upd m 7ul (index m 7ul +%^ index m0 7ul); 
  upd m 8ul (index m 8ul +%^ index m0 8ul);
  upd m 9ul (index m 9ul +%^ index m0 9ul); 
  upd m 10ul (index m 10ul +%^ index m0 10ul);
  upd m 11ul (index m 11ul +%^ index m0 11ul);
  upd m 12ul (index m 12ul +%^ index m0 12ul);
  upd m 13ul (index m 13ul +%^ index m0 13ul);
  upd m 14ul (index m 14ul +%^ index m0 14ul);
  upd m 15ul (index m 15ul +%^ index m0 15ul);
  ()

let s #t (b:buffer t) = Set.singleton (frameOf b)
let op_Plus_Plus = Set.union

#set-options "--lax" // Try large timeout

let lemma_chacha20_block (output:bytes) (state:uint32s{frameOf output <> frameOf state}) 
  (m0:uint32s{frameOf m0 <> frameOf state /\ frameOf m0 <> frameOf output})
  hinit h0 h1 h2 h3 h4 h5 hfin : Lemma
  (requires (live hinit state /\ live hinit output /\ fresh_frame hinit h0 /\ ~(contains h0 m0)
    /\ modifies_1 state h0 h1 /\ live h1 state
    /\ modifies_0 h1 h2 /\ live h2 m0 /\ frameOf m0 = h0.tip
    /\ modifies_1 m0 h2 h3 /\ live h3 m0
    /\ modifies_1 state h3 h4 /\ live h4 state
    /\ modifies_1 output h4 h5 /\ live h5 output
    /\ popped h5 hfin ))
  (ensures (modifies_2 output state hinit hfin /\ live hfin output /\ live hfin state ))
  = ()

(* #set-options "--lax" *)

#reset-options

val chacha20_block: output:bytes{length output = 64} -> 
  state:uint32s{length state = 16 /\ frameOf state <> frameOf output} ->
  key:bytes{length key = 32 /\ disjoint state key /\ disjoint output key} -> counter:u32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint key nonce /\ disjoint state nonce /\ disjoint nonce output} -> STL unit
    (requires (fun h -> live h state /\ live h output /\ live h key /\ live h nonce))
    (ensures (fun h0 _ h1 -> live h1 output /\ live h1 state /\ modifies_2 output state h0 h1 ))
let chacha20_block output m key counter nonce =
  let h0 = HST.get() in
  push_frame ();
  (* Initialize internal state *)
  let h0' = HST.get() in
  initialize_state m key counter nonce;
  let h1 = HST.get() in
  cut(modifies_1 m h0' h1);
  (* Initial state *) 
  let m0 = create 0ul 16ul in
  let h2 = HST.get() in
  cut(modifies_0 h1 h2);
  blit m 0ul m0 0ul 16ul;
  let h3 = HST.get() in
  cut(modifies_1 m0 h2 h3);
  cut(live h3 output); 
  cut(live h3 m); 
  cut(live h3 m0);
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
  let h4 = HST.get() in
  no_upd_lemma_1 h3 h4 m m0;
  cut(modifies_1 m h3 h4); 
  cut(live h4 m0); 
  (* Sum the matrixes *)
  sum_matrixes m m0;
  let h5 = HST.get() in
  cut(modifies_1 m h3 h5);
  no_upd_lemma_1 h3 h5 m output;
  (* Serialize the state into byte stream *)
  bytes_of_uint32s output m 16ul;
  let h6 = HST.get() in
  cut(modifies_1 output h5 h6);
  cut(live h6 output /\ live h6 m);
  pop_frame ();
  let h7 = HST.get() in
  cut (live h0 m /\ live h0 output /\ fresh_frame h0 h0' /\ ~(contains h0' m0));
  cut (modifies_1 m h0' h1 /\ modifies_0 h1 h2 /\ modifies_1 m0 h2 h3 /\ modifies_1 m h3 h5);
  cut ( modifies_1 output h5 h6 /\ popped h6 h7);
  cut (frameOf m0 <> frameOf output /\ frameOf m <> frameOf m0); 
  lemma_chacha20_block output m m0 h0 h0' h1 h2 h3 h5 h6 h7; 
  assume (equal_domains h0 h7) // TODO, need lemmas about that

#reset-options
#set-options "--lax"

val chacha20_encrypt_loop: 
  state:uint32s{length state = 16} -> key:bytes{length key = 32 /\ disjoint state key} -> 
  counter:u32 -> nonce:bytes{length nonce = 12 /\ disjoint state nonce /\ disjoint key nonce} -> 
  plaintext:bytes{disjoint state plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} -> 
  ciphertext:bytes{frameOf state <> frameOf ciphertext /\ disjoint key ciphertext /\ disjoint nonce ciphertext /\ disjoint plaintext ciphertext} -> j:u32 -> max:u32{v j <= v max /\ v counter + v max < pow2 n} -> 
  STL unit
    (requires (fun h -> live h state /\ live h key /\ live h nonce /\ live h plaintext  /\ live h ciphertext
      /\ length plaintext >= (v max-v j) * 64  /\ length ciphertext >= (v max-v j) * 64 ))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ live h1 state /\ modifies_2 ciphertext state h0 h1 ))
let rec chacha20_encrypt_loop state key counter nonce plaintext ciphertext j max =
  let h0 = HST.get() in
  if j = max then ()
  else 
    begin
      (* Generate new state for block *)
      let cipher_block = sub ciphertext 0ul 64ul in
      let ciphertext' = sub ciphertext 64ul (64ul ^* (max -^ j -^ 1ul)) in
      let plain_block = sub plaintext 0ul 64ul in
      let plaintext' = sub plaintext 64ul (64ul ^* (max -^ j -^ 1ul)) in
      chacha20_block cipher_block state key (counter +^ j) nonce; 
	(** Lemmas **)
	let h1 = HST.get() in
	(* aux_lemma plain_block cipher_block state; *)
	(* (\* eq_lemma h0 h1 plain_block (only cipher_block ++ state);  *\) *)
	(** End lemmas **)
      (* XOR the key stream with the plaintext *)
      xor_bytes cipher_block cipher_block plain_block 64ul; 
	(** Lemmas **)
	let h2 = HST.get() in
	(* (\* eq_lemma h1 h2 plain_block (only cipher_block ++ state);  *\) *)
	(* aux_lemma' state cipher_block;  *)
	(* (\* eq_lemma h1 h2 state (only cipher_block);  *\) *)
	(* aux_lemma nonce cipher_block state; *)
	(* (\* eq_lemma h0 h2 nonce (only cipher_block ++ state);  *\) *)
	(* aux_lemma key cipher_block state; *)
	(* (\* eq_lemma h0 h2 key (only cipher_block ++ state);  *\) *)
	(* aux_lemma plaintext' cipher_block state; *)
	(* (\* eq_lemma h0 h2 plaintext' (only cipher_block ++ state);  *\) *)
	(* aux_lemma ciphertext' cipher_block state; *)
	(* (\* eq_lemma h0 h2 ciphertext' (only cipher_block ++ state);  *\) *)
	(** End lemmas **)
      (* Apply Chacha20 to the next blocks *)
      chacha20_encrypt_loop state key counter nonce plaintext' ciphertext' (j +^ 1ul) max;
	(** Lemmas **)
	let h3 = HST.get() in
	(* aux_lemma'' state cipher_block; *)
	(* aux_lemma'' state ciphertext'; *)
	(* aux_lemma'' state ciphertext; *)
	(* modifies_subbuffer_lemma h0 h2 (only state) cipher_block ciphertext; *)
	(* modifies_subbuffer_lemma h2 h3 (only state) ciphertext' ciphertext *)
	()
	(** End lemmas **)
    end

let op_Hat_Slash = op_Slash_Hat
let op_Hat_Percent = op_Percent_Hat

val chacha20_encrypt: 
  ciphertext:bytes -> key:bytes{length key = 32 /\ disjoint ciphertext key} -> counter:u32 -> 
  nonce:bytes{length nonce = 12 /\ disjoint ciphertext nonce /\ disjoint key nonce} -> 
  plaintext:bytes{disjoint ciphertext plaintext /\ disjoint key plaintext /\ disjoint nonce plaintext} -> len:u32{length ciphertext >= v len /\ length plaintext >= v len /\ v counter + v len / 64 < pow2 32} -> STL unit
    (requires (fun h -> live h ciphertext /\ live h key /\ live h nonce /\ live h plaintext))
    (ensures (fun h0 _ h1 -> live h1 ciphertext /\ modifies_1 ciphertext h0 h1))
let chacha20_encrypt ciphertext key counter nonce plaintext len = 
  push_frame ();
  let h0 = HST.get() in
  (* Allocate the internal state *)
  let state = create 0ul 16ul  in
  (* Compute number of iterations *)
  let max = (len ^/ 64ul) in 
  let rem = len ^% 64ul in
    (** Lemmas **)
    (* cut (length ciphertext >= v len /\ length ciphertext >= v max * 64);  *)
    (* cut (length plaintext >= v len /\ length plaintext >= v max * 64);  *)
    let h1 = HST.get() in
    (** End lemmas **)    
  (* Apply Chacha20 max times **)  
  (* assert(disjoint state plaintext); admit() *)
  chacha20_encrypt_loop state key counter nonce plaintext ciphertext 0ul max;
    (** Lemmas **)
    let h2 = HST.get() in 
    assert(frameOf state = h0.tip);
    modifies_fresh h0 h2 (only ciphertext) state;
    (** End lemmas **)
  if rem =^ 0ul then 
    begin
      (** Lemmas **)
      (* modifies_fresh_lemma h0 h2 (only ciphertext) state *)
      ()
      (** End lemmas **)
    end
  else 
    begin 
	(** Lemmas **)
	(* eq_lemma h1 h2 plaintext (only ciphertext ++ state);  *)
	(* eq_lemma h1 h2 key (only ciphertext ++ state);  *)
	(* eq_lemma h1 h2 nonce (only ciphertext ++ state);  *)
	(** End lemmas **)
      (* Apply Chacha20 to last block *)
      let cipher_block = create 0uy 64ul in
      let cipher_block' = sub ciphertext (max ^* 64ul) (len -^ (max ^* 64ul)) in
      let plain_block = sub plaintext (max ^* 64ul) (len -^ (max ^* 64ul)) in
      (* let cipher_block' = offset ciphertext (max*64) in *)
      (* let plain_block = offset plaintext (max*64) in *)
      chacha20_block cipher_block state key (counter +^ max) nonce; 
	(** Lemmas **)
	let h3 = HST.get() in
	(* cut (v rem < 64 /\ length cipher_block >= v rem /\ v len = Prims.op_Addition (v max * 64) (v rem));  *)
	(* cut (True /\ length plain_block >= v len - (v max * 64));  *)
	(** End lemmas **)	
      (* XOR the key stream with the plaintext *)
      xor_bytes cipher_block' cipher_block plain_block rem;
	(** Lemmas **)
	let h4 = HST.get() in 
	aux_lemma'' state cipher_block;
	modifies_fresh h2 h3 (only state) cipher_block
	(* modifies_subbuffer_lemma h3 h4 empty cipher_block' ciphertext;  *)
	(* empty_lemma ciphertext; *)
	(* modifies_fresh h0 h4 (only ciphertext) state *)
	(** End lemmas **)	
    end;
    pop_frame ();
    admit()
