module Primitives.Sha256

open FStar.Array
open Primitives.Word
open Primitives.ByteArray
open Primitives.Uint32
open Primitives.Uint64



(* Define a type for registers *)
type registers = {
  a : ref uint32;
  b : ref uint32;
  c : ref uint32;
  d : ref uint32;
  e : ref uint32;
  f : ref uint32;
  g : ref uint32;
  h : ref uint32;
}

(* Definition of the circular shifts of N bits of a binary word *)
// [Coq] Definition Rotl x n := Int.ror n (Int.repr x).
val rotl: (x:ref uint32) -> (n:nat) -> St unit
let rotl x n =
  x := Word.rotate_left !x n

// [Coq] Definition Rotr x n := Int.ror n (Int.repr x).
val rotr: (x:ref uint32) -> (n:nat) -> St unit
let rotr x n =
  x := Word.rotate_right !x n


(* [FIPS 180-4] section 4.1.2 *)
// [Coq] Definition Ch (x y z : int) : int :=
//          Int.xor (Int.and x y) (Int.and (Int.not x) z).
val _Ch: uint32 -> uint32 -> uint32 -> Tot uint32
let _Ch x y z =
  Word.logxor (Word.logand x y) (Word.logand (Word.complement x) z)

// [Coq] Definition Maj (x y z : int) : int :=
//          Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).
val _Maj: uint32 -> uint32 -> uint32 -> Tot uint32
let _Maj x y z =
  Word.logxor (Word.logand x y) (Word.logxor (Word.logand x z) (Word.logand y z))

// [Coq] Definition Sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
val _Sigma0: uint32 -> Tot uint32
let _Sigma0 x =
  Word.logxor (Word.rotate_right x 2) (Word.logxor (Word.rotate_right x 13) (Word.rotate_right x 22))

// [Coq] Definition Sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
val _Sigma1: uint32 -> Tot uint32
let _Sigma1 x =
  Word.logxor (Word.rotate_right x 6) (Word.logxor (Word.rotate_right x 11) (Word.rotate_right x 25))

// [Coq] Definition sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
val _sigma0: uint32 -> Tot uint32
let _sigma0 x =
  Word.logxor (Word.rotate_right x 7) (Word.logxor (Word.rotate_right x 18) (Word.shift_right_logical x 3))

// [Coq] Definition sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).
val _sigma1: uint32 -> Tot uint32
let _sigma1 x =
  Word.logxor (Word.rotate_right x 17) (Word.logxor (Word.rotate_right x 19) (Word.shift_right_logical x 10))


(* [FIPS 180-4] section 4.2.2 *)

// [Coq] Definition K256 := map Int.repr
//       [1116352408 ; 1899447441 ; 3049323471 ; 3921009573;
//        961987163  ; 1508970993 ; 2453635748 ; 2870763221;
//        3624381080 ; 310598401  ; 607225278  ; 1426881987;
//        1925078388 ; 2162078206 ; 2614888103 ; 3248222580;
//        3835390401 ; 4022224774 ; 264347078  ; 604807628;
//        770255983  ; 1249150122 ; 1555081692 ; 1996064986;
//        2554220882 ; 2821834349 ; 2952996808 ; 3210313671;
//        3336571891 ; 3584528711 ; 113926993  ; 338241895;
//        666307205  ; 773529912  ; 1294757372 ; 1396182291;
//        1695183700 ; 1986661051 ; 2177026350 ; 2456956037;
//        2730485921 ; 2820302411 ; 3259730800 ; 3345764771;
//        3516065817 ; 3600352804 ; 4094571909 ; 275423344;
//        430227734  ; 506948616  ; 659060556  ; 883997877;
//        958139571  ; 1322822218 ; 1537002063 ; 1747873779;
//        1955562222 ; 2024104815 ; 2227730452 ; 2361852424;
//        2428436474 ; 2756734187 ; 3204031479 ; 3329325298].

val k_init: unit -> St (array uint32)
let k_init () =
  let k = FStar.Array.create 64 (Uint32.of_string "0x00000000") in
  upd k 0  (Uint32.of_string "0x428a2f98");
  upd k 1  (Uint32.of_string "0x71374491");
  upd k 2  (Uint32.of_string "0xb5c0fbcf");
  upd k 3  (Uint32.of_string "0xe9b5dba5");
  upd k 4  (Uint32.of_string "0x3956c25b");
  upd k 5  (Uint32.of_string "0x59f111f1");
  upd k 6  (Uint32.of_string "0x923f82a4");
  upd k 7  (Uint32.of_string "0xab1c5ed5");
  upd k 8  (Uint32.of_string "0xd807aa98");
  upd k 9  (Uint32.of_string "0x12835b01");
  upd k 10 (Uint32.of_string "0x243185be");
  upd k 11 (Uint32.of_string "0x550c7dc3");
  upd k 12 (Uint32.of_string "0x72be5d74");
  upd k 13 (Uint32.of_string "0x80deb1fe");
  upd k 14 (Uint32.of_string "0x9bdc06a7");
  upd k 15 (Uint32.of_string "0xc19bf174");
  upd k 16 (Uint32.of_string "0xe49b69c1");
  upd k 17 (Uint32.of_string "0xefbe4786");
  upd k 18 (Uint32.of_string "0x0fc19dc6");
  upd k 19 (Uint32.of_string "0x240ca1cc");
  upd k 20 (Uint32.of_string "0x2de92c6f");
  upd k 21 (Uint32.of_string "0x4a7484aa");
  upd k 22 (Uint32.of_string "0x5cb0a9dc");
  upd k 23 (Uint32.of_string "0x76f988da");
  upd k 24 (Uint32.of_string "0x983e5152");
  upd k 25 (Uint32.of_string "0xa831c66d");
  upd k 26 (Uint32.of_string "0xb00327c8");
  upd k 27 (Uint32.of_string "0xbf597fc7");
  upd k 28 (Uint32.of_string "0xc6e00bf3");
  upd k 29 (Uint32.of_string "0xd5a79147");
  upd k 30 (Uint32.of_string "0x06ca6351");
  upd k 31 (Uint32.of_string "0x14292967");
  upd k 32 (Uint32.of_string "0x27b70a85");
  upd k 33 (Uint32.of_string "0x2e1b2138");
  upd k 34 (Uint32.of_string "0x4d2c6dfc");
  upd k 35 (Uint32.of_string "0x53380d13");
  upd k 36 (Uint32.of_string "0x650a7354");
  upd k 37 (Uint32.of_string "0x766a0abb");
  upd k 38 (Uint32.of_string "0x81c2c92e");
  upd k 39 (Uint32.of_string "0x92722c85");
  upd k 40 (Uint32.of_string "0xa2bfe8a1");
  upd k 41 (Uint32.of_string "0xa81a664b");
  upd k 42 (Uint32.of_string "0xc24b8b70");
  upd k 43 (Uint32.of_string "0xc76c51a3");
  upd k 44 (Uint32.of_string "0xd192e819");
  upd k 45 (Uint32.of_string "0xd6990624");
  upd k 46 (Uint32.of_string "0xf40e3585");
  upd k 47 (Uint32.of_string "0x106aa070");
  upd k 48 (Uint32.of_string "0x19a4c116");
  upd k 49 (Uint32.of_string "0x1e376c08");
  upd k 50 (Uint32.of_string "0x2748774c");
  upd k 51 (Uint32.of_string "0x34b0bcb5");
  upd k 52 (Uint32.of_string "0x391c0cb3");
  upd k 53 (Uint32.of_string "0x4ed8aa4a");
  upd k 54 (Uint32.of_string "0x5b9cca4f");
  upd k 55 (Uint32.of_string "0x682e6ff3");
  upd k 56 (Uint32.of_string "0x748f82ee");
  upd k 57 (Uint32.of_string "0x78a5636f");
  upd k 58 (Uint32.of_string "0x84c87814");
  upd k 59 (Uint32.of_string "0x8cc70208");
  upd k 60 (Uint32.of_string "0x90befffa");
  upd k 61 (Uint32.of_string "0xa4506ceb");
  upd k 62 (Uint32.of_string "0xbef9a3f7");
  upd k 63 (Uint32.of_string "0xc67178f2");
  k

(* [FIPS 180-4] section 5.1.1 *)
(* l + 1 + k ≡ 448 mod 512 *)

// [Coq]
//  Definition generate_and_pad msg :=
//    let n := Zlength msg in
//     Zlist_to_intlist (msg ++ [128%Z]
//     ++ list_repeat (Z.to_nat (-(n + 9) mod 64)) 0)
//     ++ [Int.repr (n * 8 / Int.modulus); Int.repr (n * 8)].

(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
val nblocks: nat -> Tot (n:nat{ n >= 1})
let nblocks x = ((x + 8) - ((x + 8) % 64))/64 + 1

(* Create the padding and set it to the specified value *)
val pad_create: (b:bytes) -> St (pb:bytes{length pb >= 1 /\ length pb <= 64})
let pad_create raw =
  (* Compute the padding length *)
  let plen =
    let len = ByteArray.length raw in
    let len_uint64 = Uint64.of_int (len * 8) in
    if (len % 64) < 56 then 56 - (len % 64)
    else 64 + 56 - (len % 64)
  in
  let pad = ByteArray.zero_create plen in
  ByteArray.set pad 0 (ByteArray.of_string_byte "0x80");
  pad

(* Function taking bytes and storing them in a (array uint32) *)
val store_word: (fbytes:bytes) ->
                (wi:bytes{length wi = 4}) ->
                (wdata:array uint32(*{FStar.Heap.Ref wdata <> FStar.Heap.Ref wi}*)) ->
                (wmax:nat) ->
                (idxw:ref int) ->
                (idxb:ref int) -> ST unit
                               (requires (fun h -> FStar.Seq.length (FStar.Heap.sel h wdata) = wmax))
                               (ensures (fun h0 _ h1 -> True))

let rec store_word fbytes wi wdata wmax idxw idxb =
  if !idxw < wmax then begin
    (* Store four bytes into a temporary word (uint32) *)
    ByteArray.set wi 0 (ByteArray.get fbytes !idxb);
    ByteArray.set wi 1 (ByteArray.get fbytes (!idxb + 1));
    ByteArray.set wi 2 (ByteArray.get fbytes (!idxb + 2));
    ByteArray.set wi 3 (ByteArray.get fbytes (!idxb + 3));
    (* Store the temporary word to the final data array *)

    let h = FStar.ST.get () in
    admitP(True /\ ((FStar.Heap.sel h idxw) < wmax));
//    admit();

    FStar.Array.upd wdata !idxw (Uint32.of_bytes (wi));
    idxb := !idxb + 4;
    idxw := !idxw + 1;

    let h = FStar.ST.get () in
    admitP (True /\ (FStar.Seq.length (FStar.Heap.sel h wdata) = wmax));
    store_word fbytes wi wdata wmax idxw idxb end
  else ()


val pad: (data:bytes) -> (array uint32)
let pad raw =
  let idxw = ref 0 in
  let idxb = ref 0 in
  let wi = ByteArray.zero_create 4 in
  let wmax = nblocks (ByteArray.length raw) in
  let wdata = FStar.Array.create wmax (Uint32.of_string "0x00000000") in
  (* Encode the length of the raw data in 8 bytes (uint64) *)
  let lenbytes = ByteArray.length_bytes 8 raw in
  (* Generate bytes required for the padding and create the final bytes *)
  let padbytes = pad_create raw in
  let fbytes = (Primitives.ByteArray.append (Primitives.ByteArray.append lenbytes padbytes) raw) in
  (* Store the final bytes in a (array uint32) *)
  store_word fbytes wi wdata wmax idxw idxb;
  wdata

(* [FIPS 180-4] section 6.2.2 *)
(* Block processing functions *)

// [Coq]
// Function W (M: Z -> int) (t: Z) {measure Z.to_nat t} : int :=
//   if zlt t 16
//   then M t
//   else  (Int.add (Int.add (sigma_1 (W M (t-2))) (W M (t-7)))
//                (Int.add (sigma_0 (W M (t-15))) (W M (t-16)))).
// Proof.
// intros; apply Z2Nat.inj_lt; omega.
// intros; apply Z2Nat.inj_lt; omega.
// intros; apply Z2Nat.inj_lt; omega.
// intros; apply Z2Nat.inj_lt; omega.
// Qed.

(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
val wsched: array uint32 -> nat -> uint32
let rec wsched data t =
  if t >= 0 && t < 16 then
    FStar.Array.index data t
  else if t < 64 then
    Uint32.add (_sigma1 (wsched data (t-2)))
               (Uint32.add (wsched data (t-7))
                           (Uint32.add (_sigma0 (wsched data (t-15)))
                                       (wsched data (t-16))))
  else
    failwith "Error: scheduling function only handle values from 0 to 63 included"


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)

// [Coq] Definition init_registers : registers :=
//   map Int.repr  [1779033703; 3144134277; 1013904242; 2773480762;
//                  1359893119; 2600822924; 528734635; 1541459225].
val init : unit -> array uint32
let init () =
  let m =
    FStar.Array.create 8 (Uint32.of_string "0x00000000")
  in
  upd m 0 (Uint32.of_string "0x6a09e667");
  upd m 1 (Uint32.of_string "0xbb67ae85");
  upd m 2 (Uint32.of_string "0x3c6ef372");
  upd m 3 (Uint32.of_string "0xa54ff53a");
  upd m 4 (Uint32.of_string "0x510e527f");
  upd m 5 (Uint32.of_string "0x9b05688c");
  upd m 6 (Uint32.of_string "0x1f83d9ab");
  upd m 7 (Uint32.of_string "0x5be0cd19");
  m

(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
//
// [Coq]
// Definition hash_block (r: registers) (block: list int) : registers :=
//      map2 Int.add r (Round r (nthi block) 63).
//
// Function hash_blocks (r: registers) (msg: list int) {measure length msg} : registers :=
//   match msg with
//   | nil => r
//   | _ => hash_blocks (hash_block r (firstn 16 msg)) (skipn 16 msg)
//   end.
// Proof. intros.
//  destruct (lt_dec (length msg) 16).
//  rewrite skipn_length_short. simpl; omega. subst; simpl in *; omega.
//  rewrite <- teq; auto.
//  rewrite skipn_length. simpl; omega.
// Qed.
val update : (hash:array uint32) -> (data:array uint32) -> array uint32
let update hash data =
  let i = ref 0 in
  let max = FStar.Array.length data in
  let t1 = ref Uint32.zero in
  let t2 = ref Uint32.zero in
  let k = k_init () in
  let rec process_chunk (i:ref int) =
    if !i < max then begin
    let data_block = Array.sub data (!i * 16) 16 in
    (* Step 2 : Initialize the eight working variables *)
    let wh = {
      a = ref (FStar.Array.index hash 0);
      b = ref (FStar.Array.index hash 1);
      c = ref (FStar.Array.index hash 2);
      d = ref (FStar.Array.index hash 3);
      e = ref (FStar.Array.index hash 4);
      f = ref (FStar.Array.index hash 5);
      g = ref (FStar.Array.index hash 6);
      h = ref (FStar.Array.index hash 7);
    } in
    (* Step 3 : Perform logical operations on the working variables *)
    let t = ref 0 in
    let rec inner_loop (t:ref int) =
      if !t < 63 then begin
        t1 := Uint32.add !(wh.h)
                         (Uint32.add (_Sigma1 !(wh.e))
                                     (Uint32.add (_Ch !(wh.e) !(wh.f) !(wh.g))
                                                 (Uint32.add (FStar.Array.index k !t) (wsched data_block !t))));
        t2 := Uint32.add (_Sigma0 !(wh.a)) (_Maj !(wh.a) !(wh.b) !(wh.c));
        wh.h := !(wh.g);
        wh.g := !(wh.f);
        wh.f := !(wh.e);
        wh.e := Uint32.add !(wh.d) !t1;
        wh.d := !(wh.c);
        wh.c := !(wh.b);
        wh.b := !(wh.a);
        wh.a := Uint32.add !t1 !t2;
        t := (!t + 1);
        inner_loop t end
      else ()
    in inner_loop t;
    (* Step 4 : Compute the ith intermediate hash value *)
    upd hash 0 (Uint32.add !(wh.a) (FStar.Array.index hash 0));
    upd hash 1 (Uint32.add !(wh.b) (FStar.Array.index hash 1));
    upd hash 2 (Uint32.add !(wh.c) (FStar.Array.index hash 2));
    upd hash 3 (Uint32.add !(wh.d) (FStar.Array.index hash 3));
    upd hash 4 (Uint32.add !(wh.e) (FStar.Array.index hash 4));
    upd hash 5 (Uint32.add !(wh.f) (FStar.Array.index hash 5));
    upd hash 6 (Uint32.add !(wh.g) (FStar.Array.index hash 6));
    upd hash 7 (Uint32.add !(wh.h) (FStar.Array.index hash 7));
    i := !i + 1;
    process_chunk i end
  else ()
  in
  process_chunk i;
  hash

(* Compute the final value of the hash from the last hash value *)
val finish: (hash:array uint32) -> bytes
let finish hash =
  Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 7))
    (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 6))
      (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 5))
        (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 4))
          (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 3))
            (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 2))
              (Primitives.ByteArray.append (uint32_to_bytes (FStar.Array.index hash 1))
                                           (uint32_to_bytes (FStar.Array.index hash 0))))))))

(* Compute the sha256 hash of some bytes *)

// [Coq] Definition SHA_256 (str : list Z) : list Z :=
//     intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).
val sha265: (data:bytes) -> St bytes
let sha256 data =
  let pdata = pad data in
  let hash = init () in
  let hash = update hash pdata in
  finish hash
