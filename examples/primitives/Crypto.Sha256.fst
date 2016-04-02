module Crypto.Sha256

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open FStar.UInt64
open FStar.UInt32

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
val rotl: (x:ref uint32) ->
          (n:nat {n <= 32})
          -> ST unit
               (requires (fun h -> contains h x))
               (ensures (fun h0 _ h1 -> contains h1 x
                                   /\ sel h1 x = UInt32.rotate_left (sel h0 x) n))
let rotl x n =
  x := UInt32.rotate_left !x n

// [Coq] Definition Rotr x n := Int.ror n (Int.repr x).
val rotr: (x:ref uint32) ->
          (n:nat {n <= 32})
          -> ST unit
               (requires (fun h -> contains h x))
               (ensures (fun h0 _ h1 -> contains h1 x
                                   /\ sel h1 x = UInt32.rotate_right (sel h0 x) n))
let rotr x n =
  x := UInt32.rotate_right !x n

(* [FIPS 180-4] section 4.1.2 *)
// [Coq] Definition Ch (x y z : int) : int :=
//          Int.xor (Int.and x y) (Int.and (Int.not x) z).
val _Ch: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

// [Coq] Definition Maj (x y z : int) : int :=
//          Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).
val _Maj: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

// [Coq] Definition Sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
val _Sigma0: x:uint32 -> Tot uint32
let _Sigma0 x = logxor (rotate_right x 2) (logxor (rotate_right x 13) (rotate_right x 22))

// [Coq] Definition Sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
val _Sigma1: x:uint32 -> Tot uint32
let _Sigma1 x = logxor (rotate_right x 6) (logxor (rotate_right x 11) (rotate_right x 25))

// [Coq] Definition sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
val _sigma0: x:uint32 -> Tot uint32
let _sigma0 x = logxor (rotate_right x 7) (logxor (rotate_right x 18) (shift_right x 3))

// [Coq] Definition sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).
val _sigma1: x:uint32 -> Tot uint32
let _sigma1 x = logxor (rotate_right x 17) (logxor (rotate_right x 19) (shift_right x 10))

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

val k_init: unit -> St (buffer 32)
let k_init () =
  let k = SBuffer.create #32 FStar.UInt32.zero 64  in
  SBuffer.upd k 0  (of_string "0x428a2f98");
  SBuffer.upd k 1  (of_string "0x71374491");
  SBuffer.upd k 2  (of_string "0xb5c0fbcf");
  SBuffer.upd k 3  (of_string "0xe9b5dba5");
  SBuffer.upd k 4  (of_string "0x3956c25b");
  SBuffer.upd k 5  (of_string "0x59f111f1");
  SBuffer.upd k 6  (of_string "0x923f82a4");
  SBuffer.upd k 7  (of_string "0xab1c5ed5");
  SBuffer.upd k 8  (of_string "0xd807aa98");
  SBuffer.upd k 9  (of_string "0x12835b01");
  SBuffer.upd k 10 (of_string "0x243185be");
  SBuffer.upd k 11 (of_string "0x550c7dc3");
  SBuffer.upd k 12 (of_string "0x72be5d74");
  SBuffer.upd k 13 (of_string "0x80deb1fe");
  SBuffer.upd k 14 (of_string "0x9bdc06a7");
  SBuffer.upd k 15 (of_string "0xc19bf174");
  SBuffer.upd k 16 (of_string "0xe49b69c1");
  SBuffer.upd k 17 (of_string "0xefbe4786");
  SBuffer.upd k 18 (of_string "0x0fc19dc6");
  SBuffer.upd k 19 (of_string "0x240ca1cc");
  SBuffer.upd k 20 (of_string "0x2de92c6f");
  SBuffer.upd k 21 (of_string "0x4a7484aa");
  SBuffer.upd k 22 (of_string "0x5cb0a9dc");
  SBuffer.upd k 23 (of_string "0x76f988da");
  SBuffer.upd k 24 (of_string "0x983e5152");
  SBuffer.upd k 25 (of_string "0xa831c66d");
  SBuffer.upd k 26 (of_string "0xb00327c8");
  SBuffer.upd k 27 (of_string "0xbf597fc7");
  SBuffer.upd k 28 (of_string "0xc6e00bf3");
  SBuffer.upd k 29 (of_string "0xd5a79147");
  SBuffer.upd k 30 (of_string "0x06ca6351");
  SBuffer.upd k 31 (of_string "0x14292967");
  SBuffer.upd k 32 (of_string "0x27b70a85");
  SBuffer.upd k 33 (of_string "0x2e1b2138");
  SBuffer.upd k 34 (of_string "0x4d2c6dfc");
  SBuffer.upd k 35 (of_string "0x53380d13");
  SBuffer.upd k 36 (of_string "0x650a7354");
  SBuffer.upd k 37 (of_string "0x766a0abb");
  SBuffer.upd k 38 (of_string "0x81c2c92e");
  SBuffer.upd k 39 (of_string "0x92722c85");
  SBuffer.upd k 40 (of_string "0xa2bfe8a1");
  SBuffer.upd k 41 (of_string "0xa81a664b");
  SBuffer.upd k 42 (of_string "0xc24b8b70");
  SBuffer.upd k 43 (of_string "0xc76c51a3");
  SBuffer.upd k 44 (of_string "0xd192e819");
  SBuffer.upd k 45 (of_string "0xd6990624");
  SBuffer.upd k 46 (of_string "0xf40e3585");
  SBuffer.upd k 47 (of_string "0x106aa070");
  SBuffer.upd k 48 (of_string "0x19a4c116");
  SBuffer.upd k 49 (of_string "0x1e376c08");
  SBuffer.upd k 50 (of_string "0x2748774c");
  SBuffer.upd k 51 (of_string "0x34b0bcb5");
  SBuffer.upd k 52 (of_string "0x391c0cb3");
  SBuffer.upd k 53 (of_string "0x4ed8aa4a");
  SBuffer.upd k 54 (of_string "0x5b9cca4f");
  SBuffer.upd k 55 (of_string "0x682e6ff3");
  SBuffer.upd k 56 (of_string "0x748f82ee");
  SBuffer.upd k 57 (of_string "0x78a5636f");
  SBuffer.upd k 58 (of_string "0x84c87814");
  SBuffer.upd k 59 (of_string "0x8cc70208");
  SBuffer.upd k 60 (of_string "0x90befffa");
  SBuffer.upd k 61 (of_string "0xa4506ceb");
  SBuffer.upd k 62 (of_string "0xbef9a3f7");
  SBuffer.upd k 63 (of_string "0xc67178f2");
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
val nblocks: nat -> Tot (n:nat{n >= 1})
let nblocks x = ((x + 8) - ((x + 8) % 64))/64 + 1

(* Pad the data and return a buffer of uint32 for subsequent treatment *)
val pad: (rdata :buffer 8 ) ->
         (rlen  :nat { length rdata = rlen })
         -> ST (data:buffer 8)
              (requires (fun h -> Live h rdata))
              (ensures  (fun h0 r h1 -> Live h1 rdata /\ h0 = h1))
// TODO: Refinement on the value of the pad -> length raw + rplen = 64
let pad rdata rlen =
  // Value of the raw data length in bits represented as UInt64
  let rlen_64 =
    let v = create #8 FStar.UInt8.zero 8 in
    let v64 = FStar.UInt64.of_int (rlen * 8) in
    FStar.SBytes.sbytes_of_uint64 v v64;
    v
  in
  // Compute the padding length
  let rplen =
    if (rlen % 64) < 56 then 56 - (rlen % 64)
    else 64 + 56 - (rlen % 64)
  in
  // Generate the padding
  let rpad = create #8 zero rplen in
  SBuffer.upd rpad 0 (FStar.UInt8.of_string "0x80");
  // Create the final data as a buffer of bytes
  let data = SBuffer.create #8 FStar.UInt8.zero (rlen + rplen + 8) in
  blit rdata 0 data 0 rlen;
  blit rpad 0 data rlen rplen;
  blit rlen_64 0 data (rlen + rplen) 8;
  data

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
val wsched: (ws    :buffer 32 { length ws = 64 }) ->
            (pdata :sbytes    { Disjoint ws pdata }) ->
            (len   :nat         { length pdata = len }) ->
            (tw    :sbytes    { length tw = 4 }) ->
            (t     :ref nat)
            -> ST unit
                 (requires (fun h -> Live h pdata /\ Live h ws))
                 (ensures  (fun h0 r h1 -> Live h1 pdata /\ Live h1 ws))

let rec wsched ws pdata len tw t =
  if !t >= 0 && !t < 16 then begin
    (* Transform pdata into a buffer 32 *)
    SBuffer.upd tw 0 (index pdata (!t * 4));
    SBuffer.upd tw 1 (index pdata (!t * 4 + 1));
    SBuffer.upd tw 2 (index pdata (!t * 4 + 2));
    SBuffer.upd tw 3 (index pdata (!t * 4 + 3));
    let w = FStar.SBytes.uint32_of_sbytes tw in
    SBuffer.upd ws !t w end
  else if !t < 64 then
    let _t16 = index ws (!t-16) in
    let _t15 = index ws (!t-15) in
    let _t7 = index ws (!t-7) in
    let _t2 = index ws (!t-2) in

    let v0 = _sigma1 _t2 in
    let v1 = _sigma0 _t15 in

    let v = (FStar.UInt32.add v0
                              (FStar.UInt32.add _t7
                                                (FStar.UInt32.add v1 _t16)))
    in SBuffer.upd ws !t v;
    t := !t + 1
  else ()

(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)

// [Coq] Definition init_registers : registers :=
//   map Int.repr  [1779033703; 3144134277; 1013904242; 2773480762;
//                  1359893119; 2600822924; 528734635; 1541459225].
val init : unit -> St (buffer 32)
let init () =
  let m = SBuffer.create #32 FStar.UInt32.zero 8  in
  SBuffer.upd m 0 (of_string "0x6a09e667");
  SBuffer.upd m 1 (of_string "0xbb67ae85");
  SBuffer.upd m 2 (of_string "0x3c6ef372");
  SBuffer.upd m 3 (of_string "0xa54ff53a");
  SBuffer.upd m 4 (of_string "0x510e527f");
  SBuffer.upd m 5 (of_string "0x9b05688c");
  SBuffer.upd m 6 (of_string "0x1f83d9ab");
  SBuffer.upd m 7 (of_string "0x5be0cd19");
  m

(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :buffer 32 { length ws = 64 }) ->
                        (k     :buffer 32 { length k = 64 /\ Disjoint k ws }) ->
                        (wh    :registers) ->
                        (block :uint32) ->
                        (t     :ref int) ->
                        (t1    :ref uint32) ->
                        (t2    :ref uint32)
                        -> ST unit
                             (requires (fun h -> Live h ws /\ Live h k))
                             (ensures  (fun h0 r h1 -> Live h1 ws /\ Live h1 k))

let rec update_inner_loop ws k wh block t t1 t2 =
  if !t < 63 then begin
    let _h = !(wh.h) in
    let _kt = index k !t in
    let v0 = _Sigma1 !(wh.e) in
    let v1 = _Ch !(wh.e) !(wh.f) !(wh.g) in
    t1 := FStar.UInt32.add _h
                           (FStar.UInt32.add _kt
                                             (FStar.UInt32.add v0 v1));
    let z0 = _Sigma0 !(wh.a) in
    let z1 = _Maj !(wh.a) !(wh.b) !(wh.c) in
    t2 := FStar.UInt32.add z0 z1;

    let _t1 = !t1 in
    let _t2 = !t2 in
    let _d = !(wh.d) in
    wh.h := !(wh.g);
    wh.g := !(wh.f);
    wh.f := !(wh.e);
    wh.e := FStar.UInt32.add _d _t1;
    wh.d := !(wh.c);
    wh.c := !(wh.b);
    wh.b := !(wh.a);
    wh.a := FStar.UInt32.add _t1 _t2;
    t := (!t + 1);
    update_inner_loop ws k wh block t t1 t2 end
  else ()

val update_step : (hash :buffer 32 { length hash = 8 }) ->
                  (pdata :buffer 8 { Disjoint hash pdata }) ->
                  (len  :nat         { length pdata = len }) ->
                  (ws   :buffer 32 { length ws = 64 /\ Disjoint ws hash /\ Disjoint ws pdata }) ->
                  (k    :buffer 32 { length k = 64 /\ Disjoint k hash /\ Disjoint k pdata /\ Disjoint k ws }) ->
                  (i    :ref int) ->
                  (t1   :ref uint32) ->
                  (t2   :ref uint32)
                  -> ST unit
                       (requires (fun h -> Live h hash
                                      /\ Live h pdata
                                      /\ Live h ws
                                      /\ Live h k))
                       (ensures  (fun h0 r h1 -> Live h1 hash
                                            /\ Live h1 pdata
                                            /\ Live h1 ws
                                            /\ Live h1 k))

let rec update_step hash pdata len ws k i t1 t2 =
  if !i < len then begin
    let pos =  (!i * 16) in
    let block = SBuffer.sub pdata pos 16 in
    (* Step 2 : Initialize the eight working variables *)
    let wh = {
      a = ref (index hash 0);
      b = ref (index hash 1);
      c = ref (index hash 2);
      d = ref (index hash 3);
      e = ref (index hash 4);
      f = ref (index hash 5);
      g = ref (index hash 6);
      h = ref (index hash 7);
    } in

    (* Step 3 : Perform logical operations on the working variables *)
    let t = ref 0 in
    let wblock = uint32_of_sbytes block in
    update_inner_loop ws k wh wblock t t1 t2;

    (* Step 4 : Compute the ith intermediate hash value *)
    let x01 = !(wh.a) in
    let x02 = index hash 0 in
    let x11 = !(wh.b) in
    let x12 = index hash 1 in
    let x21 = !(wh.c) in
    let x22 = index hash 2 in
    let x31 = !(wh.d) in
    let x32 = index hash 3 in
    let x41 = !(wh.e) in
    let x42 = index hash 4 in
    let x51 = !(wh.f) in
    let x52 = index hash 5 in
    let x61 = !(wh.g) in
    let x62 = index hash 6 in
    let x71 = !(wh.h) in
    let x72 = index hash 7 in
    SBuffer.upd hash 0 (FStar.UInt32.add x01 x02);
    SBuffer.upd hash 1 (FStar.UInt32.add x11 x12);
    SBuffer.upd hash 2 (FStar.UInt32.add x21 x22);
    SBuffer.upd hash 3 (FStar.UInt32.add x31 x32);
    SBuffer.upd hash 4 (FStar.UInt32.add x41 x42);
    SBuffer.upd hash 5 (FStar.UInt32.add x51 x52);
    SBuffer.upd hash 6 (FStar.UInt32.add x61 x62);
    SBuffer.upd hash 7 (FStar.UInt32.add x71 x72);
    i := !i + 1;
    update_step hash pdata len ws k i t1 t2 end
  else ()

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
// TODO: ensures Modifies (only hash) h0 h1
val update : (whash   :buffer 32 { length whash = 8 }) ->
             (data    :buffer 8  { Disjoint whash data }) ->
             (datalen :nat         { length data = datalen })
             -> ST unit
                  (requires (fun h -> Live h whash /\ Live h data))
                  (ensures  (fun h0 r h1 -> Live h1 whash /\ Live h1 data))

let update whash pdata len =
  (* Define working variables *)
  let i = ref 0 in
  let j = ref 0 in
  let t1 = ref FStar.UInt32.zero in
  let t2 = ref FStar.UInt32.zero in
  let tw = create #8 FStar.UInt8.zero 4 in
  (* Initialize constant *)
  let k = k_init () in
  (* Precompute schedule function *)
  let ws = create #32 FStar.UInt32.zero 64 in
  wsched ws pdata len tw i;
  (* Perform function *)
  update_step whash pdata len ws k j t1 t2

(* Compute the final value of the hash from the last hash value *)
// TODO: ensures Modifies (only hash) h0 h1
val finish: (hash  :sbytes    { length hash = 32 }) ->
            (whash :buffer 32 { Disjoint whash hash })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h whash))
                 (ensures  (fun h0 r h1 -> Live h1 hash /\ Live h1 whash))

let finish hash whash = sbytes_of_uint32s hash whash 8

(* Compute the sha256 hash of some bytes *)
// [Coq] Definition SHA_256 (str : list Z) : list Z :=
//     intlist_to_Zlist (hash_blocks init_registers (generate_and_pad str)).
// TODO: ensures Modifies (only hash) h0 h1
val sha265: (hash:sbytes { length hash = 32 }) ->
            (data:sbytes { Disjoint hash data }) ->
            (len:nat       { length data = len })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h data))
                 (ensures  (fun h0 r h1 -> Live h1 data /\ Live h1 hash))

let sha256 hash data len =
  let pdata = pad data len in
  let whash = init () in
  update whash pdata len;
  finish hash whash
