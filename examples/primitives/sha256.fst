module Sha256

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
val rotl: (x:ref uint32) -> (n:nat{n <= 32}) -> ST unit
  (requires (fun h -> contains h x))
  (ensures (fun h0 _ h1 -> contains h1 x
    /\ sel h1 x = UInt32.rotate_left (sel h0 x) n))
let rotl x n =
  x := UInt32.rotate_left !x n

// [Coq] Definition Rotr x n := Int.ror n (Int.repr x).
val rotr: (x:ref uint32) -> (n:nat{n <= 32}) -> ST unit
  (requires (fun h -> contains h x))
  (ensures (fun h0 _ h1 -> contains h1 x
    /\ sel h1 x = UInt32.rotate_right (sel h0 x) n))
let rotr x n =
  x := UInt32.rotate_right !x n

(* [FIPS 180-4] section 4.1.2 *)
// [Coq] Definition Ch (x y z : int) : int :=
//          Int.xor (Int.and x y) (Int.and (Int.not x) z).
val _Ch: uint32 -> uint32 -> uint32 -> Tot uint32
let _Ch x y z =
  logxor (logand x y) (logand (lognot x) z)

// [Coq] Definition Maj (x y z : int) : int :=
//          Int.xor (Int.xor (Int.and x z) (Int.and y z) ) (Int.and x y).
val _Maj: uint32 -> uint32 -> uint32 -> Tot uint32
let _Maj x y z =
  logxor (logand x y) (logxor (logand x z) (logand y z))

// [Coq] Definition Sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 2 x) (Rotr 13 x)) (Rotr 22 x).
val _Sigma0: uint32 -> Tot uint32
let _Sigma0 x =
  logxor (rotate_right x 2) (logxor (rotate_right x 13) (rotate_right x 22))

// [Coq] Definition Sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 6 x) (Rotr 11 x)) (Rotr 25 x).
val _Sigma1: uint32 -> Tot uint32
let _Sigma1 x =
  logxor (rotate_right x 6) (logxor (rotate_right x 11) (rotate_right x 25))

// [Coq] Definition sigma_0 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 7 x) (Rotr 18 x)) (Shr 3 x).
val _sigma0: uint32 -> Tot uint32
let _sigma0 x =
  logxor (rotate_right x 7) (logxor (rotate_right x 18) (shift_right x 3))

// [Coq] Definition sigma_1 (x : int) : int :=
//          Int.xor (Int.xor (Rotr 17 x) (Rotr 19 x)) (Shr 10 x).
val _sigma1: uint32 -> Tot uint32
let _sigma1 x =
  logxor (rotate_right x 17) (logxor (rotate_right x 19) (shift_right x 10))

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
  admit();
  let k = SBuffer.create #32 FStar.UInt32.zero (* (of_string "0x00000000") *) 64  in 
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
val nblocks: nat -> Tot (n:nat{ n >= 1})
let nblocks x = ((x + 8) - ((x + 8) % 64))/64 + 1

(* Create the padding and set it to the specified value *)
val pad_create: (b:buffer 8) -> len:nat -> St (pb:buffer 8{length pb >= 1 /\ length pb <= 64})
let pad_create raw len =
  (* Compute the padding length *)
  let plen =
//    let len = ByteArray.length raw in
    let len_uint64 = UInt64.of_int (len * 8) in
    if (len % 64) < 56 then 56 - (len % 64)
    else 64 + 56 - (len % 64)
  in
  let pad = create #8 zero plen in
  SBuffer.upd pad 0 (FStar.UInt8.of_string "0x80");
  pad

(* Function taking bytes and storing them in a (array uint32) *)
val store_word: (fbytes:buffer 8) ->
                (wi:buffer 8{length wi = 4 /\ Disjoint wi fbytes}) ->
                (wdata:buffer 32{Disjoint wi wdata /\ Disjoint wdata fbytes(*{FStar.Heap.Ref wdata <> FStar.Heap.Ref wi}*)}) ->
                (wmax:nat) ->
                (idxw:ref nat) ->
                (idxb:ref nat) -> ST unit
                               (requires (fun h -> length wdata = wmax
				 /\ Live h fbytes /\ Live h wi /\ Live h wdata
				 /\ FStar.Heap.contains h idxw /\ FStar.Heap.contains h idxb
				 /\ FStar.Heap.sel h idxb < length fbytes - 4)) // TODO : change with constraint on wmax
                               (ensures (fun h0 _ h1 -> Modifies (SBuffer.only wi) h0 h1
				 /\ Live h1 wi))

let rec store_word fbytes wi wdata wmax idxw idxb =
  admit(); //  TODO: proof
  if !idxw < wmax then begin
    (* Store four bytes into a temporary word (uint32) *)
    SBuffer.upd wi 0 (SBuffer.index fbytes !idxb);
    SBuffer.upd wi 1 (SBuffer.index fbytes (!idxb + 1));
    SBuffer.upd wi 2 (SBuffer.index fbytes (!idxb + 2));
    SBuffer.upd wi 3 (SBuffer.index fbytes (!idxb + 3));
    (* Store the temporary word to the final data array *)
    let h = FStar.ST.get () in
    admitP(True /\ ((FStar.Heap.sel h idxw) < wmax));
//    admit();
    SBuffer.upd wdata !idxw (uint32_of_sbytes (wi));
    idxb := !idxb + 4;
    idxw := !idxw + 1;
    let h = FStar.ST.get () in
//    admitP (True /\ (FStar.Seq.length (FStar.Heap.sel h wdata) = wmax));
    store_word fbytes wi wdata wmax idxw idxb end
  else ()

val pad: (data:buffer 8) -> len:nat -> St (buffer 32)
let pad raw len =
  admit();
  let idxw = ref 0 in
  let idxb = ref 0 in
  let wi = SBuffer.create #8 FStar.UInt8.zero 4 in
  let wmax = nblocks len in
  let wdata = SBuffer.create #32 FStar.UInt32.zero wmax in
  (* Encode the length of the raw data in 8 bytes (uint64) *)
  let lenbytes = SBuffer.create #8 FStar.UInt8.zero 8 in // TODO from: ByteArray.length_bytes 8 raw i 
  (* Generate bytes required for the padding and create the final bytes *)
  let pad_len = 16 in // TODO: fake
  let padbytes = pad_create raw pad_len in
  let lenbytes_len = 8 in // TODO: fake
  let raw_len = len in // TODO: fake
  let fbytes = create #8 FStar.UInt8.zero (lenbytes_len + len + wmax) in (* TODO: fake numbers, see below *)
  blit raw 0 fbytes 0 raw_len;
  blit padbytes 0 fbytes raw_len pad_len;
  blit lenbytes 0 fbytes (raw_len+pad_len) lenbytes_len;
//  let fbytes = (Primitives.ByteArray.append (Primitives.ByteArray.append lenbytes padbytes) raw) in
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
    FStar.UInt32.add (_sigma1 (wsched data (t-2)))
               (FStar.UInt32.add (wsched data (t-7))
                           (FStar.UInt32.add (_sigma0 (wsched data (t-15)))
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
    FStar.Array.create 8 (FStar.UInt32.of_string "0x00000000")
  in
  upd m 0 (FStar.UInt32.of_string "0x6a09e667");
  upd m 1 (FStar.UInt32.of_string "0xbb67ae85");
  upd m 2 (FStar.UInt32.of_string "0x3c6ef372");
  upd m 3 (FStar.UInt32.of_string "0xa54ff53a");
  upd m 4 (FStar.UInt32.of_string "0x510e527f");
  upd m 5 (FStar.UInt32.of_string "0x9b05688c");
  upd m 6 (FStar.UInt32.of_string "0x1f83d9ab");
  upd m 7 (FStar.UInt32.of_string "0x5be0cd19");
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
  let t1 = ref FStar.UInt32.zero in
  let t2 = ref FStar.UInt32.zero in
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
        t1 := FStar.UInt32.add !(wh.h)
                         (FStar.UInt32.add (_Sigma1 !(wh.e))
                                     (FStar.UInt32.add (_Ch !(wh.e) !(wh.f) !(wh.g))
                                                 (FStar.UInt32.add (FStar.Array.index k !t) (wsched data_block !t))));
        t2 := FStar.UInt32.add (_Sigma0 !(wh.a)) (_Maj !(wh.a) !(wh.b) !(wh.c));
        wh.h := !(wh.g);
        wh.g := !(wh.f);
        wh.f := !(wh.e);
        wh.e := FStar.UInt32.add !(wh.d) !t1;
        wh.d := !(wh.c);
        wh.c := !(wh.b);
        wh.b := !(wh.a);
        wh.a := FStar.UInt32.add !t1 !t2;
        t := (!t + 1);
        inner_loop t end
      else ()
    in inner_loop t;
    (* Step 4 : Compute the ith intermediate hash value *)
    upd hash 0 (FStar.UInt32.add !(wh.a) (FStar.Array.index hash 0));
    upd hash 1 (FStar.UInt32.add !(wh.b) (FStar.Array.index hash 1));
    upd hash 2 (FStar.UInt32.add !(wh.c) (FStar.Array.index hash 2));
    upd hash 3 (FStar.UInt32.add !(wh.d) (FStar.Array.index hash 3));
    upd hash 4 (FStar.UInt32.add !(wh.e) (FStar.Array.index hash 4));
    upd hash 5 (FStar.UInt32.add !(wh.f) (FStar.Array.index hash 5));
    upd hash 6 (FStar.UInt32.add !(wh.g) (FStar.Array.index hash 6));
    upd hash 7 (FStar.UInt32.add !(wh.h) (FStar.Array.index hash 7));
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
val sha265: (data:buffer 8) -> St (buffer 8)
let sha256 data =
  let pdata = pad data in
  let hash = init () in
  let hash = update hash pdata in
  finish hash
