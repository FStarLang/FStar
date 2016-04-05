module Crypto.Sha224

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open FStar.UInt64
open FStar.UInt32



(* [FIPS 180-4] section 4.1.2 *)
val _Ch: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Maj: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _Sigma0: x:uint32 -> Tot uint32
let _Sigma0 x = logxor (rotate_right x 2) (logxor (rotate_right x 13) (rotate_right x 22))

val _Sigma1: x:uint32 -> Tot uint32
let _Sigma1 x = logxor (rotate_right x 6) (logxor (rotate_right x 11) (rotate_right x 25))

val _sigma0: x:uint32 -> Tot uint32
let _sigma0 x = logxor (rotate_right x 7) (logxor (rotate_right x 18) (shift_right x 3))

val _sigma1: x:uint32 -> Tot uint32
let _sigma1 x = logxor (rotate_right x 17) (logxor (rotate_right x 19) (shift_right x 10))


(* [FIPS 180-4] section 4.2.2 *)

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

(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
val nblocks: nat -> Tot (n:nat{n >= 1})
let nblocks x = ((x + 8) - ((x + 8) % 64))/64 + 1


(* Compute the pad length *)
val pad_length: nat -> Tot (n:nat{n <= 64})
let pad_length rlen =
  if (rlen % 64) < 56 then 56 - (rlen % 64)
  else 64 + 56 - (rlen % 64)


(* Pad the data and return a buffer of uint32 for subsequent treatment *)
val pad: (pdata :buffer 8 ) ->
         (rdata :buffer 8 ) ->
         (rlen  :nat { length rdata = rlen })
         -> ST unit
              (requires (fun h -> Live h rdata))
              (ensures  (fun h0 r h1 -> Live h1 rdata))
// TODO: Refinement on the value of the pad -> length raw + rplen = 64
let pad pdata rdata rlen =
  // Value of the raw data length in bits represented as UInt64
  let rlen_64 =
    let v = create #8 FStar.UInt8.zero 8 in
    let v64 = FStar.UInt64.of_int (rlen * 8) in
    FStar.SBytes.be_sbytes_of_uint64 v v64;
    v
  in
  // Compute the padding length
  let rplen = pad_length rlen in
  // Generate the padding
  let rpad = create #8 zero rplen in
  SBuffer.upd rpad 0 (FStar.UInt8.of_string "0x80");
  blit rdata 0 pdata 0 rlen;
  blit rpad 0 pdata rlen rplen;
  blit rlen_64 0 pdata (rlen + rplen) 8


(* Store function to handle pdata as a sequence of words *)
val store : (wdata :buffer 32) ->
            (pdata :buffer 8 { length pdata = 4 * (length wdata) /\ Disjoint wdata pdata }) ->
            (plen  :nat        { length pdata = plen /\ plen = 4 * (length wdata) })
            -> ST unit
                 (requires (fun h -> Live h wdata /\ Live h pdata))
                 (ensures  (fun h0 r h1 -> Live h1 wdata /\ Live h1 pdata))

let store wdata pdata plen = be_uint32s_of_sbytes wdata pdata plen


(* [FIPS 180-4] section 6.2.2 *)
(* Step 1 : Scheduling function for sixty-four 32bit words *)
val wsched_define: (ws     :buffer 32 { length ws = 64 }) ->
                   (wblock :buffer 32 { length wblock = 16 /\ Disjoint ws wblock }) ->
                   (t      :ref nat)
                   -> ST unit
                        (requires (fun h -> Live h ws /\ Live h wblock))
                        (ensures  (fun h0 r h1 -> Live h1 ws /\ Live h1 wblock))

let rec wsched_define ws wblock t =
  if !t >= 0 && !t < 16 then begin
    SBuffer.upd ws !t (index wblock !t);
    t := !t + 1;
    wsched_define ws wblock t end
  else if !t < 64 then begin
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
    t := !t + 1;
    wsched_define ws wblock t end
  else ()


(* [FIPS 180-4] section 5.3.3 *)
(* Define the initial hash value *)

val init : (whash :buffer 32 { length whash = 8 })
           -> ST unit
                (requires (fun h -> Live h whash))
                (ensures  (fun h0 r h1 -> Live h1 whash))

let init whash =
  SBuffer.upd whash 0 (of_string "0xc1059ed8");
  SBuffer.upd whash 1 (of_string "0x367cd507");
  SBuffer.upd whash 2 (of_string "0x3070dd17");
  SBuffer.upd whash 3 (of_string "0xf70e5939");
  SBuffer.upd whash 4 (of_string "0xffc00b31");
  SBuffer.upd whash 5 (of_string "0x68581511");
  SBuffer.upd whash 6 (of_string "0x64f98fa7");
  SBuffer.upd whash 7 (of_string "0xbefa4fa4")


(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :buffer 32 { length ws = 64 }) ->
                        (whash :buffer 32 { length whash = 8 }) ->
                        (t     :ref int) ->
                        (t1    :buffer 32 { length t1 = 1 }) ->
                        (t2    :buffer 32 { length t2 = 1 }) ->
                        (k     :buffer 32 { length k = 64 /\ Disjoint k ws })
                        -> ST unit
                             (requires (fun h -> Live h ws /\ Live h k))
                             (ensures  (fun h0 r h1 -> Live h1 ws /\ Live h1 k))

let rec update_inner_loop ws whash t t1 t2 k =
  if !t < 64 then begin
    let _h = index whash 7 in
    let _kt = index k !t in
    let _wt = index ws !t in
    let v0 = _Sigma1 (index whash 4) in
    let v1 = _Ch (index whash 4) (index whash 5) (index whash 6) in
    let _t1 = FStar.UInt32.add _h
                               (FStar.UInt32.add v0
                                                 (FStar.UInt32.add v1
                                                                   (FStar.UInt32.add _kt _wt))) in
    SBuffer.upd t1 0 _t1;
    let z0 = _Sigma0 (index whash 0) in
    let z1 = _Maj (index whash 0) (index whash 1) (index whash 2) in

    let _t2 = FStar.UInt32.add z0 z1 in
    SBuffer.upd t2 0 _t2;

    let _d = (index whash 3) in
    SBuffer.upd whash 7 (index whash 6);
    SBuffer.upd whash 6 (index whash 5);
    SBuffer.upd whash 5 (index whash 4);
    SBuffer.upd whash 4 (FStar.UInt32.add _d _t1);
    SBuffer.upd whash 3 (index whash 2);
    SBuffer.upd whash 2 (index whash 1);
    SBuffer.upd whash 1 (index whash 0);
    SBuffer.upd whash 0 (FStar.UInt32.add _t1 _t2);
    t := !t + 1;
    update_inner_loop ws whash t t1 t2 k end
  else ()


val update_step : (whash :buffer 32 { length whash = 8 }) ->
                  (wdata :buffer 32 { Disjoint whash wdata }) ->
                  (ws    :buffer 32 { length ws = 64 /\ Disjoint ws whash /\ Disjoint ws wdata }) ->
                  (rounds :nat) ->
                  (i     :ref int) ->
                  (t1    :buffer 32 { length t1 = 1 }) ->
                  (t2    :buffer 32 { length t2 = 1 }) ->
                  (k     :buffer 32 { length k = 64 /\ Disjoint k whash /\ Disjoint k wdata /\ Disjoint k ws })
                  -> ST unit
                       (requires (fun h -> Live h whash
                                      /\ Live h wdata
                                      /\ Live h ws
                                      /\ Live h k))
                       (ensures  (fun h0 r h1 -> Live h1 whash
                                            /\ Live h1 wdata
                                            /\ Live h1 ws
                                            /\ Live h1 k))

let rec update_step ihash wdata ws rounds i t1 t2 k =
  if !i < rounds then begin
    let pos = !i * 16 in
    let wblock = SBuffer.sub wdata pos 16 in

    (* Step 1 : Scheduling function for sixty-four 32 bit words *)
    let ia = ref 0 in
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the eight working variables *)
    let whash = create #32 FStar.UInt32.zero 8 in
    SBuffer.upd whash 0 (index ihash 0);
    SBuffer.upd whash 1 (index ihash 1);
    SBuffer.upd whash 2 (index ihash 2);
    SBuffer.upd whash 3 (index ihash 3);
    SBuffer.upd whash 4 (index ihash 4);
    SBuffer.upd whash 5 (index ihash 5);
    SBuffer.upd whash 6 (index ihash 6);
    SBuffer.upd whash 7 (index ihash 7);

    (* Step 3 : Perform logical operations on the working variables *)
    let ib = ref 0 in
    update_inner_loop ws whash ib t1 t2 k;

    (* Step 4 : Compute the ith intermediate hash value *)
    let x01 = index whash 0 in
    let x02 = index ihash 0 in
    let x11 = index whash 1 in
    let x12 = index ihash 1 in
    let x21 = index whash 2 in
    let x22 = index ihash 2 in
    let x31 = index whash 3 in
    let x32 = index ihash 3 in
    let x41 = index whash 4 in
    let x42 = index ihash 4 in
    let x51 = index whash 5 in
    let x52 = index ihash 5 in
    let x61 = index whash 6 in
    let x62 = index ihash 6 in
    let x71 = index whash 7 in
    let x72 = index ihash 7 in
    SBuffer.upd ihash 0 (FStar.UInt32.add x01 x02);
    SBuffer.upd ihash 1 (FStar.UInt32.add x11 x12);
    SBuffer.upd ihash 2 (FStar.UInt32.add x21 x22);
    SBuffer.upd ihash 3 (FStar.UInt32.add x31 x32);
    SBuffer.upd ihash 4 (FStar.UInt32.add x41 x42);
    SBuffer.upd ihash 5 (FStar.UInt32.add x51 x52);
    SBuffer.upd ihash 6 (FStar.UInt32.add x61 x62);
    SBuffer.upd ihash 7 (FStar.UInt32.add x71 x72);
    i := !i + 1;
    update_step ihash wdata ws rounds i t1 t2 k end
  else ()


(* [FIPS 180-4] section 6.2.2 *)
(* Update running hash function *)
val update : (whash  :buffer 32 { length whash = 8 }) ->
             (pdata  :buffer 32 { Disjoint whash pdata }) ->
             (rounds :nat )
             -> ST unit
                  (requires (fun h -> Live h whash /\ Live h pdata))
                  (ensures  (fun h0 r h1 -> Live h1 whash /\ Live h1 pdata))

let update whash wdata rounds =
  (* Define working variables *)
  let i = ref 0 in
  let t1 = create #32 FStar.UInt32.zero 1 in
  let t2 = create #32 FStar.UInt32.zero 1 in
  (* Scheduling function *)
  let ws = create #32 FStar.UInt32.zero 64 in
  (* Initialize constant *)
  let k = k_init () in
  (* Perform function *)
  update_step whash wdata ws rounds i t1 t2 k


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :sbytes    { length hash = 28 }) ->
            (whash :buffer 32 { Disjoint whash hash })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h whash))
                 (ensures  (fun h0 r h1 -> Live h1 hash /\ Live h1 whash))

let finish hash whash = be_sbytes_of_uint32s hash whash 7


(* Compute the sha224 hash of some bytes *)
val sha224: (hash:sbytes { length hash = 28 }) ->
            (data:sbytes { Disjoint hash data }) ->
            (len:nat       { length data = len })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h data))
                 (ensures  (fun h0 r h1 -> Live h1 data /\ Live h1 hash))

let sha224 hash data len =
  let whash = create #32 FStar.UInt32.zero 8 in
  let plen = len + (pad_length len) + 8 in
  let rounds = nblocks plen - 1 in
  let pdata = create #8 FStar.UInt8.zero plen in
  let wlen = plen/4 in
  let wdata = create #32 FStar.UInt32.zero wlen in

  init whash;
  pad pdata data len;
  store wdata pdata plen;
  update whash wdata rounds;
  finish hash whash
