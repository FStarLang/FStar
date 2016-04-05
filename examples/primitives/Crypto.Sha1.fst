module Crypto.Sha1

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open FStar.UInt64
open FStar.UInt32



(* [FIPS 180-4] section 4.1.1 *)
val _Ch: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Ch x y z = logxor (logand x y) (logand (lognot x) z)

val _Parity: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Parity x y z = logxor x (logxor y z)

val _Maj: x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _Maj x y z = logxor (logand x y) (logxor (logand x z) (logand y z))

val _F: t:nat{t <= 79} -> x:uint32 -> y:uint32 -> z:uint32 -> Tot uint32
let _F t x y z =
  if t >= 0 && t < 20 then
    _Ch x y z
  else if t < 40 then
    _Parity x y z
  else if t < 60 then
    _Maj x y z
  else
    _Parity x y z

(* [FIPS 180-4] section 4.2.1 *)
val k_init_inner: (k :buffer 32) ->
                  (i :ref nat)
                  -> ST unit
                       (requires (fun h -> Live h k))
                       (ensures  (fun h0 r h1 -> Live h1 k))
let rec k_init_inner k i =
    if !i < 20 then begin
      SBuffer.upd k !i (of_string "0x5a827999");
      i := !i + 1;
      k_init_inner k i end
    else if !i < 40 then begin
      SBuffer.upd k !i (of_string "0x6ed9eba1");
      i := !i + 1;
      k_init_inner k i end
    else if !i < 60 then begin
      SBuffer.upd k !i (of_string "0x8f1bbcdc");
      i := !i + 1;
      k_init_inner k i end
    else if !i < 80 then begin
      SBuffer.upd k !i (of_string "0xca62c1d6");
      i := !i + 1;
      k_init_inner k i end
    else ()

val k_init: unit -> St (buffer 32)
let k_init () =
  let k = SBuffer.create #32 FStar.UInt32.zero 80  in
  k_init_inner k (ref 0);
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


(* [FIPS 180-4] section 6.1.2 *)
(* Step 1 : Scheduling function for eighty 32 bit words *)
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
  else if !t < 80 then begin
    let _t3 = index ws (!t-3) in
    let _t8 = index ws (!t-8) in
    let _t14 = index ws (!t-14) in
    let _t16 = index ws (!t-16) in

    let w = (FStar.UInt32.logxor _t3
                                 (FStar.UInt32.logxor _t8
                                                      (FStar.UInt32.logxor _t14 _t16)))
    in
    let v = FStar.UInt32.rotate_left w 1 in
    SBuffer.upd ws !t v;
    t := !t + 1;
    wsched_define ws wblock t end
  else ()


(* [FIPS 180-4] section 5.3.1 *)
(* Define the initial hash value *)

val init : (whash :buffer 32 { length whash = 5 })
           -> ST unit
                (requires (fun h -> Live h whash))
                (ensures  (fun h0 r h1 -> Live h1 whash))

let init whash =
  SBuffer.upd whash 0 (of_string "0x67452301");
  SBuffer.upd whash 1 (of_string "0xefcdab89");
  SBuffer.upd whash 2 (of_string "0x98badcfe");
  SBuffer.upd whash 3 (of_string "0x10325476");
  SBuffer.upd whash 4 (of_string "0xc3d2e1f0")


(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :buffer 32 { length ws = 80 }) ->
                        (whash :buffer 32 { length whash = 5 }) ->
                        (t     :ref int) ->
                        (t1    :buffer 32 { length t1 = 1 }) ->
                        (k     :buffer 32 { length k = 80 /\ Disjoint k ws })
                        -> ST unit
                             (requires (fun h -> Live h ws /\ Live h k))
                             (ensures  (fun h0 r h1 -> Live h1 ws /\ Live h1 k))

let rec update_inner_loop ws whash t t1 k =
  if !t < 80 then begin
    let _a = index whash 0 in
    let _b = index whash 1 in
    let _c = index whash 2 in
    let _d = index whash 3 in
    let _e = index whash 4 in

    let _rotl5 = FStar.UInt32.rotate_left _a 5 in
    let _rotl30 = FStar.UInt32.rotate_left _b 30 in
    let _ft = _F !t _b _c _d in
    let _kt = index k !t in
    let _wt = index ws !t in

    let _T = FStar.UInt32.add _rotl5
                              (FStar.UInt32.add _ft
                                                (FStar.UInt32.add _e
                                                                  (FStar.UInt32.add _kt _wt)))
    in
    SBuffer.upd whash 4 _d;
    SBuffer.upd whash 3 _c;
    SBuffer.upd whash 2 _rotl30;
    SBuffer.upd whash 1 _a;
    SBuffer.upd whash 0 _T;
    t := !t + 1;
    update_inner_loop ws whash t t1 k end
  else ()


val update_step : (whash :buffer 32 { length whash = 5 }) ->
                  (wdata :buffer 32 { Disjoint whash wdata }) ->
                  (ws    :buffer 32 { length ws = 80 /\ Disjoint ws whash /\ Disjoint ws wdata }) ->
                  (rounds :nat) ->
                  (i     :ref int) ->
                  (t1    :buffer 32 { length t1 = 1 }) ->
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

let rec update_step ihash wdata ws rounds i t1 k =
  if !i < rounds then begin
    let pos = !i * 16 in
    let wblock = SBuffer.sub wdata pos 16 in

    (* Step 1 : Scheduling function for eighty 32 bit words *)
    let ia = ref 0 in
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the five working variables *)
    let whash = create #32 FStar.UInt32.zero 5 in
    SBuffer.upd whash 0 (index ihash 0);
    SBuffer.upd whash 1 (index ihash 1);
    SBuffer.upd whash 2 (index ihash 2);
    SBuffer.upd whash 3 (index ihash 3);
    SBuffer.upd whash 4 (index ihash 4);

    (* Step 3 : Perform logical operations on the working variables *)
    let ib = ref 0 in
    update_inner_loop ws whash ib t1 k;

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
    SBuffer.upd ihash 0 (FStar.UInt32.add x01 x02);
    SBuffer.upd ihash 1 (FStar.UInt32.add x11 x12);
    SBuffer.upd ihash 2 (FStar.UInt32.add x21 x22);
    SBuffer.upd ihash 3 (FStar.UInt32.add x31 x32);
    SBuffer.upd ihash 4 (FStar.UInt32.add x41 x42);
    i := !i + 1;
    update_step ihash wdata ws rounds i t1 k end
  else ()


(* [FIPS 180-4] section 6.1.2 *)
(* Update running hash function *)
val update : (whash  :buffer 32 { length whash = 5 }) ->
             (pdata  :buffer 32 { Disjoint whash pdata }) ->
             (rounds :nat )
             -> ST unit
                  (requires (fun h -> Live h whash /\ Live h pdata))
                  (ensures  (fun h0 r h1 -> Live h1 whash /\ Live h1 pdata))

let update whash wdata rounds =
  (* Define working variables *)
  let i = ref 0 in
  let t1 = create #32 FStar.UInt32.zero 1 in
  (* Scheduling function *)
  let ws = create #32 FStar.UInt32.zero 80 in
  (* Initialize constant *)
  let k = k_init () in
  (* Perform function *)
  update_step whash wdata ws rounds i t1 k


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :sbytes    { length hash = 20 }) ->
            (whash :buffer 32 { Disjoint whash hash })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h whash))
                 (ensures  (fun h0 r h1 -> Live h1 hash /\ Live h1 whash))

let finish hash whash = be_sbytes_of_uint32s hash whash 5


(* Compute the sha1 hash of some bytes *)
val sha1: (hash:sbytes { length hash = 20 }) ->
            (data:sbytes { Disjoint hash data }) ->
            (len:nat       { length data = len })
            -> ST unit
                 (requires (fun h -> Live h hash /\ Live h data))
                 (ensures  (fun h0 r h1 -> Live h1 data /\ Live h1 hash))

let sha1 hash data len =
  let whash = create #32 FStar.UInt32.zero 5 in
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
