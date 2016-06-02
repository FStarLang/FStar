module Crypto.Sha256

open FStar.Heap
open SBytes
open SBuffer
open SInt.UInt8
open SInt.UInt64
open SInt.UInt32




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

val k_init: k:buffer 32{ length k = 64 } -> ST unit
                                             (requires (fun h -> live h k))
                                             (ensures  (fun h0 _ h1 -> live h1 k))

let k_init k =
  admit();
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
  SBuffer.upd k 63 (of_string "0xc67178f2")


(* [FIPS 180-4] section 5.1.1 *)

(* Compute the number of 512 bit blocks to store data (56 bytes) and padding (8 bytes) *)
(* l + 1 + k ≡ 448 mod 512 *)
val nblocks: nat -> Tot (n:nat{n >= 1})
let nblocks x = ((x + 8) - ((x + 8) % 64))/64 + 1

(* Compute the pad length *)
// TODO: Refinement on the value of the pad -> length raw + rplen = 64
val pad_length: rl:nat -> Tot (pl:nat{ pl <= 64 })
let pad_length rl =
  if (rl % 64) < 56 then 56 - (rl % 64)
  else 64 + 56 - (rl % 64)

#reset-options "--z3timeout 20"

(* Pad the data and return a buffer of uint32 for subsequent treatment *)
val pad: (pdata :sbytes ) ->
         (rdata :sbytes {disjoint pdata rdata} ) ->
         (rlen  :nat { length rdata = rlen /\ length pdata >= rlen + (pad_length rlen) + 8})
         -> ST unit
              (requires (fun h -> live h pdata /\ live h rdata))
              (ensures  (fun h0 r h1 -> live h1 pdata 
                                   /\ live h1 rdata 
                                   /\ modifies_buf (only pdata) h0 h1))

let pad pdata rdata rlen =
  let h0 = ST.get () in
  // Value of the raw data length in bits represented as UInt64
  let rlen_64 =
    let v = create #8 SInt.UInt8.zero 8 in
    assume (Prims.op_Multiply rlen 8 < IntLib.pow2 64);
    let v64 = SInt.UInt64.of_int (Prims.op_Multiply rlen 8) in
    SBytes.be_sbytes_of_uint64 v v64;
    v
  in
  // Compute the padding length
  let rplen = pad_length rlen in
  // Generate the padding
  let rpad = create #8 SInt.UInt8.zero rplen in
  SBuffer.upd rpad 0 (SInt.UInt8.of_string "0x80");
  blit rdata 0 pdata 0 rlen;
  blit rpad 0 pdata rlen rplen;
  blit rlen_64 0 pdata (rlen + rplen) 8;
  let h1 = ST.get () in
  eq_lemma h0 h1 rdata (SBuffer.only pdata)

#reset-options

(* Store function to handle pdata as a sequence of words *)
val store : (wdata :buffer 32) ->
            (pdata :sbytes { disjoint wdata pdata }) ->
            (plen  :nat      { length pdata = plen })
            -> ST unit
                 (requires (fun h -> live h wdata /\ live h pdata))
                 (ensures  (fun h0 r h1 -> live h1 wdata /\ live h1 pdata))

let store wdata pdata plen = 
  assume (Prims.op_Multiply 4 plen <= length pdata);
  be_uint32s_of_sbytes wdata pdata plen

(* [FIPS 180-4] section 6.2.2 *)

#reset-options "--z3timeout 20"

(* Step 1 : Scheduling function for sixty-four 32bit words *)
val wsched_define: (ws     :buffer 32 { length ws = 64 }) ->
                   (wblock :buffer 32 { length wblock = 16 /\ disjoint ws wblock }) ->
                   (t      :ref nat)
                   -> ST unit
                        (requires (fun h -> live h ws /\ live h wblock))
                        (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 wblock))

let rec wsched_define ws wblock t =
  admit();
  let h = ST.get() in 
  assume (Heap.sel h t < 64);
  if !t < 16 then begin
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
//    assume (SInt.UInt32.of_int v1 >= 0);
//    assume (SInt.UInt32.of_int v1 < SInt.UInt32.n);
//    assume ((SInt.UInt32.of_int v1) + (SInt.UInt32.of_int _t16) <  (IntLib.pow2 32));
    let z1 = SInt.UInt32.add v1 _t16 in
    let z2 = SInt.UInt32.add _t7 z1 in
    let v = SInt.UInt32.add v0 z2 in
    SBuffer.upd ws !t v;
    t := !t + 1;
    wsched_define ws wblock t end
  else ()

#reset-options

(* [FIPS 180-4] section 5.3.3 *)

(* Define the initial hash value *)
val init : (whash :buffer 32 { length whash = 8 })
           -> ST unit
                (requires (fun h -> live h whash))
                (ensures  (fun h0 r h1 -> live h1 whash))

let init whash =
  SBuffer.upd whash 0 (of_string "0x6a09e667");
  SBuffer.upd whash 1 (of_string "0xbb67ae85");
  SBuffer.upd whash 2 (of_string "0x3c6ef372");
  SBuffer.upd whash 3 (of_string "0xa54ff53a");
  SBuffer.upd whash 4 (of_string "0x510e527f");
  SBuffer.upd whash 5 (of_string "0x9b05688c");
  SBuffer.upd whash 6 (of_string "0x1f83d9ab");
  SBuffer.upd whash 7 (of_string "0x5be0cd19")


(* Step 3 : Perform logical operations on the working variables *)
val update_inner_loop : (ws    :buffer 32 { length ws = 64 }) ->
                        (whash :buffer 32 { length whash = 8 /\ disjoint whash ws}) ->
                        (t     :ref int) ->
                        (t1    :buffer 32 { length t1 = 1 /\ disjoint t1 ws /\ disjoint t1 whash }) ->
                        (t2    :buffer 32 { length t2 = 1 /\ disjoint t2 ws /\ disjoint t2 whash /\ disjoint t2 t1}) ->
                        (k     :buffer 32 { length k = 64 /\ disjoint k ws /\ disjoint k whash /\ disjoint k t1 /\ disjoint k t2})
                        -> ST unit
                             (requires (fun h -> live h ws /\ live h whash /\ live h t1 /\ live h t2 /\ live h k))
                             (ensures  (fun h0 r h1 -> live h1 ws /\ live h1 whash /\ live h1 t1 /\ live h1 t2 /\ live h1 k))

let rec update_inner_loop ws whash t t1 t2 k =
  admit();
  let h0 = ST.get() in
  assume (Heap.sel h0 t < 64);
  assume (Heap.sel h0 t < length k);
  if !t < 64 then begin
    let _h = index whash 7 in
    let _kt = index k !t in
    let _wt = index ws !t in
    let v0 = _Sigma1 (index whash 4) in
    let v1 = _Ch (index whash 4) (index whash 5) (index whash 6) in
    let _t1 = SInt.UInt32.add _h
                               (SInt.UInt32.add v0
                                                 (SInt.UInt32.add v1
                                                                   (SInt.UInt32.add _kt _wt))) in
    SBuffer.upd t1 0 _t1;
    let z0 = _Sigma0 (index whash 0) in
    let z1 = _Maj (index whash 0) (index whash 1) (index whash 2) in

    let _t2 = SInt.UInt32.add z0 z1 in
    SBuffer.upd t2 0 _t2;

    let _d = (index whash 3) in
    SBuffer.upd whash 7 (index whash 6);
    SBuffer.upd whash 6 (index whash 5);
    SBuffer.upd whash 5 (index whash 4);
    SBuffer.upd whash 4 (SInt.UInt32.add _d _t1);
    SBuffer.upd whash 3 (index whash 2);
    SBuffer.upd whash 2 (index whash 1);
    SBuffer.upd whash 1 (index whash 0);
    SBuffer.upd whash 0 (SInt.UInt32.add _t1 _t2);
    t := !t + 1;
    update_inner_loop ws whash t t1 t2 k end
  else ()

#reset-options "--z3timeout 20"

val update_step : (whash :buffer 32 { length whash = 8 }) ->
                  (wdata :buffer 32 { disjoint wdata whash }) ->
                  (ws    :buffer 32 { length ws = 64 /\ disjoint ws whash /\ disjoint ws wdata }) ->
                  (rounds :nat) ->
                  (i     :ref int) ->
                  (t1    :buffer 32 { length t1 = 1 
                                      /\ disjoint t1 whash /\ disjoint t1 wdata /\ disjoint t1 ws }) ->
                  (t2    :buffer 32 { length t2 = 1 
                                      /\ disjoint t2 whash /\ disjoint t2 wdata /\ disjoint t2 ws /\ disjoint t2 t1}) ->
                  (k     :buffer 32 { length k = 64 
                                      /\ disjoint k whash /\ disjoint k wdata /\ disjoint k ws /\ disjoint k t1 /\ disjoint k t2 })
                  -> ST unit
                       (requires (fun h -> live h whash
                                      /\ live h wdata
                                      /\ live h ws
                                      /\ live h t1
                                      /\ live h t2
                                      /\ live h k))
                       (ensures  (fun h0 r h1 -> live h1 whash
                                            /\ live h1 wdata
                                            /\ live h1 ws
                                            /\ live h1 t1
                                            /\ live h1 t2
                                            /\ live h1 k))

let rec update_step ihash wdata ws rounds i t1 t2 k =
  let h0 = ST.get() in
  assume (Heap.sel h0 i >= 0);
  assume (Heap.sel h0 i < rounds);
  if !i < rounds then begin
    let pos = Prims.op_Multiply !i 16 in
    assume (Prims.op_Addition pos 16 <= SBuffer.length wdata);
    let wblock = SBuffer.sub wdata pos 16 in

    (* Step 1 : Scheduling function for sixty-four 32 bit words *)
    let ia = ST.alloc 0 in
    assert (length wblock = 16);
    assume (disjoint ws wblock);
    wsched_define ws wblock ia;

    (* Step 2 : Initialize the eight working variables *)
    let whash = create #32 SInt.UInt32.zero 8 in
    assume (length ihash = 8);
    let p0 = 0 in
    assume (p0 < SBuffer.length ihash);
    admit();
    let g0 = index ihash p0 in
    SBuffer.upd whash 0 g0;
    SBuffer.upd whash 1 (index ihash 1);
    SBuffer.upd whash 2 (index ihash 2);
    SBuffer.upd whash 3 (index ihash 3);
    SBuffer.upd whash 4 (index ihash 4);
    SBuffer.upd whash 5 (index ihash 5);
    SBuffer.upd whash 6 (index ihash 6);
    SBuffer.upd whash 7 (index ihash 7);

    (* Step 3 : Perform logical operations on the working variables *)
    let ib = ST.alloc 0 in
    assume (length t1 = 1 /\ disjoint t1 ws /\ disjoint t1 ihash);
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
    SBuffer.upd ihash 0 (SInt.UInt32.add x01 x02);
    SBuffer.upd ihash 1 (SInt.UInt32.add x11 x12);
    SBuffer.upd ihash 2 (SInt.UInt32.add x21 x22);
    SBuffer.upd ihash 3 (SInt.UInt32.add x31 x32);
    SBuffer.upd ihash 4 (SInt.UInt32.add x41 x42);
    SBuffer.upd ihash 5 (SInt.UInt32.add x51 x52);
    SBuffer.upd ihash 6 (SInt.UInt32.add x61 x62);
    SBuffer.upd ihash 7 (SInt.UInt32.add x71 x72);
    i := !i + 1;
    update_step ihash wdata ws rounds i t1 t2 k end
  else ()


(* [FIPS 180-4] section 6.2.2 *)

(* Update running hash function *)
val update : (whash  :buffer 32 { length whash = 8 }) ->
             (pdata  :buffer 32 { disjoint whash pdata }) ->
             (rounds :nat )
             -> ST unit
                  (requires (fun h -> live h whash /\ live h pdata))
                  (ensures  (fun h0 r h1 -> live h1 whash /\ live h1 pdata))

let update whash wdata rounds =
  let h0 = ST.get () in
  assert (live h0 whash /\ live h0 wdata);
  (* Define working variables *)
  let i = ST.alloc 0 in
  
  let t1 = create #32 SInt.UInt32.zero 1 in
  assert (length t1 = 1 /\ disjoint t1 whash /\ disjoint t1 wdata);
  let h1 = ST.get () in
  assert (live h1 t1);
  
  let t2 = create #32 SInt.UInt32.zero 1 in
  assert (length t2 = 1 /\ disjoint t2 whash /\ disjoint t2 wdata /\ disjoint t2 t1);
  let h2 = ST.get () in
  assert (live h2 t2);
  
  (* Scheduling function *)
  let ws = create #32 SInt.UInt32.zero 64 in
  assert (length ws = 64 /\ disjoint ws whash /\ disjoint ws wdata /\ disjoint ws t1 /\ disjoint ws t2);
  let h3 = ST.get () in
  assert (live h3 ws);

  (* Initialize constant *)
  let k = SBuffer.create #32 SInt.UInt32.zero 64 in
  k_init k;
  assert (length k = 64 /\ disjoint k whash /\ disjoint k wdata /\ disjoint k t1 /\ disjoint k t2 /\ disjoint k ws);
  let h4 = ST.get () in
  assert (live h4 k);

  (* Perform function *)
  admit();
  update_step whash wdata ws rounds i t1 t2 k;
  let h1 = ST.get() in
  assume (live h1 whash /\ live h1 wdata)


(* Compute the final value of the hash from the last hash value *)
val finish: (hash  :sbytes    { length hash = 32 }) ->
            (whash :buffer 32 { disjoint whash hash })
            -> ST unit
                 (requires (fun h -> live h hash /\ live h whash))
                 (ensures  (fun h0 r h1 -> live h1 hash /\ live h1 whash))

let finish hash whash = 
  assume (8 <= length whash /\ (Prims.op_Multiply 4 8) <= length hash);
  be_sbytes_of_uint32s hash whash 8


(* Compute the sha256 hash of some bytes *)
val sha265: (hash:sbytes { length hash = 32 }) ->
            (data:sbytes { disjoint hash data }) ->
            (len:nat       { length data = len })
            -> ST unit
                 (requires (fun h -> live h hash /\ live h data))
                 (ensures  (fun h0 r h1 -> live h1 data /\ live h1 hash))

let sha256 hash data len =
  let whash = create #32 SInt.UInt32.zero 8 in
  let plen = len + (pad_length len) + 8 in
  let rounds = nblocks plen - 1 in
  let pdata = create #8 SInt.UInt8.zero plen in
  let wlen = plen/4 in
  let wdata = create #32 SInt.UInt32.zero wlen in
  init whash;
  pad pdata data len;
  store wdata pdata plen;
  update whash wdata rounds;
  finish hash whash
