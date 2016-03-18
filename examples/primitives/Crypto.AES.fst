module Crypto.AES

open FStar.Ghost
open FStar.Heap
open Sint
open FStar.UInt8
open FStar.SBytes
open SBuffer

// Parameters for AES-256
let nk = 8
let nb = 4
let nr = 14

val xtime: b:uint8 -> Tot uint8 
let xtime b = 
  (b ^<< 1) ^^ (((b ^>> 7) ^& one) ^*% FStar.UInt8.of_string "0x1b")

val multiply: a:uint8 -> b:uint8 -> Tot uint8
let multiply a b =
  b ^^ (a ^& one)
  ^^ (xtime b ^*% ((a ^>> 1) ^& one))
  ^^ (xtime (xtime b) ^*% ((a ^>> 2) ^& one))
  ^^ (xtime (xtime (xtime b)) ^*% ((a ^>> 3) ^& one))
  ^^ (xtime (xtime (xtime (xtime b))) ^*% ((a ^>> 4) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime b)))) ^*% ((a ^>> 5) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime b))))) ^*% ((a ^>> 6) ^& one))
  ^^ (xtime (xtime (xtime (xtime (xtime (xtime (xtime (xtime b))))))) ^*% ((a ^>> 7) ^& one))

// Code taken from http://www.literatecode.com/get/aes256.c
// and made constant time
val alog_aux: x:uint8 -> y:uint8 -> mask:uint8 -> ctr:nat{ctr <= 256} -> Tot uint8 (decreases (256 - ctr))
let rec alog_aux x y mask ctr =
  match ctr with
  | 256 -> y
  | _ -> 
    let mask = lognot(gte (of_int ctr) x) in
    let y = y ^^ (xtime(y) ^& mask) in
    alog_aux x y mask (ctr+1)

val alog: x:uint8 -> Tot uint8
let alog x =
  let y = one in
  let mask = zero in
  alog_aux x y mask 0

val log_aux: x:uint8 -> y:uint8 -> j:uint8 -> mask:uint8 -> ctr:nat{ctr <= 256} -> Tot uint8 (decreases (256 - ctr))
let rec log_aux x y j mask ctr =
  match ctr with
  | 256 -> j
  | _ ->
    let j = j ^+% (one ^& mask) in
    let y = y ^^ xtime y in
    let mask = mask ^& (lognot (eq x y)) in
    log_aux x y j mask (ctr+1)

val log: uint8 -> Tot uint8
let log x =
  let y = one in
  let j = zero in
  let mask = lognot(eq x zero) in
  log_aux x y j mask 0

val inverse: uint8 -> Tot uint8 
let inverse x = (lognot (eq x zero)) ^& (alog (of_int 255 ^-% log x))

val subBytes_: uint8 -> St uint8
let subBytes_ x =
  admit();
  let b = inverse x in
  let b4 = rotate_left b 4 in
  let b5 = rotate_left b 5 in
  let b6 = rotate_left b 6 in
  let b7 = rotate_left b 7 in
  b ^^ b4 ^^ b5 ^^ b6 ^^ b7 ^^ of_int 0x63

val subBytes_aux: state:uint8s -> ctr:nat -> St unit
let rec subBytes_aux state ctr =
  admit();
  let n = 4 * nb in
  match ctr with
  | n -> ()
  | _ ->
    let si = index state ctr in
    let si' = subBytes_ si in
    upd state ctr si';
    subBytes_aux state (ctr+1);
    ()

val subBytes: state:uint8s -> St unit
let subBytes state = 
  admit();
  subBytes_aux state 0

val shiftRows: state:uint8s{length state = 16} -> St unit
let shiftRows state =
  admit();
  let i = 1 in
  let tmp = index state i in
  upd state i      (index state (i+4)); 
  upd state (i+4)  (index state (i+8)); 
  upd state (i+8)  (index state (i+12)); 
  upd state (i+12) tmp;
  let i = 2 in
  let tmp = index state i in
  upd state i      (index state (i+8)); 
  upd state (i+4)  (index state (i+12)); 
  upd state (i+8)  tmp; 
  upd state (i+12) (index state (i+4));
  let i = 3 in
  let tmp = index state i in
  upd state i      (index state (i+12)); 
  upd state (i+4)  tmp; 
  upd state (i+8)  (index state (i+4)); 
  upd state (i+12) (index state (i+8));
  ()

val multiply_2: uint8 -> uint8 -> Tot uint8 
let multiply_2 x y =
  (((y ^& one) ^*% x) 
  ^^ (((y ^>> 1) ^& one) ^*% xtime(x))
  ^^ (((y ^>> 2) ^& one) ^*% xtime(xtime(x)))
  ^^ (((y ^>> 3) ^& one) ^*% xtime(xtime(xtime(x)))))
       
val mixColumns: uint8s -> St unit
let mixColumns state =
  admit();
  let c = 0 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state 0 (multiply_2 (of_int 0x2) s0 ^^ multiply_2 (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state 0 (multiply_2 (of_int 0x2) s1 ^^ multiply_2 (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state 0 (multiply_2 (of_int 0x2) s2 ^^ multiply_2 (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state 0 (multiply_2 (of_int 0x2) s3 ^^ multiply_2 (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 1 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state 0 (multiply_2 (of_int 0x2) s0 ^^ multiply_2 (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state 0 (multiply_2 (of_int 0x2) s1 ^^ multiply_2 (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state 0 (multiply_2 (of_int 0x2) s2 ^^ multiply_2 (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state 0 (multiply_2 (of_int 0x2) s3 ^^ multiply_2 (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 2 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state 0 (multiply_2 (of_int 0x2) s0 ^^ multiply_2 (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state 0 (multiply_2 (of_int 0x2) s1 ^^ multiply_2 (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state 0 (multiply_2 (of_int 0x2) s2 ^^ multiply_2 (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state 0 (multiply_2 (of_int 0x2) s3 ^^ multiply_2 (of_int 0x3) s0 ^^ s1 ^^ s2);
  let c = 3 in
  let s0 = index state (0+4*c) in
  let s1 = index state (1+4*c) in
  let s2 = index state (2+4*c) in
  let s3 = index state (3+4*c) in
  upd state 0 (multiply_2 (of_int 0x2) s0 ^^ multiply_2 (of_int 0x3) s1 ^^ s2 ^^ s3);
  upd state 0 (multiply_2 (of_int 0x2) s1 ^^ multiply_2 (of_int 0x3) s2 ^^ s3 ^^ s0);
  upd state 0 (multiply_2 (of_int 0x2) s2 ^^ multiply_2 (of_int 0x3) s3 ^^ s0 ^^ s1);
  upd state 0 (multiply_2 (of_int 0x2) s3 ^^ multiply_2 (of_int 0x3) s0 ^^ s1 ^^ s2);
  ()

val addRoundKey: uint8s -> uint8s -> nat -> St unit
let addRoundKey state w round =
  admit();
  let c = 0 in
  let s0 = index state (c+0) in
  let s1 = index state (c+4) in
  let s2 = index state (c+8) in
  let s3 = index state (c+12) in
  let w0 = index w (round*nb+4*c+0) in
  let w1 = index w (round*nb+4*c+1) in
  let w2 = index w (round*nb+4*c+2) in
  let w3 = index w (round*nb+4*c+3) in
  upd state (c+0) (s0 ^^ w0);
  upd state (c+1) (s1 ^^ w1);
  upd state (c+2) (s2 ^^ w2);
  upd state (c+3) (s3 ^^ w3);
  let c = 1 in
  let s0 = index state (c+0) in
  let s1 = index state (c+4) in
  let s2 = index state (c+8) in
  let s3 = index state (c+12) in
  let w0 = index w (round*nb+4*c+0) in
  let w1 = index w (round*nb+4*c+1) in
  let w2 = index w (round*nb+4*c+2) in
  let w3 = index w (round*nb+4*c+3) in
  upd state (c+0) (s0 ^^ w0);
  upd state (c+1) (s1 ^^ w1);
  upd state (c+2) (s2 ^^ w2);
  upd state (c+3) (s3 ^^ w3);
  let c = 2 in
  let s0 = index state (c+0) in
  let s1 = index state (c+4) in
  let s2 = index state (c+8) in
  let s3 = index state (c+12) in
  let w0 = index w (round*nb+4*c+0) in
  let w1 = index w (round*nb+4*c+1) in
  let w2 = index w (round*nb+4*c+2) in
  let w3 = index w (round*nb+4*c+3) in
  upd state (c+0) (s0 ^^ w0);
  upd state (c+1) (s1 ^^ w1);
  upd state (c+2) (s2 ^^ w2);
  upd state (c+3) (s3 ^^ w3);
  let c = 3 in
  let s0 = index state (c+0) in
  let s1 = index state (c+4) in
  let s2 = index state (c+8) in
  let s3 = index state (c+12) in
  let w0 = index w (round*nb+4*c+0) in
  let w1 = index w (round*nb+4*c+1) in
  let w2 = index w (round*nb+4*c+2) in
  let w3 = index w (round*nb+4*c+3) in
  upd state (c+0) (s0 ^^ w0);
  upd state (c+1) (s1 ^^ w1);
  upd state (c+2) (s2 ^^ w2);
  upd state (c+3) (s3 ^^ w3);
  ()

val cipher_loop: state:uint8s -> w:uint8s -> round:nat -> St unit
let rec cipher_loop state w round = 
  admit();
  match round with
  | nr -> ()
  | _ -> 
    subBytes state;
    shiftRows state;
    mixColumns state;
    addRoundKey state w round; 
    cipher_loop state w (round+1);
    ()

val cipher: out:uint8s{length out = 4 * nb} -> input:uint8s{length input = 4*nb} -> w:uint8s{length w = 4 * (nr+1)} -> St unit
let cipher out input w =
  admit();
  let state = create #8 FStar.UInt8.zero (4*nb) in
  blit input 0 state 0 (4*nb);
  addRoundKey state w 0;
  cipher_loop state w 1;
  subBytes state;
  shiftRows state;
  addRoundKey state w nr;
  blit state 0 out 0 (4*nb);
  ()

val rotWord: word:uint8s{length word = 4} -> St unit
let rotWord word =
  admit();
  let w0 = index word 0 in
  let w1 = index word 1 in
  let w2 = index word 2 in
  let w3 = index word 3 in
  upd word 0 w1;
  upd word 1 w2;
  upd word 2 w3;
  upd word 3 w0;
  ()
  
val subWord: word:uint8s{length word = 4} -> St unit
let subWord word =
  admit();
  let w0 = index word 0 in
  let w1 = index word 1 in
  let w2 = index word 2 in
  let w3 = index word 3 in
  upd word 0 (subBytes_ w0);
  upd word 1 (subBytes_ w1);
  upd word 2 (subBytes_ w2);
  upd word 3 (subBytes_ w3);
  ()  

val rcon: nat -> uint8 -> Tot uint8
let rec rcon i tmp =
  admit();
  match i with
  | 0 -> tmp
  | _ ->
    let tmp = multiply (of_int 0x2) tmp in
    rcon (i-1) tmp

val keyExpansion_aux: uint8s -> uint8s -> uint8s -> nat -> St unit
let rec keyExpansion_aux key w temp i =
  admit();
  let max = 4 * nb * (nr+1) in
  match i with
  | max -> ()
  | _ ->
    blit temp 0 w (i-4) 4;
    if (i/4) % nk = 0 then (
      rotWord temp;
      subWord temp;
      upd temp 0 (index temp 0 ^^ rcon ((i/4)/nk) one) 
    ) else if ((i/4) % nk = 4) then (
      subWord(temp)
    );
    let w0 = index w (i+0-4*nk) in
    let w1 = index w (i+1-4*nk) in
    let w2 = index w (i+2-4*nk) in
    let w3 = index w (i+3-4*nk) in
    let t0 = index temp (0) in
    let t1 = index temp (1) in
    let t2 = index temp (2) in
    let t3 = index temp (3) in
    upd w (i+0) (t0 ^^ w0);
    upd w (i+1) (t1 ^^ w1);
    upd w (i+2) (t2 ^^ w2);
    upd w (i+3) (t3 ^^ w3);
    keyExpansion_aux key w temp (i+4);
    ()
    
val keyExpansion: key:uint8s{length key = 4 * nk} -> w:uint8s{length w = 4 * (nb * (nr+1))} -> St unit
let keyExpansion key w =
  admit();
  let temp = create #8 zero 4 in
  blit key 0 w 0 (4*nk);
  let i = 4 * nk in
  keyExpansion_aux key w temp i;
  ()

(*
val invMixColumns: unit -> St unit

val invShiftRows: unit -> St unit

val invSubBytes: unit -> St unit


  
