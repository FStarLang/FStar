module Crypto.HMAC.Sha384

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open Crypto.Sha384



(* Define parameters *)
let hash = sha384
let hl = 40
let bl = 128

(* Define a function to wrap the key length after bl bits *)
val wrap_key : (key    :sbytes) ->
               (keylen :nat { length key = keylen })
               -> St (okey:sbytes { length okey <= bl } * okeylen: nat)

let wrap_key key keylen =
  if keylen > bl then
    let nkey = create #8 FStar.UInt8.zero hl in
    hash nkey key keylen;
    nkey,hl
  else
    key,keylen


(* Define the main function *)
val hmac_sha384 : (mac     :sbytes { length mac = hl }) ->
                  (key     :sbytes { Disjoint key mac }) ->
                  (keylen  :nat      { length key = keylen }) ->
                  (data    :sbytes { Disjoint mac data /\ Disjoint key data }) ->
                  (datalen :nat      { length data = datalen })
                  -> ST unit
                      (requires (fun h -> Live h mac /\ Live h data /\ Live h key))
                      (ensures  (fun h0 r h1 -> Live h1 mac /\ Live h1 data /\ Live h1 key))

let hmac_sha384 mac key keylen data datalen =
  (* Define ipad and opad *)
  let ipad = SBuffer.create #8 (FStar.UInt8.of_string "0x36") bl in
  let opad = SBuffer.create #8 (FStar.UInt8.of_string "0x5c") bl in

  (* Step 1: make sure the key has the proper length *)
  let okey,okeylen = wrap_key key keylen in
  let s1 = create #8 FStar.UInt8.zero bl in
  FStar.SBytes.blit okey 0 s1 0 okeylen;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create #8 FStar.UInt8.zero bl in
  FStar.SBytes.xor_bytes s2 s1 ipad bl;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create #8 FStar.UInt8.zero (bl + datalen) in
  FStar.SBytes.blit s2 0 s3 0 bl;
  FStar.SBytes.blit data 0 s3 bl datalen;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = create #8 FStar.UInt8.zero hl in
  hash s4 s3 (bl + datalen);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create #8 FStar.UInt8.zero bl in
  FStar.SBytes.xor_bytes s5 s1 opad bl;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create #8 FStar.UInt8.zero (hl + bl) in
  FStar.SBytes.blit s5 0 s6 0 bl;
  FStar.SBytes.blit s4 0 s6 bl hl;

  (* Step 7: apply H to "result of step 6" *)
  hash mac s6 (hl + bl)
