module Crypto.HMAC.Sha1

open FStar.SBytes
open SBuffer
open FStar.Heap
open FStar.UInt8
open Crypto.Sha1



(* Define a function to wrap the key length after 64 bits *)
val wrap_key : (key    :sbytes) ->
               (keylen :nat { length key = keylen })
               -> St (okey:sbytes { length okey <= 64 } * okeylen: nat)

let wrap_key key keylen =
  if keylen > 64 then
    let nkey = create #8 FStar.UInt8.zero 20 in
    sha1 nkey key keylen;
    nkey,20
  else
    key,keylen

(* Define the main function *)
val hmac_sha1 : (mac     :sbytes { length mac = 20 }) ->
                (data    :sbytes { Disjoint mac data }) ->
                (datalen :nat { length data = datalen }) ->
                (key     :sbytes { Disjoint key mac /\ Disjoint key data }) ->
                (keylen  :nat { length key = keylen })
                -> ST unit
                     (requires (fun h -> Live h mac /\ Live h data /\ Live h key))
                     (ensures  (fun h0 r h1 -> Live h1 mac /\ Live h1 data /\ Live h1 key))

let hmac_sha1 mac data datalen key keylen =
  (* Define ipad and opad *)
  let ipad = SBuffer.create #8 (FStar.UInt8.of_string "0x36") 64 in
  let opad = SBuffer.create #8 (FStar.UInt8.of_string "0x5c") 64 in

  (* Step 1: make sure the key has the proper length *)
  let okey,okeylen = wrap_key key keylen in
  let s1 = create #8 FStar.UInt8.zero 64 in
  FStar.SBytes.blit okey 0 s1 0 okeylen;

  (* Step 2: xor "result of step 1" with ipad *)
  let s2 = create #8 FStar.UInt8.zero 64 in
  FStar.SBytes.xor_bytes s2 s1 ipad 64;

  (* Step 3: append data to "result of step 2" *)
  let s3 = create #8 FStar.UInt8.zero (64 + datalen) in
  FStar.SBytes.blit s2 0 s3 0 64;
  FStar.SBytes.blit data 0 s3 64 datalen;

  (* Step 4: apply H to "result of step 3" *)
  let s4 = create #8 FStar.UInt8.zero 20 in
  sha1 s4 s3 (64 + datalen);

  (* Step 5: xor "result of step 1" with opad *)
  let s5 = create #8 FStar.UInt8.zero 64 in
  FStar.SBytes.xor_bytes s5 s1 opad 64;

  (* Step 6: append "result of step 4" to "result of step 5" *)
  let s6 = create #8 FStar.UInt8.zero (20 + 64) in
  FStar.SBytes.blit s5 0 s6 0 64;
  FStar.SBytes.blit s4 0 s6 64 20;

  (* Step 7: apply H to "result of step 6" *)
  sha1 mac s6 (20 + 64)
