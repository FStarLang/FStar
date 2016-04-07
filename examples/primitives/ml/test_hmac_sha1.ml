open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha1
open Crypto_HMAC_Sha1



let from_string s =
  let b = create 0 (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (code (String.get s i))
  done;
  b

let from_bytestring s =
  let b = create 0 ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (int_of_string ("0x" ^ (String.sub s (2*i) 2)))
  done;
  b


(* Tests from RFC 4231 *)

let _ =
  let mac = create (0) 20 in

  (* Test 1 *)

  let key = Bytes.make 20 '\x0b' in
  let data = "Hi There" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "b617318655057264e28bc0b6fb378c8ef146be00" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 2 *)

  let key = "Jefe" in
  let data = "what do ya want for nothing?" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 3 *)

  let key = Bytes.make 20 '\xaa' in
  let data = Bytes.make 50 '\xdd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "125d7342b9ac11cd91a39af48aa17b4f63f175d3" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 4 *)

  let key = Bytes.make 25 '\x00' in
  Bytes.set key 0 '\x01';
  Bytes.set key 1 '\x02';
  Bytes.set key 2 '\x03';
  Bytes.set key 3 '\x04';
  Bytes.set key 4 '\x05';
  Bytes.set key 5 '\x06';
  Bytes.set key 6 '\x07';
  Bytes.set key 7 '\x08';
  Bytes.set key 8 '\x09';
  Bytes.set key 9 '\x0a';
  Bytes.set key 10 '\x0b';
  Bytes.set key 11 '\x0c';
  Bytes.set key 12 '\x0d';
  Bytes.set key 13 '\x0e';
  Bytes.set key 14 '\x0f';
  Bytes.set key 15 '\x10';
  Bytes.set key 16 '\x11';
  Bytes.set key 17 '\x12';
  Bytes.set key 18 '\x13';
  Bytes.set key 19 '\x14';
  Bytes.set key 20 '\x15';
  Bytes.set key 21 '\x16';
  Bytes.set key 22 '\x17';
  Bytes.set key 23 '\x18';
  Bytes.set key 24 '\x19';
  let data = Bytes.make 50 '\xcd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "4c9007f4026250c6bc8414f9bf50c86c2d7235da" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 5 *)

  let key = Bytes.make 20 '\x0c' in
  let data = "Test With Truncation" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;


  (* Test 6 *)

  let key = Bytes.make 80 '\xaa' in
  let data = "Test Using Larger Than Block-Size Key - Hash Key First" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "aa4ae5e15272d00e95705637ce8a3b55ed402112" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 7 *)

  let key = Bytes.make 80 '\xaa' in
  let data = "Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "e8e99d0f45237d786d6bbaa7965c7808bbff1a91" in

  hmac_sha1 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected
