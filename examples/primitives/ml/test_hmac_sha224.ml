open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha224
open Crypto_HMAC_Sha224



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
  let mac = create (0) 28 in

  (* Test 1 *)

  let key = Bytes.make 20 '\x0b' in
  let data = "Hi There" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "896fb1128abbdf196832107cd49df33f47b4b1169912ba4f53684b22" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 2 *)

  let key = "Jefe" in
  let data = "what do ya want for nothing?" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "a30e01098bc6dbbf45690f3a7e9e6d0f8bbea2a39e6148008fd05e44" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 3 *)

  let key = Bytes.make 20 '\xaa' in
  let data = Bytes.make 50 '\xdd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "7fb3cb3588c6c1f6ffa9694d7d6ad2649365b0c1f65d69d1ec8333ea" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
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

  let expected = "6c11506874013cac6a2abc1bb382627cec6a90d86efc012de7afec5a" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 5 *)

  let key = Bytes.make 20 '\x0c' in
  let data = "Test With Truncation" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "0e2aea68a90c8d37c988bcdb9fca6fa8" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  let res = SBuffer.sub 28 mac 0 16 in
  Printf.printf "Result (truncation at 128) :";
  print_bytes res;
  Printf.printf "Expected                   :%s\n\n" expected;


  (* Test 6 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "Test Using Larger Than Block-Size Key - Hash Key First" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "95e9a0db962095adaebe9b2d6f0dbce2d499f112f2d2b7273fa6870e" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 7 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm." in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "3a854166ac5d9f023f54d517d0b39dbd946770db9c2b95c9f6f565d1" in

  hmac_sha224 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected
