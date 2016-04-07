open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha512
open Crypto_HMAC_Sha512



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
  let mac = create (0) 64 in

  (* Test 1 *)

  let key = Bytes.make 20 '\x0b' in
  let data = "Hi There" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 2 *)

  let key = "Jefe" in
  let data = "what do ya want for nothing?" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea2505549758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 3 *)

  let key = Bytes.make 20 '\xaa' in
  let data = Bytes.make 50 '\xdd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
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

  let expected = "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3dba91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 5 *)

  let key = Bytes.make 20 '\x0c' in
  let data = "Test With Truncation" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "415fad6271580a531d4179bc891d87a6" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  let res = SBuffer.sub 64 mac 0 16 in
  Printf.printf "Result (truncation at 128) :";
  print_bytes res;
  Printf.printf "Expected                   :%s\n\n" expected;


  (* Test 6 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "Test Using Larger Than Block-Size Key - Hash Key First" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 7 *)

  let key = Bytes.make 131 '\xaa' in
  let data = "This is a test using a larger than block-size key and a larger than block-size data. The key needs to be hashed before being used by the HMAC algorithm." in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58" in

  hmac_sha512 mac (from_string key) keylen (from_string data) datalen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected
