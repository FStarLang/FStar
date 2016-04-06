open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha256
open Crypto_HMAC_Sha256



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



let _ =
  let mac = create (0) 32 in

  (* Test 1 *)

  let key = Bytes.make 20 '\x0b' in
  let data = "Hi There" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7" in

  hmac_sha256 mac (from_string data) datalen (from_string key) keylen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 2 *)

  let key = "Jefe" in
  let data = "what do ya want for nothing?" in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843" in

  hmac_sha256 mac (from_string data) datalen (from_string key) keylen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;

  (* Test 3 *)

  let key = Bytes.make 20 '\xaa' in
  let data = Bytes.make 50 '\xdd' in
  let keylen = Bytes.length key in
  let datalen = Bytes.length data in

  let expected = "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe" in

  hmac_sha256 mac (from_string data) datalen (from_string key) keylen;
  Printf.printf "Result   :";
  print_bytes mac;
  Printf.printf "Expected :%s\n\n" expected;
