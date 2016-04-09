open Char
open SBuffer
open FStar_SBytes
open Crypto_HKDF_HMAC_Sha1



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


(* Tests from RFC 5869 *)

let _ =

  (* Test 1 *)

  Printf.printf "\n########  Test 1 ######## \n\n";

  let ikm  = "0b0b0b0b0b0b0b0b0b0b0b" in
  let salt = "000102030405060708090a0b0c" in
  let info = "f0f1f2f3f4f5f6f7f8f9" in
  let l = 42 in
  let hl = 20 in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "9b6c18c432a7bf8f0e71c8eb88f4b30baa2ba243" in
  let expected_okm = "085a01ea1b10f36933068b56efa5ad81a4f14b822f5b091568a9cdd4f155fda2c22e422478d305f3f896" in

  hkdf_extract prk (from_bytestring salt) ((String.length salt)/2) (from_bytestring ikm) ((String.length ikm)/2);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_bytestring info) ((String.length info)/2) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm;

  (* Test 2 *)

  Printf.printf "########  Test 2 ######## \n\n";

  let ikm  = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f" in
  let salt = "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf" in
  let info = "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff" in
  let l = 82 in
  let hl = 20 in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "8adae09a2a307059478d309b26c4115a224cfaf6" in
  let expected_okm = "0bd770a74d1160f7c9f12cd5912a06ebff6adcae899d92191fe4305673ba2ffe8fa3f1a4e5ad79f3f334b3b202b2173c486ea37ce3d397ed034c7f9dfeb15c5e927336d0441f4c4300e2cff0d0900b52d3b4" in

  hkdf_extract prk (from_bytestring salt) ((String.length salt)/2) (from_bytestring ikm) ((String.length ikm)/2);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_bytestring info) ((String.length info)/2) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm;

  (* Test 3 *)

  Printf.printf "########  Test 3 ######## \n\n";

  let l = 42 in
  let hl = 20 in

  let ikm  = "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b" in
  let salt = "" in
  let info = "" in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "da8c8a73c7fa77288ec6f5e7c297786aa0d32d01" in
  let expected_okm = "0ac1af7002b3d761d1e55298da9d0506b9ae52057220a306e07b6b87e8df21d0ea00033de03984d34918" in

  hkdf_extract prk (from_bytestring salt) ((String.length salt)/2) (from_bytestring ikm) ((String.length ikm)/2);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_bytestring info) ((String.length info)/2) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm;

  (* Test 4 *)

  Printf.printf "########  Test 4 ######## \n\n";

  let l = 42 in
  let hl = 20 in

  let ikm  = "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c" in
  let salt = Bytes.make hl '\x00' in
  let info = "" in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "2adccada18779e7c2077ad2eb19d3f3e731385dd" in
  let expected_okm = "2c91117204d745f3500d636a62f64f0ab3bae548aa53d423b0d1f27ebba6f5e5673a081d70cce7acfc48" in

  hkdf_extract prk (from_string salt) (String.length salt) (from_bytestring ikm) ((String.length ikm)/2);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_bytestring info) ((String.length info)/2) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm;
