open Char
open SBuffer
open FStar_SBytes
open Crypto_HKDF_HMAC_Sha256



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

  let ikm  = Bytes.make 22 '\x0b' in
  let salt = Bytes.make 13 '\x00' in
  let info = Bytes.make 10 '\x00' in
  let l = 42 in
  let hl = 32 in

  Bytes.set salt 0 '\x00';
  Bytes.set salt 1 '\x01';
  Bytes.set salt 2 '\x02';
  Bytes.set salt 3 '\x03';
  Bytes.set salt 4 '\x04';
  Bytes.set salt 5 '\x05';
  Bytes.set salt 6 '\x06';
  Bytes.set salt 7 '\x07';
  Bytes.set salt 8 '\x08';
  Bytes.set salt 9 '\x09';
  Bytes.set salt 10 '\x0a';
  Bytes.set salt 11 '\x0b';
  Bytes.set salt 12 '\x0c';

  Bytes.set info 0 '\xf0';
  Bytes.set info 1 '\xf1';
  Bytes.set info 2 '\xf2';
  Bytes.set info 3 '\xf3';
  Bytes.set info 4 '\xf4';
  Bytes.set info 5 '\xf5';
  Bytes.set info 6 '\xf6';
  Bytes.set info 7 '\xf7';
  Bytes.set info 8 '\xf8';
  Bytes.set info 9 '\xf9';

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5" in
  let expected_okm = "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865" in

  hkdf_extract prk (from_string salt) (String.length salt) (from_string ikm) (String.length ikm);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_string info) (String.length info) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm;

  (* Test 2 *)

  Printf.printf "########  Test 2 ######## \n\n";

  let l = 82 in
  let hl = 32 in

  let ikm  = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f" in
  let salt = "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf" in
  let info = "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff" in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244" in
  let expected_okm = "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87" in

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
  let hl = 32 in

  let ikm  = "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b" in
  let salt = "" in
  let info = "" in

  let prk = create (0) hl in
  let okm = create (0) l in

  let expected_prk = "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04" in
  let expected_okm = "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8" in

  hkdf_extract prk (from_bytestring salt) ((String.length salt)/2) (from_bytestring ikm) ((String.length ikm)/2);
  Printf.printf "Extract Result   :";
  print_bytes prk;
  Printf.printf "Extract Expected :%s\n" expected_prk;

  hkdf_expand okm prk hl (from_bytestring info) ((String.length info)/2) l;
  Printf.printf "Expand Result    :";
  print_bytes okm;
  Printf.printf "Expand Expected  :%s\n\n" expected_okm
