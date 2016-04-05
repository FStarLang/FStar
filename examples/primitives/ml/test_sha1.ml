open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha1

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
  let hash = create (0) 20 in

  let input = "" in
  let expected = "da39a3ee5e6b4b0d3255bfef95601890afd80709" in
  Printf.printf "Input    : '%s'\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abc" in
  let expected = "a9993e364706816aba3e25717850c26c9cd0d89d" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcabc" in
  let expected = "f8c1d87006fbf7e5cc4b026c3138bc046883dc71" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "32d10c7b8cf96570ca04ce37f2a19d84240d3a89" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "84983e441c3bd26ebaae4aa1f95129e5e54670f1" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "afc53a4ea20856f98e08dc6f3a5c9833137768ed" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "a49b2446a02c645bf419f995b67091253a04a259" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "1M 'a'" in
  let expected = "34aa973cd4c4daa4f61eeb2bdbad27316534016f" in
  Printf.printf "Input    : %s\n" input;
  sha1 hash (from_string (Bytes.make 1000000 '\x61')) 1000000;
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected
