open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha224

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
  let hash = create (0) 28 in

  let input = "" in
  let expected = "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f" in
  Printf.printf "Input    : '%s'\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abc" in
  let expected = "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcabc" in
  let expected = "7c9c91fc479626aa1a525301084deb96716131d146a2db61b533f4c9" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "45a5f72c39c5cff2522eb3429799e49e5f44b356ef926bcf390dccc2" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "7de2f93b0d0a1f5caf837739da74167a03bd64b793067ebd4073d0dc" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "c97ca9a559850ce97a04a96def6d99a9e0e0e2ab14e6b8df265fc0b3" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "1M 'a'" in
  let expected = "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67" in
  Printf.printf "Input    : %s\n" input;
  sha224 hash (from_string (Bytes.make 1000000 '\x61')) 1000000;
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected
