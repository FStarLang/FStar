open Char
open SBuffer
open FStar_SBytes
open Crypto_Sha256

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


let test_result () =
  let hash = create (0) 32 in

  let input = "" in
  let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" in
  Printf.printf "Input    : '%s'\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "abc" in
  let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "abcabc" in
  let expected = "bbb59da3af939f7af5f360f2ceb80a496e3bae1cd87dde426db0ae40677e1c2c" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "59f109d9533b2b70e7c3b814a2bd218f78ea5d3714455bc67987cf0d664399cf" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string input) (String.length input);
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected;

  let hash = create (0) 32 in
  let input = "1M 'a'" in
  let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" in
  Printf.printf "Input    : %s\n" input;
  sha256 hash (from_string (Bytes.make 1000000 '\x61')) 1000000;
  Printf.printf "Result   :";
  print_bytes hash;
  Printf.printf "Expected :%s\n\n" expected

(*
let test_pad () =
  let hash = create (0) 32 in

  let input = "" in
  Printf.printf "Input    : '%s'\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abc" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcabc" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdefghijklmnopqrstuvwxyz" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) (String.length input));
  Printf.printf "\n"

  (*
  let input = "1M 'a'" in
  let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result pad :";
  print_bytes (test_pad (from_string input) 1000000);
  Printf.printf "\n"
  *)


let test_whash () =
  let hash = create (0) 32 in

  let input = "" in
  let expected = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855" in
  Printf.printf "Input    : '%s'\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abc" in
  let expected = "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcabc" in
  let expected = "bbb59da3af939f7af5f360f2ceb80a496e3bae1cd87dde426db0ae40677e1c2c" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdefghijklmnopqrstuvwxyz" in
  let expected = "71c480df93d6ae2f1efad1447c66c9525e316218cf51fc8d9ed832f2daf18b73" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" in
  let expected = "59f109d9533b2b70e7c3b814a2bd218f78ea5d3714455bc67987cf0d664399cf" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n";

  let input = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu" in
  let expected = "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) (String.length input));
  Printf.printf "\n"

  (*
  let input = "1M 'a'" in
  let expected = "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0" in
  Printf.printf "Input    : %s\n" input;
  Printf.printf "Result W1 :";
  print_bytes (test_whash (from_string input) 1000000);
  Printf.printf "\n"
  *)


let test_init_whash () = print_bytes (test_init_whash ())
*)

let _ =  test_result ()
