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

let _ =
  let hash = create (0) 32 in
  let input = [ "abc";
                "abcabc";
                "abcdefghijklmnopqrstuvwxyz";
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
                "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopqabcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
              ]
  in
  List.iter (
      fun e ->
      Printf.printf "INPUT : %s\n" e;
      sha256 hash (from_string e) (String.length e);
      print_bytes hash
    ) input;
  Printf.printf "INPUT : 1 million de 'a'\n";
  sha256 hash (from_string (Bytes.make 1000000 '\x61')) 1000000;
  print_bytes hash
