open Crypto_Sha256

let _ =
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
      sha256 (Bytes.of_string e) (String.length e)
    ) input;
  Printf.printf "INPUT : 1 million de 'a'\n";
  sha256 (Bytes.make 1000000 '\x61') 1000000
