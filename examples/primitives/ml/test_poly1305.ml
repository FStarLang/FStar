open Poly1305
open Char
open FStar_SBytes
       
let bytes_from_bytestring s =
  let b = Bytes.of_string s in
  for i = 0 to Bytes.length b / 2 - 1 do
    Bytes.set b i (chr (int_of_string ("0x" ^ (String.sub s (2*i) 2))))
  done;
  {content = b; idx = 0; length = Bytes.length b}

let bytes_from_string s = {content = Bytes.of_string s; idx = 0; length = String.length s}

let key = bytes_from_bytestring "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
let msg = bytes_from_string "Cryptographic Forum Research Group"
let expected = "Tag: a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9"

let _ =
  (* To store the hash *)
  let hash = create (chr 0) 16 in
  (* Run hash computation *)
  poly1305_mac hash msg 34 key;
  (* Output result *)
  print_string ("Expected " ^ expected ^ "\n");
  print_string "Got hash:\n";
  print_bytes hash 
