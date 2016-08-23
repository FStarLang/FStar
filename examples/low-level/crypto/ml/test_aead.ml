open Crypto_AEAD_Chacha20Poly1305
open Char
open FStar_Buffer
open Crypto_Symmetric_Poly1305_Bigint
       
let from_string s : bytes =
  let b = create 0 (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (code (String.get s i))
  done;
  b

let from_bytestring (s:string) : bytes =
  let b = create (FStar_UInt8.of_string "0") ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (int_of_string ("0x" ^ (String.sub s (2*i) 2)))
  done;
  b

let print (s:bytes) (len:int) : unit =
  for i = 0 to len - 1 do
    Printf.printf "%02x" (index s i);
    if i < len - 1 then print_string ":"
  done;
  print_string "\n"
    
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)

let plaintext = from_string "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
let aad = from_bytestring "50515253c0c1c2c3c4c5c6c7"
let key = from_bytestring "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
let iv = FStar_UInt64.of_string "0x4746454443424140"
let constant = FStar_UInt32.of_string "0x7"

let expected_ciphertext = "d3:1a:8d:34:64:8e:60:db:7b:86:af:bc:53:ef:7e:c2:a4:ad:ed:51:29:6e:08:fe:a9:e2:b5:a7:36:ee:62:d6:3d:be:a4:5e:8c:a9:67:12:82:fa:fb:69:da:92:72:8b:1a:71:de:0a:9e:06:0b:29:05:d6:a5:b6:7e:cd:3b:36:92:dd:bd:7f:2d:77:8b:8c:98:03:ae:e3:28:09:1b:58:fa:b3:24:e4:fa:d6:75:94:55:85:80:8b:48:31:d7:bc:3f:f4:de:f0:8e:4b:7a:9d:e5:76:d2:65:86:ce:c6:4b:61:16"
let expected_tag_bytes = [
    0x1a; 0xe1; 0x0b; 0x59; 0x4f; 0x09; 0xe2; 0x6a; 0x7e; 0x90; 0x2e; 0xcb; 0xd0; 0x60; 0x06; 0x91
  ]
let expected_tag = String.concat ":" (List.map (Printf.sprintf "%02x") expected_tag_bytes)
                                
let _ =
  print_string "Testing AEAD Chacha-Poly...\n";
  (* To store the hash *)
  let ciphertext = FStar_Buffer.create 0 114 in
  let tag = FStar_Buffer.create 0 16 in
  (* Run hash computation *)
  time (fun () -> for i = 0 to 999 do chacha20_aead_encrypt ciphertext tag aad key iv constant plaintext 114 12 done) () "1000 iterations of poly1305";
  (* Output result *)
  print_string ("Expected ciphertext: \n" ^ expected_ciphertext ^ "\n");
  print_string "Got ciphertext:\n";
  print ciphertext 114;
  print_string ("Expected tag: \n" ^ expected_tag ^ "\n");
  print_string  "Got tag: \n";
  print tag 16;
  print_string "\n";
  List.iteri (fun i c ->
    if FStar_Buffer.index tag i <> c then
      failwith (Printf.sprintf "tag and reference differ at byte %d" i)
  ) expected_tag_bytes
