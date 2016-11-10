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
  Printf.printf "Elapsed time for %s : %fs\n" s (Sys.time() -. t)

let plaintext = from_string "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
let aad = from_bytestring "50515253c0c1c2c3c4c5c6c7"
let key = from_bytestring "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
let iv =
  Crypto_Symmetric_Bytes.load_uint128 12 (from_bytestring  ("07000000"^"4041424344454647"))

let expected_ciphertext = from_bytestring "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116"

let expected_tag = from_bytestring "1ae10b594f09e26a7e902ecbd0600691"

let diff name expected computed len =
  print_string ("Expected "^name^":\n"); print expected len;
  print_string ("Computed "^name^":\n"); print computed len;
  if not(FStar_Buffer.eqb expected computed 16) then
    failwith "Doesn't match expected result"
         
let _ =
  print_string "Testing AEAD chacha20_poly1305...\n";
  let ciphertext = FStar_Buffer.create 0 114 in
  let tag = FStar_Buffer.create 0 16 in
  time (fun () -> for i = 0 to 999 do
                    chacha20_aead_encrypt key iv 12 aad 114 plaintext ciphertext tag;
                  done) () "1000 iterations";
  (* Output result *)
  diff "cipher" expected_ciphertext ciphertext 114;
  diff "tag" expected_tag tag 16;

  let decrypted = FStar_Buffer.create 0 114 in
  if chacha20_aead_decrypt key iv 12 aad 114 decrypted ciphertext tag = 0
  then diff "decryption" plaintext decrypted 114
  else print_string "decryption failed";

  ()
