open FStar_UInt8
open FStar_Buffer
open Crypto_Symmetric_AES

let print (b:bytes) =
  for i = 0 to (Array.length b.content - 1) do
    print_string (to_string_hex (index b i));
    if i mod 4 = 3 then print_string "\n"
  done;
  print_string "\n"
       
let _ =
  let zero = 0 in
  let plaintext = create zero 16 in
  let plaintext2 = create zero 16 in
  let key = create zero 32 in
  let ciphertext = create zero 16 in
  let w = create zero 240 in
  let sbox = create zero 256 in
  let inv_sbox = create zero 256 in
  (* Initialize the test vectors *)
  for i = 0 to 15 do
    upd plaintext i (i + (i lsl 4));
    upd key (2*i) (2*i); 
    upd key (2*i+1) (2*i+1)
  done;
  (* Initialize sboxes *)
  mk_sbox sbox;
  mk_inv_sbox inv_sbox;
  print_string "Initial plaintext:\n";
  print plaintext;
  keyExpansion key w sbox;
  cipher ciphertext plaintext w sbox;
  print_string "Resulting ciphertext:\n";  
  print ciphertext;
  let expected = "8ea2b7ca516745bfeafc49904b496089" in
  for i = 0 to 15 do
    if not(to_string_hex (index ciphertext i) = String.sub expected (2*i) 2) then
      failwith (Printf.sprintf "Ciphertext differs at byte %d: %s %s\n" i (to_string_hex (index ciphertext i)) (String.sub expected (2*i) 2)) 
  done;
  inv_cipher plaintext2 ciphertext w inv_sbox;
  print_string "Decrypted plaintext:\n";  
  print plaintext2
