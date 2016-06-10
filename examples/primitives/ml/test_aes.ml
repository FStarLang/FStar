open SInt_UInt8
open SBuffer
open Crypto_AES

let print (b:uint8s) =
  for i = 0 to (Array.length b.content - 1) do
    Printf.printf "%2x " (to_int (index 0 b i));
    if i mod 4 = 3 then print_string "\n"
  done;
  print_string "\n"
       
let _ =
  let plaintext = create 0 zero 16 in
  let plaintext2 = create 0 zero 16 in
  let key = create 0 zero 32 in
  let ciphertext = create 0 zero 16 in
  let w = create 0 zero 240 in
  let sbox = create 0 zero 256 in
  let inv_sbox = create 0 zero 256 in
  (* Initialize the test vectors *)
  for i = 0 to 15 do
    upd 0 plaintext i (of_int (i + (i lsl 4)));
    upd 0 key (2*i) (of_int (2*i)); 
    upd 0 key (2*i+1) (of_int (2*i+1))
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
  inv_cipher plaintext2 ciphertext w inv_sbox;
  print_string "Decrypted plaintext:\n";  
  print plaintext2
  
