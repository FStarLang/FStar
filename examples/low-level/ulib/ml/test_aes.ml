open FStar_UInt32
open SInt_UInt8
open FStar_Buffer
open AES

let print (b:suint8s) =
  for i = 0 to (Array.length b.content - 1) do
    Printf.printf "%2x " (to_int (index b i));
    if i mod 4 = 3 then print_string "\n"
  done;
  print_string "\n"
       
let _ =
  let plaintext = create zero 16 in
  let plaintext2 = create zero 16 in
  let key = create zero 32 in
  let ciphertext = create zero 16 in
  let w = create zero 240 in
  let sbox = create zero 256 in
  let inv_sbox = create zero 256 in
  (* Initialize the test vectors *)
  for i = 0 to 15 do
    upd plaintext i (of_int (i + (i lsl 4)));
    upd key (2*i) (of_int (2*i)); 
    upd key (2*i+1) (of_int (2*i+1))
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
  
