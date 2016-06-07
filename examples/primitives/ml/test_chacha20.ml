open Chacha
open Char
open SBuffer
open SBytes
       
let key = {content = Array.init 32 (fun x -> (SInt_UInt8.of_int x)); idx = 0; length = 32 }

let nonce =
  let n = create SInt_UInt8.zero 12 in
  upd n 7 (SInt_UInt8.of_int 0x4a);
  n

let counter = SInt_UInt32.one

let from_string s =
  let b = create SInt_UInt8.zero (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (SInt_UInt8.of_int (code (String.get s i)))
  done;
  b
                
let print (b:sbytes) =
  let s = ref "" in
  for i = 0 to b.length - 1 do
    let s' = Printf.sprintf "%X" (SInt_UInt8.to_int (index b i))  in
    let s' = if String.length s' = 1 then "0" ^ s' else s' in 
    s := !s ^ s';
  done;
  !s

let max x y =
  if x > y then x else y
   
let print_array (a:int SBuffer.buffer) =
  let s = ref "" in
  for i = 0 to a.length - 1 do
    let s' = Printf.sprintf "%X" (SBuffer.index 0 a i)  in
    let s' = String.init (max (8 - String.length s') 0) (fun x -> '0')  ^ s' in
    let s' = if i mod 4 = 3 then s' ^ "\n" else s' ^ " " in
    s := !s ^ s';
  done;
  print_string !s; print_string "\n"

let print_bytes b =
  print_string (print b); print_string "\n"

let plaintext = from_string "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
                            
let expected = "  000  6e 2e 35 9a 25 68 f9 80 41 ba 07 28 dd 0d 69 81  n.5.%h..A..(..i.
  016  e9 7e 7a ec 1d 43 60 c2 0a 27 af cc fd 9f ae 0b  .~z..C`..'......
  032  f9 1b 65 c5 52 47 33 ab 8f 59 3d ab cd 62 b3 57  ..e.RG3..Y=..b.W
  048  16 39 d6 24 e6 51 52 ab 8f 53 0c 35 9f 08 61 d8  .9.$.QR..S.5..a.
  064  07 ca 0d bf 50 0d 6a 61 56 a3 8e 08 8a 22 b6 5e  ....P.jaV....\".^
  080  52 bc 51 4d 16 cc f8 06 81 8c e9 1a b7 79 37 36  R.QM.........y76
  096  5a f9 0b bf 74 a3 5b e6 b4 0b 8e ed f2 78 5e 42  Z...t.[......x^B
  112  87 4d\n"

let _ =
  let ciphertext = create SInt_UInt8.zero 114 in
  (*  let state = SBuffer.create 0 0 16 in *)
  chacha20_encrypt ciphertext key counter nonce plaintext 114;
  print_string "Test key:\n";
  print_bytes key;
  print_string "Test nonce:\n";
  print_bytes nonce;
  print_string "Expected ciphertext:\n";
  print_string expected;
  print_string "Got ciphertext:\n";
  print_bytes ciphertext
              (*  print_array state *)
