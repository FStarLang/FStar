open Crypto_Symmetric_Chacha20
open Char
open FStar_Buffer


let from_string s =
  let b = create FStar_UInt8.zero (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (code (String.get s i))
  done;
  b

let from_bytestring (s:string)  =
  let b = create (FStar_UInt8.of_string "0") ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (int_of_string ("0x" ^ (String.sub s (2*i) 2)))
  done;
  b
    
let print (b:int buffer) =
  let s = ref "" in
  for i = 0 to b.length - 1 do
    let s' = Printf.sprintf "%X" ((index b i))  in
    let s' = if String.length s' = 1 then "0" ^ s' else s' in 
    s := !s ^ s';
  done;
  !s

let max x y =
  if x > y then x else y
   
let print_array (a:int buffer) =
  let s = ref "" in
  for i = 0 to a.length - 1 do
    let s' = Printf.sprintf "%X" (index a i)  in
    let s' = String.init (max (8 - String.length s') 0) (fun x -> '0')  ^ s' in
    let s' = if i mod 4 = 3 then s' ^ "\n" else s' ^ " " in
    s := !s ^ s';
  done;
  print_string !s; print_string "\n"

let print_bytes b =
  print_string (print b); print_string "\n"


(* test vector from  RFC7539 2.4.2 *)
                                  
let key = {content = Array.init 32 (fun x -> x); idx = 0; length = 32 }
let iv = from_bytestring "000000000000004a00000000"
let counter = FStar_UInt32.one
let plaintext = from_string "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
let expected = [
  0x6e; 0x2e; 0x35; 0x9a; 0x25; 0x68; 0xf9; 0x80; 0x41; 0xba; 0x07; 0x28; 0xdd; 0x0d; 0x69; 0x81;
  0xe9; 0x7e; 0x7a; 0xec; 0x1d; 0x43; 0x60; 0xc2; 0x0a; 0x27; 0xaf; 0xcc; 0xfd; 0x9f; 0xae; 0x0b;
  0xf9; 0x1b; 0x65; 0xc5; 0x52; 0x47; 0x33; 0xab; 0x8f; 0x59; 0x3d; 0xab; 0xcd; 0x62; 0xb3; 0x57;
  0x16; 0x39; 0xd6; 0x24; 0xe6; 0x51; 0x52; 0xab; 0x8f; 0x53; 0x0c; 0x35; 0x9f; 0x08; 0x61; 0xd8;
  0x07; 0xca; 0x0d; 0xbf; 0x50; 0x0d; 0x6a; 0x61; 0x56; 0xa3; 0x8e; 0x08; 0x8a; 0x22; 0xb6; 0x5e;
  0x52; 0xbc; 0x51; 0x4d; 0x16; 0xcc; 0xf8; 0x06; 0x81; 0x8c; 0xe9; 0x1a; 0xb7; 0x79; 0x37; 0x36;
  0x5a; 0xf9; 0x0b; 0xbf; 0x74; 0xa3; 0x5b; 0xe6; 0xb4; 0x0b; 0x8e; 0xed; 0xf2; 0x78; 0x5e; 0x42;
  0x87; 0x4d
]

let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Elapsed time for %s : %fs\n" s (Sys.time() -. t)

let _ =
  let ciphertext = create 0 114 in
  time (fun () -> for i = 0 to 9999 do counter_mode key iv counter 114 plaintext ciphertext done) () "10.000 chacha iterations";
  print_string "Expected ciphertext:\n";
  print_string (String.concat "" (List.map (fun i -> Printf.sprintf "%02X" i) expected));
  print_string "\nGot ciphertext:\n";
  print_bytes ciphertext;
  List.iteri (fun i c ->
    if index ciphertext i <> c then
      failwith (Printf.sprintf "ciphertext and reference differ at byte %d" i)
  ) expected
