open Crypto_Symmetric_Poly1305
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
  done
    
let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
  
let key = from_bytestring "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
let msg = from_string "Cryptographic Forum Research Group"
let expected_bytes = [
  0xa8; 0x06; 0x1d; 0xc1; 0x30; 0x51; 0x36; 0xc6; 0xc2; 0x2b; 0x8b; 0xaf; 0x0c; 0x01; 0x27; 0xa9
]
let expected = String.concat ":" (List.map (Printf.sprintf "%02x") expected_bytes)

let _ =
  print_string "Testing poly1305...\n";
  (* To store the hash *)
  let hash = create 0 16 in
  (* Run hash computation *)
  time (fun () -> for i = 0 to 1000 do poly1305_mac hash msg 34 key done) () "1.000 iterations of poly1305";
  (* Output result *)
  print_string ("Expected: " ^ expected ^ "\n");
  print_string  "Got hash: ";
  print hash 16;
  print_string "\n";
  List.iteri (fun i c ->
    if index hash i <> c then
      failwith (Printf.sprintf "ciphertext and reference differ at byte %d" i)
  ) expected_bytes
