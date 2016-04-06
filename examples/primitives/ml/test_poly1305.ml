open Poly
open Char
open SBuffer
open SBytes

let from_string s =
  let b = create 0 (String.length s) in
  for i = 0 to (String.length s - 1) do
    upd b i (code (String.get s i))
  done;
  b

let from_bytestring s =
  let b = create 0 ((String.length s) / 2) in
  for i = 0 to ((String.length s / 2) - 1) do
    upd b i (int_of_string ("0x" ^ (String.sub s (2*i) 2)))
  done;
  b

let time f x s =
  let t = Sys.time() in
  let _ = f x in
  Printf.printf "Ellapsed time for %s : %fs\n" s (Sys.time() -. t)
  
let key = from_bytestring "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
let msg = from_string "Cryptographic Forum Research Group"
let expected = "Tag: a8:06:1d:c1:30:51:36:c6:c2:2b:8b:af:0c:01:27:a9"

let _ =
  (* To store the hash *)
  let hash = create (0) 16 in
  (* Run hash computation *)
  time (fun () -> for i = 1 to 1000000 do poly1305_mac hash msg 34 key done) () "1.000.000 iterations of poly1305";
  (* Output result *)
  print_string ("Expected " ^ expected ^ "\n");
  print_string "Got hash:\n";
  print_bytes hash 
