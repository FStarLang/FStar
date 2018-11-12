module Bug460

open FStar.IO
open FStar.ST

// let x = alloc 0

// let y = alloc 0

// let z = alloc 1

let print_test () =
  let x = alloc 0 in
  let y = alloc 0 in
  let z = alloc 1 in
  print_string "Test (x = y) = ";
  print_string (string_of_bool (x = y));
  print_string "\n";
  print_string "Test (x = z) = ";
  print_string (string_of_bool (x = z));
  print_string "\n"

let main = print_test ()

(*
$ bin/fstar.exe examples/bug-reports/bug460.fst --codegen OCaml
$ ocamlfind ocamlopt -package batteries,stdint,fileutils,sqlite3,zarith -linkpkg -g -thread -w a+A-27 -I ulib/ml/ ulib/ml/fstarlib.cmxa Bug460.ml -o Bug460
$ ./Bug460
Test (x = y) = true
Test (x = z) = false
*)
