(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
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
