module SMCMain

open Prins
open Smciface

open FStar.OrdSet

open FStar.IO

val foo: int -> unit
let foo x = print_string (string_of_int x); FStar.IO.print_string "\n"

val bar: list int -> unit
let bar x =
  print_string (string_of_int (List.length x));
  print_string "\n";
  List.iter (fun i -> print_string (string_of_int i); print_string "\n") x

;;

let rec read_input (f:fd_read) =
  let s = read_line f in
  if s = "]" then []
  else
    let i = Runtime.int_of_string s in
    i::read_input f
in

let x = FStar.IO.input_int () in

if x = 0 then
  Runtime.establish_server SecServer.handle_connection 8888
else if x = 1 then
  let f = open_read_file "alice_list.txt" in
  let l = read_input f in
  if List.length l = Circuit.listsize then
    let _ = close_read_file f in
    let y = psi (union (singleton Alice) (singleton Bob)) Alice l in
    bar y
  else failwith "Input list length different from expected by circuit library"
else
  let f = open_read_file "bob_list.txt" in
  let l = read_input f in
  if List.length l = Circuit.listsize then
    let _ = close_read_file f in
    let y = psi (union (singleton Alice) (singleton Bob)) Bob l in
    bar y
  else failwith "Input list length different from expected by circuit library"
