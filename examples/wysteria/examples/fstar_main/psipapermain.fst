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
  List.iter (fun i -> print_string (string_of_int i); print_string "; ") x;
  print_string "\n"
;;

let rec read_input (f:fd_read) =
  let s = read_line f in
  if s = "]" then []
  else
    let i = Runtime.int_of_string s in
    i::read_input f
in

let p = FStar.IO.input_line () in
let x = FStar.IO.input_int () in

let check_list_size (n:nat) =
  if x = 1 then
    if n = Circuit.listsize then ()
    else failwith "Tried to run monolithic version with wrong list size"
  else ()
in

if p = "alice" then
  let f = open_read_file "alice_list.txt" in
  let l = read_input f in
  close_read_file f;
  check_list_size (List.length l);  
  let y =
    if x = 1 then psi_mono (union (singleton Alice) (singleton Bob)) Alice l
    else if x = 2 then psi (union (singleton Alice) (singleton Bob)) Alice l
    else psi_opt (union (singleton Alice) (singleton Bob)) Alice l
  in
  let y = List.filter (fun x -> x <> 0) y in
  let f = open_read_file "intersect.txt" in
  let l = read_input f in
  close_read_file f;
  if y = l then print_string "correct!" else print_string "incorrect!"

else if p = "bob" then
  let f = open_read_file "bob_list.txt" in
  let l = read_input f in
  close_read_file f; check_list_size (List.length l);  
  let y =
    if x = 1 then psi_mono (union (singleton Alice) (singleton Bob)) Bob l
    else if x = 2 then psi (union (singleton Alice) (singleton Bob)) Bob l
    else psi_opt (union (singleton Alice) (singleton Bob)) Bob l
  in
  let y = List.filter (fun x -> x <> 0) y in
  let f = open_read_file "intersect.txt" in
  let l = read_input f in
  close_read_file f;
  if y = l then print_string "correct!" else print_string "incorrect!"

else failwith "I don't know you"


(* if x = 0 then *)
(*   Runtime.establish_server SecServer.handle_connection 8888 *)

