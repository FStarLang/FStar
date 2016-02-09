module SMCMain

open Prins
open Smciface

open FStar.OrdSet

open FStar.IO

val foo: prin -> unit
let foo x = print_string (Print.prin_to_string x); print_string "\n"

;;

let p = FStar.IO.input_line () in
let x = FStar.IO.input_int () in

if p = "alice" then
  let y = gps (union (singleton Alice) (union (singleton Bob) (singleton Charlie))) Alice x in
  foo y

else if p = "bob" then
  let y = gps (union (singleton Alice) (union (singleton Bob) (singleton Charlie))) Bob x in
  foo y

else if p = "charlie" then
  let y = gps (union (singleton Alice) (union (singleton Bob) (singleton Charlie))) Charlie x in
  foo y

else failwith "I don't know you"
