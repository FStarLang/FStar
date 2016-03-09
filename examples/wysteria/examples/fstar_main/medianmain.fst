module SMCMain

open Prins
open Smciface

open FStar.OrdSet

val foo: int -> unit
let foo x = FStar.IO.print_string (string_of_int x); FStar.IO.print_string "\n"

;;

let x = FStar.IO.input_int () in
if x = 0 then
  Runtime.establish_server SecServer.handle_connection 8888
else if x = 1 then
  let y = mono_median (union (singleton Alice) (singleton Bob)) Alice (1, 2) in
  foo y;
  let y = opt_median (union (singleton Alice) (singleton Bob)) Alice (1, 2) in
  foo y
else
  let z = mono_median (union (singleton Alice) (singleton Bob)) Bob (3, 4) in
  foo z;
  let z = opt_median (union (singleton Alice) (singleton Bob)) Bob (3, 4) in
  foo z
