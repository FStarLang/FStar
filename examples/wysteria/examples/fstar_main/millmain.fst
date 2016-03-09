(* Millionaire's with 2 parties *)

module SMCMain

open Prins
open Smciface

open FStar.OrdSet

val foo: bool -> unit
let foo x = FStar.IO.print_string (string_of_bool x)

;;

let x = FStar.IO.input_int () in
if x = 0 then
  Runtime.establish_server SecServer.handle_connection 8888
else if x = 1 then
  let y = mill (union (singleton Alice) (singleton Bob)) Alice 2 in
  foo y
else
  let z = mill (union (singleton Alice) (singleton Bob)) Bob 3 in
  foo z
