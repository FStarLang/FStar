module SMCMain

open Prins
open Smciface

open FStar.OrdSet

val foo: prin -> unit
let foo x = FStar.IO.print_string (Print.prin_to_string x); FStar.IO.print_string "\n"

;;

let x = FStar.IO.input_int () in
if x = 0 then
  Runtime.establish_server SecServer.handle_connection 8888
else if x = 1 then
  let y = gps (union (singleton Alice) (singleton Bob)) Alice 2 in
  foo y
else
  let z = gps (union (singleton Alice) (singleton Bob)) Bob 3 in
  foo z
