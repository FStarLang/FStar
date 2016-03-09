module SMCMain

open Prins
open Smciface

open FStar.OrdSet

val foo: list int -> unit
let foo x = List.iter (fun i -> FStar.IO.print_string (string_of_int i); FStar.IO.print_string "\n") x

;;

let x = FStar.IO.input_int () in
if x = 0 then
  Runtime.establish_server SecServer.handle_connection 8888
else if x = 1 then
  let y = psi (union (singleton Alice) (singleton Bob)) Alice [1;2;3;4] in
  foo y
  //let y = psi_reg (union (singleton Alice) (singleton Bob)) Alice [1;2;3;4] in
  //foo y
else
  let z = psi (union (singleton Alice) (singleton Bob)) Bob [4] in
  foo z
  //let z = psi_reg (union (singleton Alice) (singleton Bob)) Bob [4] in
  //foo z
