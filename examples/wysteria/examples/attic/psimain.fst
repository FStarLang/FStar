(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj PSemantics --__temp_no_proj SecServer --admit_fsi Smciface --verify_module SMCMain;
    variables:CONTRIB=../../../../contrib;
    other-files:classical.fst ext.fst set.fsi heap.fst st.fst all.fst seq.fsi seqproperties.fst ghost.fst squash.fsti listTot.fst ordset.fsi ordmap.fsi list.fst io.fsti string.fsi ../../prins.fst ../../ast.fst ../../ffibridge.fsi ../../sem.fst ../../psem.fst ../../rtheory.fst $CONTRIB/Platform/fst/Bytes.fst ../../runtime.fsi ../../print.fst ../../ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../../../crypto/sha1.fst ../../crypto.fst ../../interpreter.fst ../../sec_server.fst psiiface.fsi
 --*)

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
