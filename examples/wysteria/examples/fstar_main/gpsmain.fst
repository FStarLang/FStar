(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj PSemantics --__temp_no_proj SecServer --admit_fsi Smciface --verify_module SMCMain;
    variables:CONTRIB=../../../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi ../../prins.fst ../../ast.fst ../../ffibridge.fsi ../../sem.fst ../../psem.fst ../../rtheory.fst $CONTRIB/Platform/fst/Bytes.fst ../../runtime.fsi ../../print.fst ../../ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../../../crypto/sha1.fst ../../FStar.Crypto.fst ../../interpreter.fst ../../sec_server.fst gpsiface.fsi
 --*)

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
