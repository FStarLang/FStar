(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj PSemantics --__temp_no_proj SecServer --admit_fsi Smciface --admit_fsi Hashtable --verify_module SMCMain;
    variables:CONTRIB=../../../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi ../../prins.fst ../../ast.fst ../../ffibridge.fsi ../../sem.fst ../../psem.fst ../../rtheory.fst $CONTRIB/Platform/fst/Bytes.fst ../../runtime.fsi ../../print.fst ../../hashtable.fsi ../../ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../../../crypto/sha1.fst ../../FStar.Crypto.fst ../../interpreter.fst ../../sec_server.fst psitestiface.fsi
 --*)

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
