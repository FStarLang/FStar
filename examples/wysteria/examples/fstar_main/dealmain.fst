(*--build-config
    options:--admit_fsi FStar.OrdSet --admit_fsi FStar.Seq --admit_fsi FStar.OrdMap --admit_fsi FStar.Set --admit_fsi Ffibridge --admit_fsi Runtime --admit_fsi Prog --admit_fsi FStar.IO --admit_fsi FStar.String --admit_fsi FStar.Squash --__temp_no_proj PSemantics --__temp_no_proj SecServer --admit_fsi Smciface --admit_fsi Hashtable --verify_module SMCMain;
    variables:CONTRIB=../../../../contrib;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst seq.fsi FStar.SeqProperties.fst FStar.Ghost.fst FStar.Squash.fsti FStar.List.Tot.fst ordset.fsi ordmap.fsi FStar.List.fst FStar.IO.fsti string.fsi ../../prins.fst $CONTRIB/Platform/fst/Bytes.fst ../../ast.fst ../../ffibridge.fsi ../../sem.fst ../../psem.fst ../../rtheory.fst ../../runtime.fsi ../../print.fst ../../hashtable.fsi ../../ckt.fst $CONTRIB/CoreCrypto/fst/CoreCrypto.fst ../../../crypto/sha1.fst ../../crypto.fst ../../interpreter.fst dealiface.fsi
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
  List.iter (fun i -> print_string (string_of_int i); print_string "; ") x;
  print_string "\n"

val loop: ps:prins{ps = union (union (singleton Alice) (singleton Bob)) (singleton Charlie)} -> p:prin{mem p ps} -> list sh -> unit
let rec loop ps p l =
  print_string "Enter a random seed:\n";
  let x = FStar.IO.input_int () in
  let (l', c) = deal ps p l x Alice in
  let _ =
    if c = 52 then print_string "Card had already been dealt\n"
    else
      let _ = print_string "New card: " in
      let _ = print_string (string_of_int c) in
      print_string "\n"
  in
  loop ps p l'

;;

let rec read_input (f:fd_read) =
  let s = read_line f in
  if s = "]" then []
  else
    let i = Runtime.int_of_string s in
    i::read_input f
in

let p = FStar.IO.input_line () in

let p =
  if p = "alice" then Alice
  else if p = "bob" then Bob
  else Charlie
in

loop (union (union (singleton Alice) (singleton Bob)) (singleton Charlie)) p [] 

(* if p = "alice" then *)
(*   let y = deal (union (union (singleton Alice) (singleton Bob)) (singleton Charlie)) Alice [] x Alice in *)
(*   let _ = print_string (string_of_int y) in *)
(*   print_string "done!"  *)
(* else if p = "bob" then *)
(*   let _ = deal (union (union (singleton Alice) (singleton Bob)) (singleton Charlie)) Bob [] 1 Alice in *)
(*   print_string "done!"  *)
(* else *)
(*   let _ = deal (union (union (singleton Alice) (singleton Bob)) (singleton Charlie)) Charlie [] 1 Alice in *)
(*   print_string "done!"  *)
