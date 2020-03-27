module Test01

open FStar.All
open FStar.IO

module I8  = FStar.Int8
module I16 = FStar.Int16
module I32 = FStar.Int32
module I64 = FStar.Int64

(* See issue #1803 *)
let main () =
    if (I8.((-1y) >=^ 0y)) then failwith "Failed (I8)";
    if (I16.((-1s) >=^ 0s)) then failwith "Failed (I16)";
    if (I32.((-1l) >=^ 0l)) then failwith "Failed (I32)";
    if (I64.((-1L) >=^ 0L)) then failwith "Failed (I64)";
    print_string "correct\n";
    0
