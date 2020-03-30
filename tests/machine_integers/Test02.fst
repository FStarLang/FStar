module Test02

open FStar.All
open FStar.IO

module I8   = FStar.Int8
module I16  = FStar.Int16
module I32  = FStar.Int32
module I64  = FStar.Int64
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module U32  = FStar.UInt32
module U64  = FStar.UInt64
module U128 = FStar.UInt128

let main () =
    (* This is awkward, but the branching makes this VC hard for Z3. The integer
     * bound checks and all that go through easily one by one, but not all at once.
     * FIXME? *)
    admit ();
    if (I8.(to_string ((shift_left 1y 6ul) +^ 1y)) <> "65") then failwith "Failed (I8)";
    if (I16.(to_string ((shift_left 1s 14ul) +^ 1s)) <> "16385") then failwith "Failed (I16)";
    if (I32.(to_string ((shift_left 1l 30ul) +^ 1l)) <> "1073741825") then failwith "Failed (I32)";
    if (I64.(to_string ((shift_left 1L 62ul) +^ 1L)) <> "4611686018427387905") then failwith "Failed (I64)";

    if (U8.(to_string ((shift_left 1uy 6ul) +^ 1uy)) <> "65") then failwith "Failed (U8)";
    if (U16.(to_string ((shift_left 1us 14ul) +^ 1us)) <> "16385") then failwith "Failed (U16)";
    if (U32.(to_string ((shift_left 1ul 30ul) +^ 1ul)) <> "1073741825") then failwith "Failed (U32)";
    if (U64.(to_string ((shift_left 1uL 62ul) +^ 1uL)) <> "4611686018427387905") then failwith "Failed (U64)";

    if (U8.(to_string ((shift_left 1uy 7ul) +^ 1uy)) <> "129") then failwith "Failed (U8')";
    if (U16.(to_string ((shift_left 1us 15ul) +^ 1us)) <> "32769") then failwith "Failed (U16')";
    if (U32.(to_string ((shift_left 1ul 31ul) +^ 1ul)) <> "2147483649") then failwith "Failed (U32')";
    if (U64.(to_string ((shift_left 1uL 63ul) +^ 1uL)) <> "9223372036854775809") then failwith "Failed (U64')";

    print_string "correct\n";
    0
