module Test03

open FStar.All
open FStar.IO

module U8 = FStar.UInt8

let main () =
    let x = U8.(add_underspec 128uy 128uy) in
    if (not (U8.(x =^ 0uy))) then failwith "oops!";
    print_string "correct\n";
    0
