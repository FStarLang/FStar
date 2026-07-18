module TestChar

open FStar.All
open FStar.IO
open FStar.Char


(* See issue #2131 *)
let main () =
    let c : char = 'A' in
    if (u32_of_char c <> 65ul) then
      failwith "'A' must be 65ul";
    print_string "correct\n";
    0

let _ = main ()
