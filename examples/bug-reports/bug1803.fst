module Bug1803

open FStar.IO

module I32 = FStar.Int32

let main () =
   if (I32.((-1l) <^ 0l)) then print_string "correct\n" else print_string "wrong\n"
