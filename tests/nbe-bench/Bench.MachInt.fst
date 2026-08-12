module Bench.MachInt
open FStar.UInt32
#set-options "--z3rlimit 30"
let rec loop (n:nat) (acc:UInt32.t) : UInt32.t =
  if n = 0 then acc else loop (n-1) (acc +%^ 3ul *%^ 5ul)
#push-options "--no_smt"
let _ = assert_norm (loop 2000 0ul == 30000ul)
#pop-options
