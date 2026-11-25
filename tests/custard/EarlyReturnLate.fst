module EarlyReturnLate

open FStar.All
module U32 = FStar.UInt32

[@@custard_extern "er_tick"; custard_c_header "EarlyReturn_stubs.h"]
assume val tick : U32.t -> ML U32.t

(* The else-branch declares a local after the early return of the
   then-branch: goto mode can only jump past it once it is hoisted. *)
let later (x:U32.t) : ML U32.t =
  if U32.eq x 0ul then tick 1ul
  else
    let y = tick x in
    let z = tick y in
    U32.add_mod y z

let main () : ML FStar.Int32.t =
  let a = later 0ul in
  let b = later 2ul in
  if U32.eq a 1ul && U32.eq b 4ul then 0l else 1l
