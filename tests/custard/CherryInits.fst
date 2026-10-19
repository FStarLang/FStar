module CherryInits
module U32 = FStar.UInt32
open FStar.All

(* Under Cherry only anonymous initializers are roots (custard.md, "Module
   initializers").  [count] is named but referenced, so it is kept; the
   anonymous [let _] runs; [unused] is named and referenced by nothing, so it
   is dropped, and the C function it calls, which does not exist, is never
   referenced either. *)
let count : ref int = alloc 0

let _ = count := !count + 1

[@@custard_extern "cherry_inits_no_such_function"]
assume val missing : unit -> ML int

let unused : int = missing ()

let main () : ML U32.t = if !count = 1 then 0ul else 1ul
