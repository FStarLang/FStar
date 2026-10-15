module Spy2

(* On s2.silicon, Uart-s2.fst cannot be replaced: Uart-s2.qemu.fst diverges
   from s2.silicon, and Uart-s3-c.fst is not more specific. *)
friend Uart

let _ = assert (Uart.board == "s2")
let ok = ()
