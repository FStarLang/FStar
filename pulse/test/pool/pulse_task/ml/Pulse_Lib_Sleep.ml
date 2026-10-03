(* Pulse.Lib.Sleep's one primitive.  The argument is a Prims.int, which
   Custard represents as OCaml's arbitrary-precision Z.t. *)

let sleep_ms (ms: Z.t) : unit = Unix.sleepf (Z.to_float ms /. 1000.0)
