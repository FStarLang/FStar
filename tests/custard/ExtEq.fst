module ExtEq
module I32 = FStar.Int32
open FStar.All
open FStar.Attributes

(* Section 117.2.  The external's target is exactly the name the generated
   equality helper for [pair] would take, and the helper has to step around
   it rather than over it. *)
type pair = { a : I32.t; b : I32.t }

[@@custard_extern "ExtEq_pair__eq"]
assume val bump (n:I32.t) : I32.t

let run (x:pair) (y:pair) : I32.t =
  if x = y then bump x.a else x.b

(* [run] on two equal pairs calls the external, which adds one: 0 out. *)
let main () : ML I32.t = run ({ a = -1l; b = 3l }) ({ a = -1l; b = 3l })
