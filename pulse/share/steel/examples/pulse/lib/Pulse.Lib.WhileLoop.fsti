module Pulse.Lib.WhileLoop
open Pulse.Lib.Core

val while_loop
  (inv:bool -> vprop)
  (cond:stt bool (exists* x. inv x) (fun b -> inv b))
  (body:stt unit (inv true) (fun _ -> exists* x. inv x))
  : stt unit (exists* x. inv x) (fun _ -> inv false)
