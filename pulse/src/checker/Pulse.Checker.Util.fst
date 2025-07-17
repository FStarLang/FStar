module Pulse.Checker.Util
open Pulse.Typing.Env
module T = FStar.Tactics.V2

let debug (g:env) (s:string) (f:unit -> T.Tac string) : T.Tac unit =
  if Pulse.RuntimeUtils.debug_at_level (fstar_env g) s
  then T.print (f ())