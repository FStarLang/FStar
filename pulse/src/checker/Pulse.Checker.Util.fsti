module Pulse.Checker.Util
open Pulse.Typing.Env
module T = FStar.Tactics.V2
val debug (g:env) (s:string) (f:unit -> T.Tac string) : T.Tac unit