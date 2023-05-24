module Pulse.RuntimeUtils
open Pulse.Typing
val extend_context (tag:string) (ctx:context) : context
val debug_at_level (g:env) (s:string) : bool
val print_exn (e:exn) : string
