module Pulse.RuntimeUtils
open Pulse.Typing
val extend_context (tag:string) (ctx:context) : context
val print_exn (e:exn) : string