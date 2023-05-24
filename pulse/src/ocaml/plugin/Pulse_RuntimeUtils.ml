let extend_context (s:string) (c:string list) = s::c
let print_exn (e:exn) = Printexc.to_string e
let debug_at_level (g:Pulse_Typing.env) (s:string) = FStar_TypeChecker_Env.debug g.f (FStar_Options.Other s)
