module Pulse.RuntimeUtils
open FStar.Tactics
open Pulse.Typing.Env
module T = FStar.Tactics
val extend_context (tag:string) (ctx:context) : context
val debug_at_level (g:env) (s:string) : bool
val print_exn (e:exn) : string
val bv_set_range (x:bv) (r:range) : bv
val bv_range (x:bv) : range
val binder_set_range (x:binder) (r:range) : binder
val binder_range (x:binder) : range
val set_range (t:T.term) (r:range) : T.term
val set_use_range (t:T.term) (r:range) : T.term
val error_code_uninstantiated_variable (_:unit) : int