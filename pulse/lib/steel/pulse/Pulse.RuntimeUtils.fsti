module Pulse.RuntimeUtils
open FStar.Tactics
module T = FStar.Tactics
type context = FStar.Sealed.Inhabited.sealed #(list (string & option range)) []
val extend_context (tag:string) (r:option range) (ctx:context) : context
val debug_at_level (g:env) (s:string) : bool
val print_exn (e:exn) : string
val bv_set_range (x:bv) (r:range) : b:bv{b==x}
val bv_range (x:bv) : range
val binder_set_range (x:binder) (r:range) : b:binder{b==x}
val binder_range (x:binder) : range
val range_of_term (t:T.term) : range
val set_range (t:T.term) (r:range) : t':T.term{t == t'}
val set_use_range (t:T.term) (r:range) : t':T.term{t == t'}
val error_code_uninstantiated_variable (_:unit) : int
val is_range_zero (r:range) : Dv bool
val union_ranges (r0 r1:range) : range