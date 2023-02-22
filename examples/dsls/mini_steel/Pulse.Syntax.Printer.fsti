module Pulse.Syntax.Printer
open Pulse.Syntax
module R = FStar.Reflection
module T = FStar.Tactics

val name_to_string (f:R.name) : string
val constant_to_string (c:constant) : string
val univ_to_string (u:universe) : string
val qual_to_string (q:option qualifier) : string
val binder_to_string (b:binder) : T.Tac string
val term_to_string (t:term) : T.Tac string
val comp_to_string (c:comp) : T.Tac string
val st_term_to_string (t:st_term) : T.Tac string
