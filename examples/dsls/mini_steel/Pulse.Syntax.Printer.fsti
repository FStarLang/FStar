module Pulse.Syntax.Printer
open Pulse.Syntax
module R = FStar.Reflection

val name_to_string (f:R.name) : string
val constant_to_string (c:constant) : string
val univ_to_string (u:universe) : string
val qual_to_string (q:option qualifier) : string
val binder_to_string (b:binder) : string
val term_to_string (t:term) : string
val comp_to_string (c:comp) : string
