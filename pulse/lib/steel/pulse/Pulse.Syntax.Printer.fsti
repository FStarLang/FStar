module Pulse.Syntax.Printer
open Pulse.Syntax
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2

val name_to_string (f:R.name) : string
// val constant_to_string (c:constant) : string
val univ_to_string (u:universe) : string
val qual_to_string (q:option qualifier) : string
val term_to_string (t:term) : T.Tac string
val binder_to_string (b:binder) : T.Tac string
val comp_to_string (c:comp) : T.Tac string
val term_list_to_string (sep:string) (t:list term): T.Tac string
val st_term_to_string (t:st_term) : T.Tac string
val tag_of_term (t:term) : string
val tag_of_st_term (t:st_term) : string
val tag_of_comp (c:comp): T.Tac string
val print_st_head (t:st_term) : string
val print_skel (t:st_term) : string
