module FStar.Tactics.Print

open FStar.Stubs.Reflection.Types
open FStar.Stubs.Reflection.V2.Data
open FStar.Tactics.Effect

[@@plugin]
val namedv_to_string (x:namedv) : Tac string

[@@plugin]
val universe_to_ast_string (u:universe) : Tac string

[@@plugin]
val universes_to_ast_string (us:universes) : Tac string

[@@plugin]
val term_to_ast_string (t:term) : Tac string

[@@plugin]
val match_returns_to_string (ret_opt:option match_returns_ascription) : Tac string

[@@plugin]
val branches_to_ast_string (brs:list branch) : Tac string

[@@plugin]
val branch_to_ast_string (b:branch) : Tac string

[@@plugin]
val comp_to_ast_string (c:comp) : Tac string

[@@plugin]
val const_to_ast_string (c:vconst) : Tac string
