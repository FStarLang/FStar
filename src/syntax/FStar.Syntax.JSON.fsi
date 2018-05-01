module FStar.Syntax.JSON
open FStar.Syntax.Syntax
open FStar.Ident
val decl_as_json : (lident * univ_names * typ) -> string

