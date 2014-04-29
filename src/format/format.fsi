(* -------------------------------------------------------------------- *)
module FSharp.Format

(* -------------------------------------------------------------------- *)
type doc
type width = int

val (~%)   : string -> doc
val (+.)   : doc -> doc -> doc
val (+?)   : doc -> doc option -> doc
val endl   : doc
val group  : doc -> doc
val groups : list<doc> -> doc
val paren  : doc -> doc
val join   : doc -> list<doc> -> doc

val tostring : width -> doc -> string
