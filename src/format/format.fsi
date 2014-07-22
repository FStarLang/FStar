(* -------------------------------------------------------------------- *)
#light "off"

module FSharp.Format

(* -------------------------------------------------------------------- *)
type doc

(* -------------------------------------------------------------------- *)
val empty  : doc
val text   : string -> doc
val cat    : doc -> doc -> doc
val nest   : int -> doc -> doc
val group  : doc -> doc

val break_ : int -> doc
val break0 : doc
val break1 : doc

val hardline : doc

(* -------------------------------------------------------------------- *)
val cat1    : doc -> doc -> doc
val reduce  : list<doc> -> doc
val reduce1 : list<doc> -> doc
val combine : doc -> list<doc> -> doc
val groups  : list<doc> -> doc
val align   : list<doc> -> doc
val hbox    : doc -> doc
val parse   : string -> doc

(* -------------------------------------------------------------------- *)
val enclose  : doc -> doc -> doc -> doc
val parens   : doc -> doc
val brackets : doc -> doc

(* -------------------------------------------------------------------- *)
val pretty : int -> doc -> string
