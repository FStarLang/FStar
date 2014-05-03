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

val (~%) : string -> doc
val (+.) : doc -> doc -> doc
val (@.) : doc -> doc -> doc

(* -------------------------------------------------------------------- *)
val enclose : string -> string -> doc -> doc
val parens  : doc -> doc

val join   : string -> doc list -> doc
val joins  : doc list -> doc
val groups : doc list -> doc
val align  : doc list -> doc

(* -------------------------------------------------------------------- *)
val pretty : int -> doc -> string
