(* -------------------------------------------------------------------- *)
module FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
type doc
type width = int

val (&.)  : string -> doc
val (+.)  : doc -> doc -> doc
val endl  : doc
val group : doc -> doc

val tostring : width -> doc -> string
