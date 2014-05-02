(* -------------------------------------------------------------------- *)
type ustring

exception InvalidEncoding

val of_utf8 : string -> ustring
val to_utf8 : ustring -> string
