module FStar.Zip

open FStar.Compiler.Effect

val zip : string -> string

(* May raise an exception *)
val unzip : string -> string
