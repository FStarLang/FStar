(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml.Code

open Microsoft.FStar.Backends.OCaml.Syntax
open FSharp.Format

val doc_of_module : module_ -> doc
val doc_of_sig : sig_ -> doc
