(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml.Code

open Microsoft.FStar.Backends.OCaml.Syntax

open FSharp.Format

val doc_of_mllib : mllib -> list<(string * doc)>
val doc_of_sig : mlsig -> doc