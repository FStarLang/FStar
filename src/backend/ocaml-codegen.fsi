(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml.Code

open Microsoft.FStar.Backends.ML.Syntax
open Microsoft.FStar.Backends.ML.Env
open FSharp.Format

val doc_of_mllib  : mllib -> list<(string * doc)>
val string_of_mlexpr : env -> mlexpr -> string
val string_of_mlty   : env -> mlty -> string

//val doc_of_sig : mlsig -> doc