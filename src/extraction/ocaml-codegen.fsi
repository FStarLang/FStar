(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Extraction.OCaml.Code

open Microsoft.FStar.Extraction.ML.Syntax
open Microsoft.FStar.Extraction.ML.Env
open FSharp.Format

val doc_of_mllib : mllib -> list<(string * doc)>
val doc_of_sig : mlsymbol -> mlsig -> doc
val string_of_mlexpr: env -> mlexpr -> string
val string_of_mlty: env -> mlty -> string
