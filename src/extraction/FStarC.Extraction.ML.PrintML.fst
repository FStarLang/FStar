(*
   Copyright 2008-2015 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module FStarC.Extraction.ML.PrintML
open FStarC.Effect
open FStarC
open FStarC.Extraction.ML.Syntax
open FStarC.Extraction.ML.Code

(* NOTE!!!! This file is not used by the OCaml build of F* (i.e. the main one).
Instead, it uses an OCaml version ocaml/fstar-lib/FStar_Extraction_ML_PrintML,
so it can use OCaml's native pretty printers.

This file is here for the F# build. *)

let print (_: option string) (ext: string) (l: mllib) =
    let newDoc = FStarC.Extraction.ML.Code.doc_of_mllib l in
    List.iter (fun (n,d) ->
        FStarC.Util.write_file (FStarC.Find.prepend_output_dir (n^ext)) (FStarC.Extraction.ML.Code.pretty 120 d)) newDoc
