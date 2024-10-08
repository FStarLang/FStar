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

module FStar.Extraction.ML.PrintML
open FStar.Compiler.Effect
open FStar.Compiler
open FStar.Extraction.ML.Syntax
open FStar.Extraction.ML.Code

(* NOTE!!!! This file is not used by the OCaml build of F* (i.e. the main one).
Instead, it uses an OCaml version ocaml/fstar-lib/FStar_Extraction_ML_PrintML,
so it can use OCaml's native pretty printers.

This file is here for the F# build. *)

let print (_: option string) (ext: string) (l: mllib) =
    let newDoc = FStar.Extraction.ML.Code.doc_of_mllib l in
    List.iter (fun (n,d) ->
        FStar.Compiler.Util.write_file (FStar.Options.prepend_output_dir (n^ext)) (FStar.Extraction.ML.Code.pretty 120 d)) newDoc
