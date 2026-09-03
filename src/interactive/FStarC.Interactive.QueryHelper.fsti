(*
   Copyright 2019 Microsoft Research

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

(* FStarC.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)

module FStarC.Interactive.QueryHelper
open FStarC
open FStarC.Effect
open FStarC.Range
open FStarC.TypeChecker.Env
open FStarC.Interactive.Ide.Types

module TcEnv = FStarC.TypeChecker.Env
module CTable = FStarC.Interactive.CompletionTable

type position = string & int & int
type sl_reponse = { slr_name: string;
                    slr_def_range: option Range.t;
                    slr_typ: option string;
                    slr_doc: option string;
                    slr_def: option string }

val term_to_string : TcEnv.env -> Syntax.Syntax.term -> ML string

(** The documentation attached to [lid] with the [FStar.Attributes.doc]
    attribute, if any.

    [None] means "this name has no documentation": either it carries no
    [doc] attribute, or it carries one whose payload is not a string
    literal and hence cannot be reported. The [lookup] request has no
    per-field error channel -- [documentation] is a string or null -- so
    both answer null, and neither is an error: a name without
    documentation is entirely ordinary. The [--export_docs] command,
    which does have somewhere to put a diagnostic, warns about the
    second case.

    When an interface declares [lid], its declaration is consulted
    directly. This makes both its text and its lack of text authoritative:
    implementation-only documentation cannot leak through a merged
    implementation sigelt. *)
val docs_of_lid : TcEnv.env -> Ident.lident -> ML (option string)

val symlookup : TcEnv.env -> string -> option position -> list string -> ML (option sl_reponse)
val ck_completion : repl_state -> string -> ML (list CTable.completion_result)
