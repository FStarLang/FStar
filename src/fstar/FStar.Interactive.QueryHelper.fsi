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

(* FStar.Interactive.Lsp needs to construct responses to various *
 * queries; this file collects helpers for them                  *)
#light "off"

module FStar.Interactive.QueryHelper
open FStar
open FStar.Range
open FStar.Util
open FStar.TypeChecker.Env
open FStar.Interactive.JsonHelper

module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable

type position = string * int * int
type sl_reponse = { slr_name: string;
                    slr_def_range: option<Range.range>;
                    slr_typ: option<string>;
                    slr_doc: option<string>;
                    slr_def: option<string> }

// Shared by IDE and LSP
val term_to_string : TcEnv.env -> Syntax.Syntax.term -> string
val symlookup : TcEnv.env -> string -> option<position> -> list<string> -> option<sl_reponse>
val ck_completion : repl_state -> string -> list<CTable.completion_result>

(* Used exclusively by LSP *)
// Lookup the definition of a particular term located at txdoc_pos
val deflookup : TcEnv.env -> txdoc_pos -> option<assoct>

// Lookup the on-hover documentation for a particular term located at txdoc_pos
val hoverlookup : TcEnv.env -> txdoc_pos -> option<assoct>

// Lookup the completion information for a particular term located at txdoc_pos
val complookup : repl_state -> txdoc_pos -> option<assoct>
