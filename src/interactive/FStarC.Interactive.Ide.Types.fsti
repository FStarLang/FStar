(*
   Copyright 2008-2016  Nikhil Swamy and Microsoft Research

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

module FStarC.Interactive.Ide.Types

open FStarC
open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Range
module PI = FStarC.Parser.ParseIt
module TcEnv = FStarC.TypeChecker.Env
module CTable = FStarC.Interactive.CompletionTable

(* Importing this module bring FStarC.Json into scope. *)
open FStarC.Json
include FStarC.Json

(***********************)
(* Global state setup *)
(***********************)
val initial_range : range

type push_kind = | SyntaxCheck | LaxCheck | FullCheck

type completion_context =
| CKCode
| CKOption of bool (* #set-options (false) or #reset-options (true) *)
| CKModuleOrNamespace of bool (* modules *) & bool (* namespaces *)

type lookup_context =
| LKSymbolOnly
| LKModule
| LKOption
| LKCode

type position = string & int & int


type push_query =
  { 
    push_kind: push_kind;
    push_line: int;
    push_column: int;
    push_peek_only: bool;
    //Either a string: Just the raw content of a document fragment
    //Or a parsed document fragment and the raw content it corresponds to
    push_code_or_decl: either string (FStarC.Parser.AST.decl & PI.code_fragment)
  }

type lookup_symbol_range = json

type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

(* Types concerning repl *)
type repl_depth_t = TcEnv.tcenv_depth_t & int
type optmod_t = option Syntax.Syntax.modul

type timed_fname =
  { tf_fname: string;
    tf_modtime: time_of_day }

(** Every snapshot pushed in the repl stack is annotated with one of these.  The
``LD``-prefixed (“Load Dependency”) onces are useful when loading or updating
dependencies, as they carry enough information to determine whether a dependency
is stale. **)
type repl_task =
  | LDInterleaved of timed_fname & timed_fname (* (interface * implementation) *)
  | LDSingle of timed_fname (* interface or implementation *)
  | LDInterfaceOfCurrentFile of timed_fname (* interface *)
  | PushFragment of either PI.input_frag FStarC.Parser.AST.decl (* code fragment *)
                  & push_kind (* FullCheck, LaxCheck, SyntaxCheck *)
                  & list json (* any warnings that were raised while checking this fragment *)
  | Noop (* Used by compute, PushPartialCheckedFile *)

type full_buffer_request_kind =
  | Full : full_buffer_request_kind
  | Lax : full_buffer_request_kind
  | Cache : full_buffer_request_kind
  | ReloadDeps : full_buffer_request_kind
  | VerifyToPosition of position
  | LaxToPosition of position
  
type query' =
| Exit
| DescribeProtocol
| DescribeRepl
| Segment of string (* File contents *)
| Pop
| Push of push_query
| PushPartialCheckedFile of string (* long declaration name *)
| VfsAdd of option string (* fname *) & string (* contents *)
| AutoComplete of string & completion_context
| Lookup of string & lookup_context & option position & list string & option lookup_symbol_range
| Compute of string & option (list FStarC.TypeChecker.Env.step)
| Search of string
| GenericError of string
| ProtocolViolation of string
// FullBuffer: To check the full contents of a document.
// FStarC.Interactive.Incremental parses it into chunks and turns this into several Push queries
| FullBuffer of string & full_buffer_request_kind & bool //bool is with_symbol
// Callback: This is an internal query, it cannot be raised by a client.
// It is useful to inject operations into the query stream.
// e.g., Incremental uses it print progress messages to the client in between
// processing a stream of Pushes that result from a chunking a FullBuffer
| Callback of callback_t
// Format: pretty-print the F* code in the selection
| Format of string
| RestartSolver
// Cancel: Cancel any remaining pushes that are at or beyond the provided position.
// Cancel all requests if the position is None
| Cancel of option position
and query = { qq: query'; qid: string }
and callback_t = repl_state -> (query_status & list json) & either repl_state int
and repl_state = {
    repl_line: int;
    repl_column: int;
    repl_fname: string;
    repl_deps_stack: repl_stack_t;
    repl_curmod: optmod_t;
    repl_env: TcEnv.env;
    repl_stdin: stream_reader;
    repl_names: CTable.table;
    repl_buffered_input_queries: list query;
    repl_lang:FStarC.Universal.lang_decls_t;
}
and repl_stack_t = list repl_stack_entry_t
and repl_stack_entry_t  = repl_depth_t & (repl_task & repl_state)

// Global repl_state, keeping state of different buffers
type grepl_state = { grepl_repls: psmap repl_state; grepl_stdin: stream_reader }

val query_to_string : query -> string

val string_of_repl_task : repl_task -> string

val json_of_issue : FStarC.Errors.issue -> json

val js_pushkind : json -> push_kind
val js_reductionrule : json -> FStarC.TypeChecker.Env.step
val js_optional_completion_context : option json -> completion_context
val js_optional_lookup_context : option json -> lookup_context

val query_needs_current_module : query' -> bool
val interactive_protocol_vernum : int
val interactive_protocol_features : list string
