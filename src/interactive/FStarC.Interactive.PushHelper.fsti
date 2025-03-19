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

(* FStarC.Interactive.Lsp and FStarC.Interactive.Ide need to push various *
 * text fragments and update state; this file collects helpers for them *)

module FStarC.Interactive.PushHelper
open FStarC
open FStarC.Effect
open FStarC.Util
open FStarC.Ident
open FStarC.TypeChecker.Env
open FStarC.Interactive.JsonHelper
open FStarC.Interactive.Ide.Types

module CTable = FStarC.Interactive.CompletionTable
module TcEnv = FStarC.TypeChecker.Env

type ctx_depth_t = int & int & solver_depth_t & int
type deps_t = FStarC.Parser.Dep.deps
type either_replst = either repl_state repl_state

// Name tracking; taken directly from IDE
type name_tracking_event =
| NTAlias of lid (* host *) & ident (* alias *) & lid (* aliased *)
| NTOpen of lid (* host *) & FStarC.Syntax.Syntax.open_module_or_namespace (* opened *)
| NTInclude of lid (* host *) & lid (* included *)
| NTBinding of either FStarC.Syntax.Syntax.binding TcEnv.sig_binding

val repl_stack : ref repl_stack_t
val set_check_kind : env_t -> push_kind -> env_t

// Push an Pop, directly copied over from IDE
val push_repl : string -> option push_kind -> repl_task -> repl_state -> repl_state
val add_issues_to_push_fragment (issues: list json) : unit
val pop_repl : string -> repl_state -> repl_state

// Factored out from IDE for use by LSP as well
val deps_and_repl_ld_tasks_of_our_file : string -> list string & list repl_task & deps_t

// Core functionality, directly copied over from IDE
val run_repl_task 
: optmod_t -> env_t -> repl_task -> FStarC.Universal.lang_decls_t ->
  optmod_t & env_t & FStarC.Universal.lang_decls_t

// Factored out from IDE for use by LSP as well
val update_task_timestamps : repl_task -> repl_task
val add_module_completions : string -> list string -> CTable.table -> CTable.table

val track_name_changes : env_t -> env_t & (env_t -> env_t & list name_tracking_event)
val commit_name_tracking : repl_state -> list name_tracking_event -> repl_state

// Lax-check the whole file; used on didOpen and didSave
// returns a diagnostic (only on error) along with the repl_state
val full_lax : string -> repl_state -> option assoct & repl_state
