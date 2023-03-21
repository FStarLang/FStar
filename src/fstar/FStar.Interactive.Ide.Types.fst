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

module FStar.Interactive.Ide.Types
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Compiler.Range
open FStar.Compiler.Util
open FStar.Getopt
open FStar.Ident
open FStar.Errors
open FStar.Interactive.JsonHelper

open FStar.Universal
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common
open FStar.Interactive
open FStar.Parser.ParseIt

module SS = FStar.Syntax.Syntax
module DsEnv = FStar.Syntax.DsEnv
module TcErr = FStar.TypeChecker.Err
module TcEnv = FStar.TypeChecker.Env
module CTable = FStar.Interactive.CompletionTable
module PI = FStar.Parser.ParseIt
module U = FStar.Compiler.Util

(***********************)
(* Global state setup *)
(***********************)
let initial_range =
  Range.mk_range "<input>" (Range.mk_pos 1 0) (Range.mk_pos 1 0)



type completion_context =
| CKCode
| CKOption of bool (* #set-options (false) or #reset-options (true) *)
| CKModuleOrNamespace of bool (* modules *) * bool (* namespaces *)

type lookup_context =
| LKSymbolOnly
| LKModule
| LKOption
| LKCode

type position = string * int * int

type push_kind = | SyntaxCheck | LaxCheck | FullCheck

type push_query =
  { 
    push_kind: push_kind;
    push_line: int;
    push_column: int;
    push_peek_only: bool;
    //Either a string: Just the raw content of a document fragment
    //Or a parsed document fragment and the raw content it corresponds to
    push_code_or_decl: either string (FStar.Parser.AST.decl * PI.code_fragment)
  }

type lookup_symbol_range = json

type query_status = | QueryOK | QueryNOK | QueryViolatesProtocol

(* Types concerning repl *)
type repl_depth_t = TcEnv.tcenv_depth_t * int
type optmod_t = option Syntax.Syntax.modul

type timed_fname =
  { tf_fname: string;
    tf_modtime: time }

(** Every snapshot pushed in the repl stack is annotated with one of these.  The
``LD``-prefixed (“Load Dependency”) onces are useful when loading or updating
dependencies, as they carry enough information to determine whether a dependency
is stale. **)
type repl_task =
  | LDInterleaved of timed_fname * timed_fname (* (interface * implementation) *)
  | LDSingle of timed_fname (* interface or implementation *)
  | LDInterfaceOfCurrentFile of timed_fname (* interface *)
  | PushFragment of either PI.input_frag FStar.Parser.AST.decl * push_kind (* code fragment *)
  | Noop (* Used by compute *)

type full_buffer_request_kind =
  | Full : full_buffer_request_kind
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
| VfsAdd of option string (* fname *) * string (* contents *)
| AutoComplete of string * completion_context
| Lookup of string * lookup_context * option position * list string * option lookup_symbol_range
| Compute of string * option (list FStar.TypeChecker.Env.step)
| Search of string
| GenericError of string
| ProtocolViolation of string
| FullBuffer of string & full_buffer_request_kind
| Callback of callback_t
| Format of string
| Cancel of option position
and query = { qq: query'; qid: string }
and callback_t = repl_state -> (query_status * list json) * either repl_state int
and repl_state = {
    repl_line: int;
    repl_column: int;
    repl_fname: string;
    repl_deps_stack: repl_stack_t;
    repl_curmod: optmod_t;
    repl_env: TcEnv.env;
    repl_stdin: stream_reader;
    repl_names: CTable.table;
    repl_buffered_input_queries: list query
}
and repl_stack_t = list repl_stack_entry_t
and repl_stack_entry_t  = repl_depth_t * (repl_task * repl_state)

// Global repl_state, keeping state of different buffers
type grepl_state = { grepl_repls: U.psmap repl_state; grepl_stdin: stream_reader }


(*************************)
(* REPL tasks and states *)
(*************************)

let t0 = Util.now ()

(** Create a timed_fname with a dummy modtime **)
let dummy_tf_of_fname fname =
  { tf_fname = fname;
    tf_modtime = t0 }

let string_of_timed_fname { tf_fname = fname; tf_modtime = modtime } =
  if modtime = t0 then Util.format1 "{ %s }" fname
  else Util.format2 "{ %s; %s }" fname (string_of_time modtime)

let string_of_repl_task = function
  | LDInterleaved (intf, impl) ->
    Util.format2 "LDInterleaved (%s, %s)" (string_of_timed_fname intf) (string_of_timed_fname impl)
  | LDSingle intf_or_impl ->
    Util.format1 "LDSingle %s" (string_of_timed_fname intf_or_impl)
  | LDInterfaceOfCurrentFile intf ->
    Util.format1 "LDInterfaceOfCurrentFile %s" (string_of_timed_fname intf)
  | PushFragment (Inl frag, _) ->
    Util.format1 "PushFragment { code = %s }" frag.frag_text
  | PushFragment (Inr d, _) ->
    Util.format1 "PushFragment { decl = %s }" (FStar.Parser.AST.decl_to_string d)
  | Noop -> "Noop {}"

module BU = FStar.Compiler.Util

let string_of_repl_stack_entry
  : repl_stack_entry_t -> string
  = fun ((depth, i), (task, state)) ->
      BU.format "{depth=%s; task=%s}"
                [string_of_int i;
                string_of_repl_task task]
                

let string_of_repl_stack s =
  String.concat ";\n\t\t"
                (List.map string_of_repl_stack_entry s)

let repl_state_to_string (r:repl_state)
  : string
  = BU.format 
    "{\n\t\
      repl_line=%s;\n\t\
      repl_column=%s;\n\t\
      repl_fname=%s;\n\t\
      repl_cur_mod=%s;\n\t\      
      repl_deps_stack={%s}\n\
     }"
     [string_of_int r.repl_line;
      string_of_int r.repl_column;
      r.repl_fname;
      (match r.repl_curmod with
       | None -> "None"
       | Some m -> Ident.string_of_lid m.name);
      string_of_repl_stack r.repl_deps_stack]


let push_query_to_string pq =
  let pk =
    match pq.push_kind with
    | SyntaxCheck -> "SyntaxCheck"
    | LaxCheck -> "LaxCheck"
    | FullCheck -> "FullCheck"
  in
  let code_or_decl =
    match pq.push_code_or_decl with
    | Inl code -> code
    | Inr (_decl, code) -> code.code
  in
  FStar.Compiler.Util.format "{ push_kind = %s; push_line = %s; \
               push_column = %s; push_peek_only = %s; push_code_or_decl = %s }"
    [pk; string_of_int pq.push_line;
     string_of_int pq.push_column;
     string_of_bool pq.push_peek_only;
     code_or_decl]

let query_to_string q = match q.qq with
| Exit -> "Exit"
| DescribeProtocol -> "DescribeProtocol"
| DescribeRepl -> "DescribeRepl"
| Segment _ -> "Segment"
| Pop -> "Pop"
| Push pq -> "(Push " ^ push_query_to_string pq ^ ")"
| VfsAdd _ -> "VfsAdd"
| AutoComplete _ -> "AutoComplete"
| Lookup _ -> "Lookup"
| Compute _ -> "Compute"
| Search _ -> "Search"
| GenericError _ -> "GenericError"
| ProtocolViolation _ -> "ProtocolViolation"
| FullBuffer _ -> "FullBuffer"
| Callback _ -> "Callback"
| Format _ -> "Format"
| Cancel _ -> "Cancel"

let query_needs_current_module = function
  | Exit | DescribeProtocol | DescribeRepl | Segment _
  | Pop | Push { push_peek_only = false } | VfsAdd _
  | GenericError _ | ProtocolViolation _ | FullBuffer _ | Callback _ | Format _ -> false
  | Push _ | AutoComplete _ | Lookup _ | Compute _ | Search _ -> true

let interactive_protocol_vernum = 2

let interactive_protocol_features =
  ["autocomplete"; "autocomplete/context";
   "compute"; "compute/reify"; "compute/pure-subterms";
   "describe-protocol"; "describe-repl"; "exit";
   "lookup"; "lookup/context"; "lookup/documentation"; "lookup/definition";
   "peek"; "pop"; "push"; "search"; "segment";
   "vfs-add"; "tactic-ranges"; "interrupt"; "progress";
   "full-buffer"; "format"; "cancel"]

let json_of_issue_level i =
  JsonStr (match i with
           | ENotImplemented -> "not-implemented"
           | EInfo -> "info"
           | EWarning -> "warning"
           | EError -> "error")

let json_of_issue issue =
  JsonAssoc <|
     [("level", json_of_issue_level issue.issue_level)]
    @(match issue.issue_number with
      | None -> []
      | Some n -> [("number", JsonInt n)])
    @[("message", JsonStr (issue_message issue));
      ("ranges", JsonList
                   ((match issue.issue_range with
                     | None -> []
                     | Some r -> [json_of_use_range r]) @
                    (match issue.issue_range with
                     | Some r when def_range r <> use_range r ->
                       [json_of_def_range r]
                     | _ -> [])))]

(*****************************************)
(* Reading queries and writing responses *)
(*****************************************)

let js_pushkind s : push_kind = match js_str s with
  | "syntax" -> SyntaxCheck
  | "lax" -> LaxCheck
  | "full" -> FullCheck
  | _ -> js_fail "push_kind" s

let js_reductionrule s = match js_str s with
  | "beta" -> FStar.TypeChecker.Env.Beta
  | "delta" -> FStar.TypeChecker.Env.UnfoldUntil SS.delta_constant
  | "iota" -> FStar.TypeChecker.Env.Iota
  | "zeta" -> FStar.TypeChecker.Env.Zeta
  | "reify" -> FStar.TypeChecker.Env.Reify
  | "pure-subterms" -> FStar.TypeChecker.Env.PureSubtermsWithinComputations
  | _ -> js_fail "reduction rule" s

let js_optional_completion_context k =
  match k with
  | None -> CKCode
  | Some k ->
    match js_str k with
    | "symbol" // Backwards compatibility
    | "code" -> CKCode
    | "set-options" -> CKOption false
    | "reset-options" -> CKOption true
    | "open"
    | "let-open" -> CKModuleOrNamespace (true, true)
    | "include"
    | "module-alias" -> CKModuleOrNamespace (true, false)
    | _ ->
      js_fail "completion context (code, set-options, reset-options, \
open, let-open, include, module-alias)" k

let js_optional_lookup_context k =
  match k with
  | None -> LKSymbolOnly // Backwards-compatible default
  | Some k ->
    match js_str k with
    | "symbol-only" -> LKSymbolOnly
    | "code" -> LKCode
    | "set-options"
    | "reset-options" -> LKOption
    | "open"
    | "let-open"
    | "include"
    | "module-alias" -> LKModule
    | _ ->
      js_fail "lookup context (symbol-only, code, set-options, reset-options, \
open, let-open, include, module-alias)" k

