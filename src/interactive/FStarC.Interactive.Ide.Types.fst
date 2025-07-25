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
open FStarC.Effect
open FStarC.List
open FStarC.Range
open FStarC.Getopt
open FStarC.Ident
open FStarC.Errors
open FStarC.Interactive.JsonHelper

open FStarC.Universal
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common
open FStarC.Interactive
open FStarC.Parser.ParseIt
open FStarC.Class.Show
open FStarC.Json

module SS = FStarC.Syntax.Syntax

let initial_range =
  Range.mk_range "<input>" (Range.mk_pos 1 0) (Range.mk_pos 1 0)

instance showable_push_kind : showable push_kind = {
  show = (function
          | SyntaxCheck -> "SyntaxCheck"
          | LaxCheck -> "LaxCheck"
          | FullCheck -> "FullCheck");
}

(*************************)
(* REPL tasks and states *)
(*************************)

let t0 = Time.get_time_of_day ()

(** Create a timed_fname with a dummy modtime **)
let dummy_tf_of_fname fname =
  { tf_fname = fname;
    tf_modtime = t0 }

let string_of_timed_fname { tf_fname = fname; tf_modtime = modtime } =
  if modtime = t0 then Format.fmt1 "{ %s }" fname
  else Format.fmt2 "{ %s; %s }" fname (show modtime)

let string_of_repl_task = function
  | LDInterleaved (intf, impl) ->
    Format.fmt2 "LDInterleaved (%s, %s)" (string_of_timed_fname intf) (string_of_timed_fname impl)
  | LDSingle intf_or_impl ->
    Format.fmt1 "LDSingle %s" (string_of_timed_fname intf_or_impl)
  | LDInterfaceOfCurrentFile intf ->
    Format.fmt1 "LDInterfaceOfCurrentFile %s" (string_of_timed_fname intf)
  | PushFragment (Inl frag, _, _) ->
    Format.fmt1 "PushFragment { code = %s }" frag.frag_text
  | PushFragment (Inr d, _, _) ->
    Format.fmt1 "PushFragment { decl = %s }" (show d)
  | Noop -> "Noop {}"


let string_of_repl_stack_entry
  : repl_stack_entry_t -> string
  = fun ((depth, i), (task, state)) ->
      Format.fmt "{depth=%s; task=%s}"
                [show i;
                string_of_repl_task task]
                

let string_of_repl_stack s =
  String.concat ";\n\t\t"
                (List.map string_of_repl_stack_entry s)

let repl_state_to_string (r:repl_state)
  : string
  = Format.fmt 
    "{\n\t\
      repl_line=%s;\n\t\
      repl_column=%s;\n\t\
      repl_fname=%s;\n\t\
      repl_cur_mod=%s;\n\t\      
      repl_deps_stack={%s}\n\
     }"
     [show r.repl_line;
      show r.repl_column;
      r.repl_fname;
      (match r.repl_curmod with
       | None -> "None"
       | Some m -> Ident.string_of_lid m.name);
      string_of_repl_stack r.repl_deps_stack]

let push_query_to_string pq =
  let code_or_decl =
    match pq.push_code_or_decl with
    | Inl code -> code
    | Inr (_decl, code) -> code.code
  in
  FStarC.Format.fmt "{ push_kind = %s; push_line = %s; \
               push_column = %s; push_peek_only = %s; push_code_or_decl = %s }"
    [show pq.push_kind; show pq.push_line;
     show pq.push_column;
     show pq.push_peek_only;
     code_or_decl]

let query_to_string (q:query) = match q.qq with
| Exit -> "Exit"
| DescribeProtocol -> "DescribeProtocol"
| DescribeRepl -> "DescribeRepl"
| Segment _ -> "Segment"
| Pop -> "Pop"
| Push pq -> "(Push " ^ push_query_to_string pq ^ ")"
| PushPartialCheckedFile d -> "(PushPartialCheckedFile " ^ d ^ ")"
| VfsAdd _ -> "VfsAdd"
| AutoComplete _ -> "AutoComplete"
| Lookup(s, _lc, pos, features, _sr) ->
  Format.fmt3 "(Lookup %s %s [%s])"
              s (match pos with
                 | None -> "None"
                 | Some (f, i, j) ->
                   Format.fmt3 "(%s, %s, %s)"
                              f (show i) (show j))
                (String.concat "; " features)
| Compute _ -> "Compute"
| Search _ -> "Search"
| GenericError _ -> "GenericError"
| ProtocolViolation _ -> "ProtocolViolation"
| FullBuffer _ -> "FullBuffer"
| Callback _ -> "Callback"
| Format _ -> "Format"
| RestartSolver -> "RestartSolver"
| Cancel _ -> "Cancel"

let query_needs_current_module = function
  | Exit | DescribeProtocol | DescribeRepl | Segment _
  | Pop | Push { push_peek_only = false } | VfsAdd _
  | GenericError _ | ProtocolViolation _
  | PushPartialCheckedFile _
  | FullBuffer _ | Callback _ | Format _ | RestartSolver | Cancel _ -> false
  | Push _ | AutoComplete _ | Lookup _ | Compute _ | Search _ -> true

let interactive_protocol_vernum = 2

let interactive_protocol_features =
  ["autocomplete"; "autocomplete/context";
   "compute"; "compute/reify"; "compute/pure-subterms";
   "describe-protocol"; "describe-repl"; "exit";
   "lookup"; "lookup/context"; "lookup/documentation"; "lookup/definition";
   "peek"; "pop"; "push"; "push-partial-checked-file"; "search"; "segment";
   "vfs-add"; "tactic-ranges"; "interrupt"; "progress";
   "full-buffer"; "format"; "restart-solver"; "cancel"]

let json_of_issue_level i =
  JsonStr (match i with
           | ENotImplemented -> "not-implemented"
           | EInfo -> "info"
           | EWarning -> "warning"
           | EError -> "error")

let json_of_issue issue =
  let r = Option.map Range.refind_range issue.issue_range in
  JsonAssoc <|
     [("level", json_of_issue_level issue.issue_level)]
    @(match issue.issue_number with
      | None -> []
      | Some n -> [("number", JsonInt n)])
    @[("message", JsonStr (format_issue' false issue));
      ("ranges", JsonList
                   ((match r with
                     | None -> []
                     | Some r -> [json_of_use_range r]) @
                    (match r with
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
  | "beta" -> FStarC.TypeChecker.Env.Beta
  | "delta" -> FStarC.TypeChecker.Env.UnfoldUntil SS.delta_constant
  | "iota" -> FStarC.TypeChecker.Env.Iota
  | "zeta" -> FStarC.TypeChecker.Env.Zeta
  | "reify" -> FStarC.TypeChecker.Env.Reify
  | "pure-subterms" -> FStarC.TypeChecker.Env.PureSubtermsWithinComputations
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

