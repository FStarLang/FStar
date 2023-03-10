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

module FStar.Interactive.ReplState
open FStar
open FStar.Compiler
open FStar.Errors
open FStar.Compiler.Util
open FStar.Compiler.Range
open FStar.TypeChecker.Env

module U = FStar.Compiler.Util
module TcEnv = FStar.TypeChecker.Env
module PI = FStar.Parser.ParseIt
module CTable = FStar.Interactive.CompletionTable


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
  | PushFragment of either PI.input_frag FStar.Parser.AST.decl (* code fragment *)
  | Noop (* Used by compute *)

type repl_state = { repl_line: int; repl_column: int; repl_fname: string;
                    repl_deps_stack: repl_stack_t;
                    repl_curmod: optmod_t;
                    repl_env: TcEnv.env;
                    repl_stdin: stream_reader;
                    repl_names: CTable.table }
and repl_stack_t = list repl_stack_entry_t
and repl_stack_entry_t = repl_depth_t * (repl_task * repl_state)

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
  | PushFragment (Inl frag) ->
    Util.format1 "PushFragment { code = %s }" frag.frag_text
  | PushFragment (Inr d) ->
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
