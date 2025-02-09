(*
   Copyright 2023  Nikhil Swamy and Microsoft Research

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

module FStarC.Interactive.Incremental
open FStar.Pervasives
open FStarC.Effect
open FStarC.List
open FStar open FStarC
open FStarC
open FStarC.Parser.AST
open FStarC.Errors
open FStarC.Interactive.Ide.Types
open FStarC.Util

(* Various kinds of progress messages to print back to the client *)
type fragment_progress =
   | FullBufferStarted
   | FragmentStarted of decl
   | FragmentSuccess of (decl & FStarC.Parser.ParseIt.code_fragment & push_kind)
   | FragmentFailed of decl
   | FragmentError of list issue
   | FullBufferFinished

(* Translates a full-buffer(qid, code) query by
   1. Parsing the code into its declarations
   2. Finding a prefix of the repl state that matches a prefix of the declarations
   3. Popping away the suffix of the repl state
   4. Pushing the suffix of parsed decls for checking

   It uses the write_full_buffer_fragment_progress callback to issue
   success markers for the prefix of decls that were found in the repl state,
   and issues syntax errors for the suffix of the code that could not be parsed.
*)   
val run_full_buffer (st:repl_state)
                    (qid:string)
                    (code:string)
                    (full:full_buffer_request_kind)
                    (with_symbols:bool)
                    (write_full_buffer_fragment_progress: fragment_progress -> unit)
  : list query & list json

(* Pretty-print the code for reformatting, or return a syntax error *)
val format_code (st:repl_state)
                (code:string)
  : either string (list issue)