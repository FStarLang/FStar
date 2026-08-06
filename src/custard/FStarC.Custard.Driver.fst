(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.Custard.Driver

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Custard.Syntax
open FStarC.Errors.Msg

module BU    = FStarC.Util
module E     = FStarC.Errors
module Ident = FStarC.Ident
module TcEnv = FStarC.TypeChecker.Env

let entrypoints () =
  Options.custard_entries () |> List.map Ident.lid_of_str

(* Check that every requested entry point actually resolves to a definition we
   can see.  Getting this wrong is by far the most likely user error, and the
   resulting "empty program" would otherwise be silent. *)
let check_entrypoints (env:TcEnv.env) (roots:list Ident.lident) : ML unit =
  roots |> List.iter (fun l ->
    match TcEnv.lookup_sigelt env l with
    | Some _ -> ()
    | None ->
      E.log_issue0 E.Error_CustardEntryNotFound [
        text ("Custard entry point " ^ Ident.string_of_lid l ^ " is not in scope.");
        text "Make sure the module defining it is among the input files."
      ])

let run (env:TcEnv.env) : ML unit =
  let roots = entrypoints () in
  if Nil? roots then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "--codegen Custard requires at least one --custard_entry.";
      text "Custard is a whole-program compiler: it extracts exactly the \
                   definitions reachable from the entry points."
    ];
  check_entrypoints env roots;
  (* M0: the extraction loop is not implemented yet; we only produce the empty
     program so the plumbing can be exercised end to end. *)
  let prog : program = [] in
  if Options.custard_dump_ir () then
    Format.print_string (program_to_string prog)
