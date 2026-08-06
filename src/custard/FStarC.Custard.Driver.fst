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
module Dep     = FStarC.Parser.Dep
module UF      = FStarC.Syntax.Unionfind
module Krml    = FStarC.Custard.PrintKrml
module Extract = FStarC.Custard.Extract
module Find    = FStarC.Find
module Layout  = FStarC.Custard.Layout
module OCaml   = FStarC.Custard.PrintOCaml
module Rename  = FStarC.Custard.Rename
module Simplify = FStarC.Custard.Simplify
module Ident   = FStarC.Ident
module TcEnv   = FStarC.TypeChecker.Env

let entrypoints () =
  Options.custard_entries () |> List.map Ident.lid_of_str

let main_entry () : ML (option Ident.lident) =
  match Options.custard_main () with
  | Some s -> Some (Ident.lid_of_str s)
  | None -> None

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

let run (deps:Dep.deps) (env:TcEnv.env) : ML unit =
  let main = main_entry () in
  (* [--custard_main] is a root too, so that the common case needs only one
     option. *)
  let roots = entrypoints () @ (match main with Some l -> [l] | None -> []) in
  if Nil? roots then
    E.raise_error0 E.Fatal_OptionsNotCompatible [
      text "--codegen Custard requires at least one --custard_entry or \
            --custard_main.";
      text "Custard is a whole-program compiler: it extracts exactly the \
                   definitions reachable from the entry points."
    ];
  check_entrypoints env roots;
  (* Looking definitions up in the environment instantiates their universes,
     which needs the union-find; by the time a backend runs it has been put in
     read-only mode.  The ML extraction does the same thing. *)
  let prog = UF.with_uf_enabled (fun () -> Extract.run (Extract.init deps env) roots main) in
  (* Phase 3/4: erasure, newtype collapse and cast elimination (section 5). *)
  let prog = Layout.run prog in
  (* Effect-guarded simplification (sections 6 and 7.3). *)
  let prog = Simplify.run prog in
  (* Last: the passes above invent names, and the whole point is that what a
     reader sees is stable under everything that happened before. *)
  let prog = Rename.run prog in
  if Options.custard_dump_ir () then
    Format.print_string (program_to_string prog ^ "\n");
  (* Custard emits one file for the whole program, so -o is unambiguous here,
     unlike in the per-module backends. *)
  let krml = Options.custard_backend () = "Krml" in
  let ofile =
    match Options.output_to () with
    | Some fn -> fn
    | None -> Find.prepend_output_dir (if krml then "Custard.krml" else "Custard.ml")
  in
  if krml
  then Krml.write_program ofile prog
  else BU.write_file ofile (OCaml.print_program prog)
