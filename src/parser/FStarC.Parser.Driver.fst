(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module FStarC.Parser.Driver
open FStarC.Effect

open FStarC
open FStarC.Parser
open FStarC.Parser.AST
open FStarC.Parser.ParseIt
open FStarC.Errors
open FStarC.Class.Show

let is_cache_file (fn: string) = Filepath.get_file_extension fn = ".cache"

let parse_fragment lang_opt (frag: ParseIt.input_frag) : fragment =
    match ParseIt.parse lang_opt (Toplevel frag) with
    | ASTFragment (Inl modul, _) -> //interactive mode: module
        Modul modul
    | ASTFragment (Inr [], _) -> //interactive mode: blank space
        Empty
    | ASTFragment (Inr decls, _) -> //interactive mode: more decls
        Decls decls
    | IncrementalFragment (decls, _, _) -> 
        DeclsWithContent decls
    | ParseError (e, msg, r) ->
        raise_error r e msg
    | Term _ ->
        failwith "Impossible: parsing a Toplevel always results in an ASTFragment"

let maybe_dump_module (m:modul) = 
    match m with
    | Module {mname; decls}
    | Interface {mname; decls} ->
      if FStarC.Options.dump_module (Ident.string_of_lid mname)
      then (
        Format.print2 "Parsed module %s\n%s\n"
            (show mname)
            (List.map show decls |> String.concat "\n")
      )
(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
let parse_file fn =
    match ParseIt.parse None (Filename fn) with
    | ASTFragment (Inl ast, comments) ->
        ast, comments
    | ASTFragment (Inr _ , _) ->
        let msg = Format.fmt1 "%s: expected a module\n" fn in
        let r = Range.dummyRange in
        raise_error r Errors.Fatal_ModuleExpected msg
    | ParseError (e, msg, r) ->
        raise_error r e msg
    | Term _ ->
        failwith "Impossible: parsing a Filename always results in an ASTFragment"

