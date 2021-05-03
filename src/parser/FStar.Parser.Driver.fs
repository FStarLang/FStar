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
#light "off"
module FStar.Parser.Driver
open FStar.Pervasives
open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Parser.ParseIt
open FStar.Util
open FStar.Errors

let is_cache_file (fn: string) = Util.get_file_extension fn = ".cache"

type fragment =
    | Empty
    | Modul of AST.modul // an entire module or interface -- unspecified
    | Decls of list<AST.decl> // a partial set of declarations

let parse_fragment (frag: ParseIt.input_frag) : fragment =
    match ParseIt.parse (Toplevel frag) with
    | ASTFragment (Inl modul, _) -> //interactive mode: module
        Modul modul
    | ASTFragment (Inr [], _) -> //interactive mode: blank space
        Empty
    | ASTFragment (Inr decls, _) -> //interactive mode: more decls
        Decls decls
    | ParseError (e, msg, r) ->
        raise_error (e, msg) r
    | Term _ ->
        failwith "Impossible: parsing a Toplevel always results in an ASTFragment"

(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
let parse_file fn =
    match ParseIt.parse (Filename fn) with
    | ASTFragment (Inl ast, comments) ->
        ast, comments
    | ASTFragment (Inr _ , _) ->
        let msg = Util.format1 "%s: expected a module\n" fn in
        let r = Range.dummyRange in
        raise_error (Errors.Fatal_ModuleExpected, msg) r
    | ParseError (e, msg, r) ->
        raise_error (e, msg) r
    | Term _ ->
        failwith "Impossible: parsing a Filename always results in an ASTFragment"

