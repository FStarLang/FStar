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

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util

open FStar.Absyn
open FStar.Absyn.Syntax


let is_cache_file (fn: string) = Util.get_file_extension fn = ".cache"

type fragment =
    | Empty
    | Modul of AST.modul
    | Decls of list<AST.decl>

let parse_fragment frag : fragment =
    match ParseIt.parse (Inr frag) with
    | Inl (Inl []) ->
      Empty

    | Inl (Inl [modul]) -> //interactive mode: module
      Modul modul

    | Inl (Inr decls) -> //interactive mode: more decls
      Decls decls 
      
//      (Desugar.desugar_decls env decls)
//
//      let env, modul = Desugar.desugar_partial_modul curmod env modul in
//      Modul (env, modul)
//
//    | Inl (Inr decls) -> //interactive mode: more decls
//      Decls (Desugar.desugar_decls env decls)

    | Inl (Inl _) ->
      raise (Absyn.Syntax.Err("Refusing to check more than one module at a time incrementally"))

    | Inr (msg,r) ->
      raise (Absyn.Syntax.Error(msg, r))

(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
let parse_file fn =
  match ParseIt.parse (Inl fn) with
  | Inl (Inl ast) ->
    ast

  | Inl (Inr _) ->
    Util.print1_error "%s: expected a module\n" fn;
    exit 1

  | Inr (msg, r) ->
    Util.print_string <| Print.format_error r msg;
    exit 1