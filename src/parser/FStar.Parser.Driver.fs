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
open FStar.All

open FStar
open FStar.Parser
open FStar.Parser.AST
open FStar.Parser.Parse
open FStar.Util
open FStar.Errors

let is_cache_file (fn: string) = Util.get_file_extension fn = ".cache"

type fragment =
    | Empty
    | Modul of AST.modul // an entire module or interface -- unspecified
    | Decls of list<AST.decl> // a partial set of declarations

(* TODO: take fsdocs into account ! *)
let parse_fragment frag : fragment =
    match ParseIt.parse (Inr frag) with
    | Inl ({ ParseIt.frag = Inl [] }) ->
      Empty

    (* interactive mode: module *)
    | Inl ({ ParseIt.frag = Inl [modul]}) ->
      Modul modul

    (* interactive mode: more decls *)
    | Inl ({ParseIt.frag = Inr decls}) ->
      Decls decls

    | Inl ({ParseIt.frag = Inl _}) ->
      raise (Err("Refusing to check more than one module at a time incrementally"))

    | Inr (msg,r) ->
      raise (Error(msg, r))

(* Returns a non-desugared AST (as in [parser/ast.fs]) or aborts. *)
let parse_file fn =
  match ParseIt.parse (Inl fn) with
  | Inl ({ParseIt.frag = Inl ast; ParseIt.comments = comments ; ParseIt.fsdocs = fsdocs}) ->
    ast, fsdocs, comments

  | Inl ({ ParseIt.frag = Inr _}) ->
    let msg = Util.format1 "%s: expected a module\n" fn in
    let r = Range.dummyRange in
    raise (Error(msg, r))

  | Inr (msg, r) ->
    raise (Error(msg, r))

