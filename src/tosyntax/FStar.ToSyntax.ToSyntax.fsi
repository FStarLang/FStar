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
module FStar.ToSyntax.ToSyntax

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Syntax.Const
open FStar.Parser
open FStar.ToSyntax.Env
open FStar.Parser.AST
open FStar.Ident

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

val desugar_file: env -> file -> env * list<S.modul>
val desugar_decls: env -> list<AST.decl> -> env * sigelts
val desugar_partial_modul: option<S.modul> -> env -> AST.modul -> env * Syntax.modul
val desugar_term: env -> term -> S.term

(* private *) val desugar_modul : env -> AST.modul -> env * Syntax.modul
(* private *) val close : env -> term -> term

val add_modul_to_env: Syntax.modul -> env -> env
