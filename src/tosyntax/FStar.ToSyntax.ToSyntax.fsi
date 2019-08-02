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
open FStar.ST
open FStar.All

open FStar
open FStar.Util
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Util
open FStar.Parser
open FStar.Syntax.DsEnv
open FStar.Parser.AST
open FStar.Ident

module S = FStar.Syntax.Syntax
module U = FStar.Syntax.Util

val as_interface:            AST.modul -> AST.modul
val desugar_term:            env -> term -> S.term
val desugar_machine_integer: env -> repr:string
                           -> (FStar.Const.signedness * FStar.Const.width)
                           -> Range.range -> Syntax.term
val close:                   env -> term -> term

val ast_modul_to_modul:          AST.modul -> withenv<Syntax.modul>
val decls_to_sigelts:            list<AST.decl> -> withenv<sigelts>
val partial_ast_modul_to_modul:  option<S.modul> -> AST.modul -> withenv<Syntax.modul>

val add_modul_to_env: Syntax.modul
                    -> module_inclusion_info
                    -> erase_univs:(S.term -> S.term)
                    -> withenv<unit>

val parse_attr_with_list : bool -> S.term -> lident -> option<(list<int>)> * bool

val get_fail_attr : bool -> S.term -> option<(list<int> * bool)>
