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
module FStarC.ToSyntax.ToSyntax
open FStarC.Effect

open FStarC
open FStarC.Util
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.Util
open FStarC.Parser
open FStarC.Syntax.DsEnv
open FStarC.Parser.AST
open FStarC.Ident

module S = FStarC.Syntax.Syntax

type extension_tosyntax_decl_t = env -> FStarC.Dyn.dyn -> lids:list lident -> Range.range -> list sigelt'
val register_extension_tosyntax (lang_name:string) (cb:extension_tosyntax_decl_t) : unit

val desugar_term:            env -> term -> S.term
val desugar_machine_integer: env -> repr:string
                           -> (FStarC.Const.signedness & FStarC.Const.width)
                           -> Range.range -> Syntax.term
val free_vars (tvars_only:bool) (e:env) (t:term) : list ident
val close:                   env -> term -> term

val ast_modul_to_modul:          AST.modul -> withenv Syntax.modul
val decls_to_sigelts:            list AST.decl -> withenv sigelts
val partial_ast_modul_to_modul:  option S.modul -> AST.modul -> withenv Syntax.modul

val add_partial_modul_to_env: Syntax.modul
                    -> module_inclusion_info
                    -> erase_univs:(S.term -> S.term)
                    -> withenv unit
val add_modul_to_env: Syntax.modul
                    -> module_inclusion_info
                    -> erase_univs:(S.term -> S.term)
                    -> withenv unit

val parse_attr_with_list : bool -> S.term -> lident -> option (list int & Range.range) & bool

val get_fail_attr1 : bool -> S.term       -> option (list int & Range.range & bool)
val get_fail_attr  : bool -> list S.term -> option (list int & Range.range & bool)
