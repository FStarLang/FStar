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
module FStarC.Syntax.Resugar //we should rename FStarC.ToSyntax to something else

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Util
open FStarC.Const
open FStarC.Range.Type

module Range = FStarC.Range.Type
module S  = FStarC.Syntax.Syntax
module A  = FStarC.Parser.AST
module DsEnv = FStarC.Syntax.DsEnv

val resugar_term: S.term -> A.term
val resugar_sigelt: S.sigelt -> option A.decl
val resugar_comp: S.comp -> A.term
val resugar_pat: S.pat -> FlatSet.t S.bv -> A.pattern
val resugar_universe: S.universe -> Range.range -> A.term
val resugar_binder: S.binder -> Range.range -> A.binder
val resugar_tscheme: S.tscheme -> A.decl
val resugar_eff_decl: eff_decl -> A.decl

val resugar_term': DsEnv.env -> S.term -> A.term
val resugar_sigelt': DsEnv.env -> S.sigelt -> option A.decl
val resugar_comp': DsEnv.env -> S.comp -> A.term
val resugar_pat': DsEnv.env -> S.pat -> FlatSet.t S.bv -> A.pattern
val resugar_universe': DsEnv.env -> S.universe -> Range.range -> A.term
val resugar_binder': DsEnv.env -> S.binder -> Range.range -> A.binder
val resugar_tscheme': DsEnv.env -> S.tscheme -> A.decl
val resugar_eff_decl': DsEnv.env -> eff_decl -> A.decl
