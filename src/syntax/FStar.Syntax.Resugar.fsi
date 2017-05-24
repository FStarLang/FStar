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
module FStar.Syntax.Resugar //we should rename FStar.ToSyntax to something else

open FStar.All
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Util
open FStar.Const
open FStar.Range

module I = FStar.Ident
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module A  = FStar.Parser.AST
module C = FStar.Syntax.Const
module U = FStar.Syntax.Util
module BU = FStar.Util
module Range = FStar.Range

val resugar_term: S.term -> A.term
val resugar_sigelt: S.sigelt-> option<A.decl>
val resugar_comp: S.comp -> A.term
val resugar_pat: S.pat -> A.pattern
val resugar_universe: S.universe -> Range.range -> A.term
val resugar_binder: S.binder -> Range.range -> A.binder
val resugar_tscheme: S.tscheme -> A.decl
val resugar_eff_decl: bool -> Range.range -> list<S.qualifier> -> eff_decl -> A.decl