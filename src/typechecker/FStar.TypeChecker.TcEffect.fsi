(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.TypeChecker.TcEffect

open FStar.ST
open FStar.Exn
open FStar.All

open FStar
open FStar.Ident

module S = FStar.Syntax.Syntax
module Env = FStar.TypeChecker.Env


val dmff_cps_and_elaborate : Env.env -> S.eff_decl -> (list<S.sigelt> * S.eff_decl * option<S.sigelt>)

val tc_eff_decl : Env.env -> S.eff_decl -> list<S.qualifier> -> S.eff_decl

val tc_lift : Env.env -> S.sub_eff -> Range.range -> S.sub_eff

val tc_effect_abbrev : Env.env -> (lident * S.univ_names * S.binders * S.comp) -> Range.range -> (lident * S.univ_names * S.binders * S.comp)
