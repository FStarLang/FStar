(*
   Copyright 2008-2014 Microsoft Research

   Authors: Jonathan Protzenko, Nikhil Swamy

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
module FStarC.TypeChecker.DMFF
open FStarC.Effect
open FStarC.TypeChecker
open FStarC.Syntax.Syntax

new val env : Type0

val empty : Env.env -> (sconst -> ML typ) -> ML env
val gen_wps_for_free: Env.env -> binders -> bv -> term -> eff_decl -> ML (sigelts & eff_decl)
val get_env: env -> ML Env.env
val set_env : env -> Env.env -> ML env
val double_star: typ -> ML typ
val star_type: env -> typ -> ML typ
val star_expr: env -> term -> ML (typ & term & term)
val trans_F  : env -> typ -> term -> ML term
val recheck_debug : string -> FStarC.TypeChecker.Env.env -> term -> ML term
val cps_and_elaborate : FStarC.TypeChecker.Env.env -> eff_decl -> ML (list sigelt & eff_decl & option sigelt)
