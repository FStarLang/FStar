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
#light "off"
module FStar.TypeChecker.DMFF
open FStar.TypeChecker
open FStar.Syntax.Syntax

type env = {
  // The type-checking environment which we abuse to store our DMFF-style types
  // when entering a binder.
  env: FStar.TypeChecker.Env.env;
  // The substitution from every [x: C] to its [x^w: C*].
  subst: list<subst_elt>;
  // Hack to avoid a dependency
  tc_const: sconst -> typ;
}

val empty : Env.env -> (sconst -> typ) -> env
val get_env: env -> Env.env
val gen_wps_for_free: Env.env -> binders -> bv -> term -> eff_decl -> sigelts * eff_decl
val double_star: typ -> typ
val star_type: env -> typ -> typ
val star_expr: env -> term -> typ * term * term
val trans_F  : env -> typ -> term -> term
