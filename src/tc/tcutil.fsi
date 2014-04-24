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
// (c) Microsoft Corporation. All rights reserved

module Microsoft.FStar.Tc.Util

open Microsoft.FStar
open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Tc.Env

val t_bool : typ
val t_unit : typ
val typing_const : env -> sconst -> typ
val push_tparams : env -> list<tparam> -> env
val new_kvar : env -> kind          
val new_tvar : env -> kind -> typ
val new_evar : env -> typ -> exp
val normalize : env -> typ -> typ
val keq : env -> kind -> kind -> unit
val teq : env -> typ -> typ -> unit
val check_and_ascribe : env -> exp -> typ -> exp
val pat_as_exps: env -> pat -> list<exp>
val generalize: Util.uvars -> exp -> typ -> (exp * typ)

val destruct_function_typ : env -> typ -> exp -> bool -> (typ*exp)
val destruct_poly_typ: env -> typ -> exp -> (typ*exp) 
val destruct_tcon_kind: env -> kind -> typ -> kind
val destruct_dcon_kind: env -> kind -> typ -> (kind*typ)
