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
module FStarC.TypeChecker.Tc
open FStarC.Effect
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env
open FStarC.TypeChecker.Common

val run_postprocess
  (for_extraction : bool)
  (env : env)
  (se : sigelt)
  : sigelt

val check_module: env -> modul -> bool -> modul & env
val load_checked_module: env -> modul -> env
val load_partial_checked_module: env -> modul -> env

val pop_context: env -> string -> env
val push_context: env -> string -> env
val snapshot_context: env -> string -> ((int & int & solver_depth_t & int) & env)
val rollback_context: solver_t -> string -> option (int & int & solver_depth_t & int) -> env

val compress_and_norm: env -> typ -> option typ
val tc_decls: env -> list sigelt -> list sigelt & env
val tc_partial_modul: env -> modul -> modul & env
val tc_more_partial_modul: env -> modul -> list sigelt -> modul & list sigelt & env
