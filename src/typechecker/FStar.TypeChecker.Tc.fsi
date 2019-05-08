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
module FStar.TypeChecker.Tc
open FStar.ST
open FStar.All
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.TypeChecker.Common


val check_module: env -> modul -> bool -> modul * env
val load_checked_module: env -> modul -> env

val pop_context: env -> string -> env
val push_context: env -> string -> env
val snapshot_context: env -> string -> ((int * int * solver_depth_t * int) * env)
val rollback_context: solver_t -> string -> option<(int * int * solver_depth_t * int)> -> env

val tc_decls: env -> list<sigelt> -> list<sigelt> * list<sigelt> * env
val tc_partial_modul: env -> modul -> modul * list<sigelt> * env
val tc_more_partial_modul: env -> modul -> list<sigelt> -> modul * list<sigelt> * env
val extract_interface: env -> modul -> modul
