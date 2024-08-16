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

module FStar.SMTEncoding.Solver
open FStar.Compiler.Effect

val with_hints_db : string -> (unit -> 'a) -> 'a
val set_current_decl (_:list Ident.lident) : unit
val report_context_current_decl (_:unit) : unit
val report_context_global 
    (modul:Ident.lident)
    (all_modules:list Ident.lident)
    (opens:list Ident.lident)
: unit
val clear_profile_context (_:unit) : unit
val dummy: FStar.TypeChecker.Env.solver_t
val solver: FStar.TypeChecker.Env.solver_t
