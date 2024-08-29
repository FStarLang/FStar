(*
   Copyright 2024 Microsoft Research

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
module FStar.SMTEncoding.SolverState
open FStar.Compiler.Effect
open FStar
open FStar.Compiler
open FStar.SMTEncoding.Term
open FStar.BaseTypes
open FStar.Compiler.Util
module BU = FStar.Compiler.Util
module U = FStar.SMTEncoding.UnsatCore
type using_facts_from_setting = list (list string & bool)

val solver_state : Type0

val init (_:unit) : solver_state
val push (s:solver_state) : solver_state
val pop (s:solver_state) : solver_state
val depth (s:solver_state) : int
val reset (_:option using_facts_from_setting) (s:solver_state) : solver_state
val give (ds:list decl) (s:solver_state) : solver_state
val start_query (msg:string) (roots:list decl) (qry:decl) (s:solver_state) : solver_state
val finish_query (msg:string) (s:solver_state) : solver_state
val filter_with_unsat_core (queryid:string) (_:U.unsat_core) (s:solver_state) : list decl
val flush (s:solver_state) : list decl & solver_state
val would_have_pruned (s:solver_state) : option (list string)