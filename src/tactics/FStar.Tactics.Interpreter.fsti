(*
   Copyright 2008-2016 Microsoft Research

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
module FStar.Tactics.Interpreter

open FStar.Compiler.Effect
open FStar.Compiler.Range
open FStar.Syntax.Syntax
open FStar.Syntax.Embeddings
open FStar.Tactics.Types
module Env = FStar.TypeChecker.Env

val run_tactic_on_ps :
    range -> (* position on the tactic call *)
    range -> (* position for the goal *)
    bool -> (* whether this call is in the "background", like resolve_implicits *)
    embedding 'a ->
    'a ->
    embedding 'b ->
    term ->        (* a term representing an `'a -> tac 'b` *)
    proofstate ->  (* proofstate *)
    list goal * 'b (* goals and return value *)

val primitive_steps : unit -> list FStar.TypeChecker.Cfg.primitive_step

val report_implicits : range -> Env.implicits -> unit

(* For debugging only *)
val tacdbg : ref bool
