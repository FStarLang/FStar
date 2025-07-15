(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.Prover.RewritesTo
open Pulse.Syntax
open Pulse.Typing.Env
module PS = Pulse.Checker.Prover.Substs

val mk_sq_rewrites_to_p (u:universe) (t x y:term) : term 

val extract_rewrites_to_p (t: typ) : option (var & term)

val get_subst_from_env (g: env) : PS.ss_t

val get_new_substs_from_env (g: env) (g': env { env_extends g' g }) (ss: PS.ss_t) : PS.ss_t