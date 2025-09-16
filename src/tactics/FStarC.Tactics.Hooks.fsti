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

module FStarC.Tactics.Hooks

open FStarC
open FStarC.Syntax.Syntax
open FStarC.Range

module O   = FStarC.Options
module Env = FStarC.TypeChecker.Env

val preprocess      : Env.env -> term -> bool & list (Env.env & term & O.optionstate)
val spinoff_strictly_positive_goals      : Env.env -> term -> list (Env.env & term)
val handle_smt_goal : Env.env -> Env.goal -> list (Env.env & term)
val synthesize      : Env.env -> typ -> term -> range -> term
val solve_implicits : Env.env -> term -> Env.implicits -> unit
val splice          : Env.splice_t
val mpreprocess     : Env.env -> term -> term -> term
val postprocess     : Env.env -> term -> typ -> term -> term
