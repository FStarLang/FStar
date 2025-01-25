(*
   Copyright 2008-2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: A. Rastogi, N. Swamy
*)

module FStarC.TypeChecker.Positivity
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax.Syntax
open FStarC.Ident

val check_strict_positivity: env -> list lident -> sigelt -> bool
val name_strictly_positive_in_type: env -> bv -> term -> bool
val name_unused_in_type: env -> bv -> term -> bool
val check_exn_strict_positivity: env -> lident -> bool
val mark_uniform_type_parameters: env -> sigelt -> sigelt