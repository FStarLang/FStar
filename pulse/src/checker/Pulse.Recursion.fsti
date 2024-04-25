(*
   Copyright 2023 Microsoft Research

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

module Pulse.Recursion

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

open FStar.Tactics.V2
open Pulse.Syntax
open Pulse.Typing

val add_knot (g : env)  (rng : R.range)
             (d : decl)
: Tac decl

val tie_knot (g : env)  (rng : R.range)
             (nm_orig : string) (nm_aux : string)
             (d : decl) (r_typ : R.term) (blob:RT.blob)
: Tac (list (RT.sigelt_for (fstar_env g) None))
