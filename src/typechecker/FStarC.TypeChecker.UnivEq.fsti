(*
   Copyright Microsoft Research

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
(* Solving equations between universes, by instantiating universe
   unification variables. This is the universe fragment of the unifier
   ([Rel]), which uses it in its own worklist; Core uses it directly, to
   equate the universes of [Type u] and [f u#us]. *)
module FStarC.TypeChecker.UnivEq

open FStarC
open FStarC.Effect
open FStarC.Syntax.Syntax
module Env = FStarC.TypeChecker.Env

(* A lazily computed error message, computed in the unionfind state in
   which it is created. *)
val mklstr (f : unit -> ML string) : ML (Thunk.t string)

type univ_eq_sol 'w =
  | UDeferred of 'w
  | USolved   of 'w
  | UFailed   of Thunk.t string

(* Replace the solved unification variables of [u] by their solutions,
   and normalize it. *)
val norm_univ (env:Env.env) (u:universe) : ML universe

(* Record the solution [u] of [v] in the unionfind graph. *)
val commit_univ (v:universe_uvar) (u:universe) : ML unit

(* [solve_universe_eq env umax_heuristic_ok defer_ok solve w u1 u2] solves
   [u1 = u2], calling [solve] to instantiate each unification variable, which
   threads the state [w]. Equations involving [max] are deferred if
   [defer_ok]; otherwise, if [umax_heuristic_ok], they are solved
   structurally, after dropping the components common to both sides. *)
val solve_universe_eq
  (#w:Type)
  (env:Env.env)
  (umax_heuristic_ok:bool)
  (defer_ok:bool)
  (solve:w -> universe_uvar -> universe -> ML w)
  (st:w)
  (u1 u2:universe)
  : ML (univ_eq_sol w)

(* Whether the universes [us1] and [us2] are pairwise equal, instantiating
   their unification variables as needed. As in [Rel], the equations not
   involving [max] are solved first. On failure, no variable is
   instantiated. *)
val teq_univs (env:Env.env) (us1 us2:universes) : ML bool
