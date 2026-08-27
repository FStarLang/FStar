(*
   Copyright 2026 Microsoft Research

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

module Pulse.Eta

(* Eta-expansion of product-typed unification variables.

   A hole standing for a pair is solved by neither of the two mechanisms Pulse
   has available: F*'s uni-valued rule (try_solve_single_valued_implicits) only
   handles [unit], and Pulse's [pure_eq_unif] only fires when one side of a
   [pure (a == b)] goal is a *bare* uvar. So a goal like

     pure (fst ?u == 4) ** pure (snd ?u == 7)     with ?u : int & int

   is stuck: [fst ?u] is not a bare uvar, and [?u] is not uni-valued.

   The missing step is purely structural. Every inhabitant of [t1 & t2] is a
   pair, so refining [?u := (?a, ?b)] commits to no value; any component that
   stays unsolved still raises an error. Once expanded, [Pulse.Simplify] reduces
   [fst (?a, ?b)] to [?a], and the existing machinery takes over.

   This must NOT be applied eagerly. A goal [pts_to r ?u] with [?u : int & int]
   is today solved against a context [pts_to r v] by taking [?u := v]; had [?u]
   already been expanded to [(?a, ?b)] the slprop matcher, which is syntactic,
   would fail to match it against the variable [v]. So expansion fires only
   where the checker is otherwise stuck -- see the two callers. *)

open Pulse.Syntax.Base
open Pulse.Typing.Env
module T = FStar.Tactics.V2

(* All three return the fresh holes introduced -- the leaves of the expansion --
   which is empty exactly when nothing was expanded. Handing those leaves to
   [RU.try_solve_single_valued_implicits] is what solves the ones at [unit]. *)

(* If the head of [t] is an unsolved uvar whose type is a [tuple2], solve it
   with a pair of fresh implicits, recursively. *)
val eta_expand_uvar (g:env) (t:term) : T.Tac (list term)

(* Eta-expand every uvar that appears under a tuple projector in [t]. Being
   under a projector is exactly the evidence that the pair structure is needed,
   and such a goal is unsolvable without it. *)
val eta_expand_projected_uvars (g:env) (t:term) : T.Tac (list term)

(* Eta-expand every product-typed uvar in [t], whether projected or not. Used
   only as a last resort, when the alternative is an error. *)
val eta_expand_term_uvars (g:env) (t:term) : T.Tac (list term)
