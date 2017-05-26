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
// (c) Microsoft Corporation. All rights reserved

module FStar.TypeChecker.Normalize
open FStar.All

open FStar.TypeChecker
open FStar.Syntax.Syntax

type step =
  | Beta
  | Iota            //pattern matching
  | Zeta            //fixed points
  | Exclude of step //the first three kinds are included by default, unless Excluded explicity
  | WHNF            //Only produce a weak head normal form
  | Primops         //reduce primitive operators like +, -, *, /, etc.
  | Eager_unfolding
  | Inlining
  | NoDeltaSteps
  | UnfoldUntil of delta_depth
  | PureSubtermsWithinComputations
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  | Reify
  | CompressUvars
  | NoFullNorm
and steps = list<step>
type primitive_step = {
    name:FStar.Ident.lid;
    arity:int;
    strong_reduction_ok:bool;
    interpretation:(FStar.Range.range -> args -> option<term>)
}
val eta_expand_with_type :Env.env -> term -> typ -> term
val eta_expand:           Env.env -> term -> term
val normalize:            steps -> Env.env -> term -> term
val normalize_universe:   Env.env -> universe -> universe
val normalize_comp:       steps -> Env.env -> comp -> comp
val normalize_refinement: steps -> Env.env -> typ -> typ
val unfold_whnf:          Env.env -> term -> term
val reduce_uvar_solutions:Env.env -> term -> term
val ghost_to_pure:        Env.env -> comp -> comp
val ghost_to_pure_lcomp:  Env.env -> lcomp -> lcomp
val normalize_with_primitive_steps : list<primitive_step> -> list<step> -> Env.env -> term -> term
val term_to_string:  Env.env -> term -> string
val comp_to_string:  Env.env -> comp -> string
