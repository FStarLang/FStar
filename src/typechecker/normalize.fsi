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

open FStar.TypeChecker
open FStar.Syntax.Syntax

type step =
  | WHNF            //Only produce a weak head normal form
  | Inline
  | UnfoldUntil of delta_depth
  | Beta            //remove Always do beta
  | BetaUVars       //only beta reduce applications of resolved uvars
  | Simplify        //Simplifies some basic logical tautologies: not part of definitional equality!
  | EraseUniverses
  | AllowUnboundUniverses //we erase universes as we encode to SMT; so, sometimes when printing, it's ok to have some unbound universe variables
  //remove the rest?
  | DeltaComp       
  | SNComp
  | Eta             
  | EtaArgs         
  | Unmeta
  | Unlabel
and steps = list<step>

val eta_expand:           Env.env -> term -> term
val unfold_effect_abbrev: Env.env -> comp -> comp_typ
val normalize:            steps -> Env.env -> term -> term
val normalize_universe:   Env.env -> universe -> universe
val normalize_comp:       steps -> Env.env -> comp -> comp
val normalize_sigelt:     steps -> Env.env -> sigelt -> sigelt
val normalize_refinement: steps -> Env.env -> typ -> typ
val ghost_to_pure:        Env.env -> comp -> comp

val term_to_string:  Env.env -> term -> string
val comp_to_string:  Env.env -> comp -> string
