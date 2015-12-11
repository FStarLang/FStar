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
open FStar.TypeChecker.Env
open FStar.Syntax.Syntax

type step =
  | WHNF         (* reduce to weak head normal form only -- CH: adding this removes behaviors, quite unintuitive; NS: Not sure what this comment means. *)
                 (* without WHNF, all the strategies reduce under lambdas *)
  | Eta          (* eta expansion (of type functions) *)
  | EtaArgs      (* eta expand arguments of functions also *)
  | Delta        (* expand type abbreviations only if reduction is blocked *)
  | DeltaHard    (* expand all type abbreviations *)
  | Beta         (* beta reduction -- CH: currently adding this changes nothing, seems that Beta always performed *)
  | DeltaComp    (* expand computation-type abbreviations *)
  | Simplify     (* simplify formulas while reducing -- experimental -- CH: actually unused *)
  | SNComp       (* normalize computation types also *)
  | Unmeta       (* remove Metas other than Meta_named -- CH: at the moment Meta_named causes failwith; why? *)
  | Unlabel      (* remove only Meta_labeled *)

and steps = list<step>

val eta_expand:           env -> term -> term
val weak_norm_comp:       env -> comp -> comp_typ
val normalize:            steps -> env -> term -> term
val normalize_comp:       steps -> env -> comp -> comp
val normalize_sigelt:     steps -> env -> sigelt -> sigelt
val normalize_refinement: steps -> env -> typ -> typ
val whnf:                 env -> term -> term

val term_to_string:  env -> term -> string
val comp_to_string:  env -> comp -> string

val debug: unit -> unit