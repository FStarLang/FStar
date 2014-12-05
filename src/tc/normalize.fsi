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

module Microsoft.FStar.Tc.Normalize

open Microsoft.FStar.Tc
open Microsoft.FStar.Absyn.Syntax

type step =
  | WHNF         (* reduce to weak head normal form only -- CH: adding this removes behaviors, quite unintuitive *)
                 (* without WHNF, all the strategies reduce under lambdas *)
  | Eta          (* eta expansion (of type functions) *)
  | Delta        (* expand type abbreviations only if reduction is blocked *)
  | DeltaHard    (* expand all type abbreviations *)
  | Beta         (* beta reduction -- CH: currently adding this changes nothing, seems that Beta always performed *)
  | DeltaComp    (* expand computation-type abbreviations *)
  | Simplify     (* simplify formulas while reducing -- experimental -- CH: actually unused *)
  | SNComp       (* normalize computation types also *)
  | Unmeta       (* remove Metas other than Meta_named -- CH: at the moment Meta_named causes failwith; why? *)
and steps = list<step>

val eta_expand: Env.env -> typ -> typ
val eta_expand_exp: Env.env -> exp -> exp
val normalize: Env.env -> typ -> typ
val normalize_comp: Env.env -> comp -> comp
val normalize_kind: Env.env -> knd -> knd
val norm_comp: steps -> Env.env -> comp -> comp
val weak_norm_comp: Env.env -> comp -> comp_typ
val norm_kind: steps -> Env.env -> knd -> knd
val norm_typ:  steps -> Env.env -> typ -> typ
val norm_exp:  steps -> Env.env -> exp -> exp
val whnf: Env.env -> typ -> typ
val exp_norm_to_string: Env.env -> exp -> string
val typ_norm_to_string : Env.env -> typ -> string
val kind_norm_to_string : Env.env -> knd -> string
val formula_norm_to_string : Env.env -> typ -> string
val comp_typ_norm_to_string : Env.env -> comp -> string
