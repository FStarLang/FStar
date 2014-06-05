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
  | Alpha
  | Delta
  | Beta
  | DeltaComp
  | Simplify
and steps = list<step>

val normalize: Env.env -> typ -> typ
val normalize_comp: Env.env -> comp -> comp_typ
val norm_comp: steps -> Env.env -> comp -> comp_typ
val weak_norm_comp: Env.env -> comp -> comp_typ
val norm_kind: steps -> Env.env -> knd -> knd
val norm_typ:  steps -> Env.env -> typ -> typ
