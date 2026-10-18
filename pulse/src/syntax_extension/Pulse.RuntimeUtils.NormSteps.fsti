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

module Pulse.RuntimeUtils.NormSteps
open FStarC.Effect

(* [FStarC.TypeChecker.Cfg.translate_norm_steps], at ulib's type of steps,
   which is the compiler's at runtime.  Naming the compiler's [norm_step] in
   this unit makes Custard emit an ill-formed second copy of it (the type is
   provided both by the compiler unit and, via ulib's FStar.NormSteps, by the
   checker unit), so the call goes through an extern instead. *)
val translate_norm_steps
  : list FStar.NormSteps.norm_step -> ML (list FStarC.TypeChecker.Env.step)
