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

module Pulse.Soundness.Lift
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

(*** Soundness of lift elaboration *)

val elab_lift_stt_atomic_st_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
  : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_STAtomic_ST? lc)
          (ensures fun _ -> True)

val elab_lift_ghost_neutral_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
      (reveal_a:R.term)
      (reveal_a_typing:RT.tot_typing (elab_env g) reveal_a
                                     (non_informative_rt (comp_u c1)
                                                         (comp_res c1)))
    : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_Ghost_Neutral? lc)
          (ensures fun _ -> True)

val elab_lift_neutral_ghost_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
    : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_Neutral_Ghost? lc)
          (ensures fun _ -> True)


val elab_lift_observability_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
    : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_Observability? lc)
          (ensures fun _ -> True)
