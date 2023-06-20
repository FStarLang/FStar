module Pulse.Soundness.Lift
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

(*** Soundness of lift elaboration *)

val elab_lift_stt_atomic_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
  : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_STAtomic_ST? lc)
          (ensures fun _ -> True)

val elab_lift_stt_ghost_typing
      (g:stt_env)
      (c1 c2:ln_comp)
      (e:R.term)
      (e_typing:RT.tot_typing (elab_env g) e (elab_comp c1))
      (lc:lift_comp g c1 c2)
      (reveal_a:R.term)
      (reveal_a_typing:RT.tot_typing (elab_env g) reveal_a
                                     (non_informative_witness_rt (comp_u c1)
                                                                 (elab_term (comp_res c1))))
    : Ghost (RT.tot_typing (elab_env g) (elab_lift lc e) (elab_comp c2))
          (requires Lift_STGhost_STAtomic? lc)
          (ensures fun _ -> True)
