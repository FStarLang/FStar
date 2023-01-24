module Pulse.Soundness.Lift
module RT = Refl.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

let elab_lift_stt_atomic_typing (f:stt_env) (g:env)
  (c1 c2:ln_comp)
  (e:R.term)
  (e_typing:RT.typing (extend_env_l f g) e (elab_pure_comp c1))
  (lc:lift_comp f g c1 c2) = admit ()

let elab_lift_stt_ghost_typing (f:stt_env) (g:env)
  (c1 c2:ln_comp)
  (e:R.term)
  (e_typing:RT.typing (extend_env_l f g) e (elab_pure_comp c1))
  (lc:lift_comp f g c1 c2)
  (reveal_a:R.term)
  (reveal_a_typing:RT.typing (extend_env_l f g) reveal_a
                             (non_informative_witness_rt (elab_universe (comp_u c1))
                                                         (elab_pure (comp_res c1)))) = admit ()
