module Pulse.Soundness.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common


// Wrapper.bind_stt and Wrapper.bind_sttg
val elab_bind_typing (f:stt_env)
                     (g:env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.typing (extend_env_l f g) r1 (elab_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.typing (extend_env_l f g) r2 
                                           (elab_term (Tm_Arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
                     (bc:bind_comp f g x c1 c2 c)
                     (t2_typing : RT.typing (extend_env_l f g) (elab_term (comp_res c2)) (RT.tm_type (elab_universe (comp_u c2))))
                     (post2_typing: RT.typing (extend_env_l f g) 
                                              (elab_comp_post c2)
                                              (post2_type_bind (elab_term (comp_res c2))))
  : Ghost (RT.typing (extend_env_l f g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp? bc)
          (ensures fun _ -> True)

// Wrapper.bind_stt_ghost_atomic
val elab_bind_ghost_l_typing
  (f:stt_env)
  (g:env)
  (c1 c2 c:ln_comp)
  (x:var{~ (x `Set.mem` freevars_comp c1)})
  (r1:R.term)
  (r1_typing:RT.typing (extend_env_l f g) r1 (elab_comp c1))
  (r2:R.term)
  (r2_typing:RT.typing (extend_env_l f g) r2
                       (elab_term (Tm_Arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
  (bc:bind_comp f g x c1 c2 c)
  (t2_typing:RT.typing (extend_env_l f g) (elab_term (comp_res c2))
                       (RT.tm_type (elab_universe (comp_u c2))))
  (post2_typing:RT.typing (extend_env_l f g) (elab_comp_post c2)
                          (post2_type_bind (elab_term (comp_res c2))))
  (reveal_a:R.term)
  (reveal_a_typing:RT.typing (extend_env_l f g) reveal_a
                             (non_informative_witness_rt (elab_universe (comp_u c1))
                                                         (elab_term (comp_res c1))))
  : Ghost (RT.typing (extend_env_l f g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp_ghost_l? bc)
          (ensures fun _ -> True)

// Wrapper.bind_stt_atomic_ghost
val elab_bind_ghost_r_typing
  (f:stt_env)
  (g:env)
  (c1 c2 c:ln_comp)
  (x:var{~ (x `Set.mem` freevars_comp c1)})
  (r1:R.term)
  (r1_typing:RT.typing (extend_env_l f g) r1 (elab_comp c1))
  (r2:R.term)
  (r2_typing:RT.typing (extend_env_l f g) r2
                       (elab_term (Tm_Arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
  (bc:bind_comp f g x c1 c2 c)
  (t2_typing:RT.typing (extend_env_l f g) (elab_term (comp_res c2))
                       (RT.tm_type (elab_universe (comp_u c2))))
  (post2_typing:RT.typing (extend_env_l f g) (elab_comp_post c2)
                          (post2_type_bind (elab_term (comp_res c2))))
  (reveal_b:R.term)
  (reveal_b_typing:RT.typing (extend_env_l f g) reveal_b
                             (non_informative_witness_rt (elab_universe (comp_u c2))
                                                         (elab_term (comp_res c2))))
  : Ghost (RT.typing (extend_env_l f g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp_ghost_r? bc)
          (ensures fun _ -> True)
