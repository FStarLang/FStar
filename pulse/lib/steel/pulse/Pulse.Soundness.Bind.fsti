module Pulse.Soundness.Bind
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


// Wrapper.bind_stt and Wrapper.bind_sttg
val elab_bind_typing (g:stt_env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.tot_typing (elab_env g) r1 (elab_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.tot_typing (elab_env g) r2 
                                               (elab_term (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
                     (bc:bind_comp g x c1 c2 c)
                     (t2_typing : RT.tot_typing (elab_env g) (elab_term (comp_res c2)) (RT.tm_type (comp_u c2)))
                     (post2_typing: RT.tot_typing (elab_env g) 
                                                  (elab_comp_post c2)
                                                  (post2_type_bind (elab_term (comp_res c2))))
  : Ghost (RT.tot_typing (elab_env g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp? bc)
          (ensures fun _ -> True)

// Wrapper.bind_stt_ghost_atomic
val elab_bind_ghost_l_typing
  (g:stt_env)
  (c1 c2 c:ln_comp)
  (x:var{~ (x `Set.mem` freevars_comp c1)})
  (r1:R.term)
  (r1_typing:RT.tot_typing (elab_env g) r1 (elab_comp c1))
  (r2:R.term)
  (r2_typing:RT.tot_typing (elab_env g) r2
                           (elab_term (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
  (bc:bind_comp g x c1 c2 c)
  (t2_typing:RT.tot_typing (elab_env g) (elab_term (comp_res c2))
                           (RT.tm_type (comp_u c2)))
  (post2_typing:RT.tot_typing (elab_env g) (elab_comp_post c2)
                              (post2_type_bind (elab_term (comp_res c2))))
  (reveal_a:R.term)
  (reveal_a_typing:RT.tot_typing (elab_env g) reveal_a
                                 (non_informative_witness_rt (comp_u c1)
                                                             (elab_term (comp_res c1))))
  : Ghost (RT.tot_typing (elab_env g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp_ghost_l? bc)
          (ensures fun _ -> True)

// Wrapper.bind_stt_atomic_ghost
val elab_bind_ghost_r_typing
  (g:stt_env)
  (c1 c2 c:ln_comp)
  (x:var{~ (x `Set.mem` freevars_comp c1)})
  (r1:R.term)
  (r1_typing:RT.tot_typing (elab_env g) r1 (elab_comp c1))
  (r2:R.term)
  (r2_typing:RT.tot_typing (elab_env g) r2
                           (elab_term (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
  (bc:bind_comp g x c1 c2 c)
  (t2_typing:RT.tot_typing (elab_env g) (elab_term (comp_res c2))
                           (RT.tm_type (comp_u c2)))
  (post2_typing:RT.tot_typing (elab_env g) (elab_comp_post c2)
                              (post2_type_bind (elab_term (comp_res c2))))
  (reveal_b:R.term)
  (reveal_b_typing:RT.tot_typing (elab_env g) reveal_b
                                 (non_informative_witness_rt (comp_u c2)
                                                             (elab_term (comp_res c2))))
  : Ghost (RT.tot_typing (elab_env g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp_ghost_r? bc)
          (ensures fun _ -> True)


val tot_bind_typing
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_TotBind? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))
