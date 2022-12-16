module Pulse.Soundness.Bind
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

val elab_bind_typing (f:stt_env)
                     (g:env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.typing (extend_env_l f g) r1 (elab_pure_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.typing (extend_env_l f g) r2 
                                           (elab_pure (Tm_Arrow (comp_res c1) (close_pure_comp c2 x))))
                     (bc:bind_comp f g x c1 c2 c)
                     (t2_typing : RT.typing (extend_env_l f g) (elab_pure (comp_res c2)) (RT.tm_type (elab_universe (comp_u c2))))
                     (post2_typing: RT.typing (extend_env_l f g) 
                                              (elab_comp_post c2)
                                              (post2_type_bind (elab_pure (comp_res c2))))
  : GTot (RT.typing (extend_env_l f g) (elab_bind c1 c2 r1 r2) (elab_pure_comp c))
