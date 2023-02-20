module Pulse.Soundness.Exists

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure

val elim_exists_soundness
  (#g:fstar_top_env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (a_typing:typing g a (pack_ln (Tv_Type u)))
  (p_typing:typing g (mk_abs a Q_Explicit p)
                     (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (typing g (mk_elim_exists u a p) (mk_stt_ghost_comp u a emp_inames_tm
                                             (mk_exists u a p)
                                             (mk_abs a Q_Explicit p)))
