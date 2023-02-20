module Pulse.Soundness.Exists

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Soundness.Common

val exists_inversion
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (e_typing:typing (extend_env_l f g)
                   (mk_exists u a p)
                   vprop_tm)

  : GTot (typing (extend_env_l f g) p
                 (mk_arrow (a, Q_Explicit) vprop_tm))

(*

 g |- a : Type u
 g |- p : a -> vprop
 ----------------------------------------------------------------
 g |- elim_exists<u> a p : stt_ghost<u> a emp (exists_<u> p) p

*)

val elim_exists_soundness
  (#f:stt_env)
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (a_typing:typing (extend_env_l f g) a (pack_ln (Tv_Type u)))
  (p_typing:typing (extend_env_l f g) p (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (typing (extend_env_l f g)
                 (mk_elim_exists u a p)
                 (mk_stt_ghost_comp u a emp_inames_tm
                    (mk_exists u a p) p))
