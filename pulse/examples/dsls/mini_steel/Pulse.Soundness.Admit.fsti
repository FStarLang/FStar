module Pulse.Soundness.Admit

open FStar.Reflection
open Pulse.Reflection.Util

module RT = Refl.Typing


(*

 g |- a : Type u
 g |- p : vprop
 g |- q : a -> vprop
 ------------------------------------------
 g |- stt_admit a p q : stt a p q

*)

val stt_admit_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_admit u a p q)
                    (mk_stt_comp u a p q))
               
val stt_atomic_admit_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_atomic_admit u a p q)
                    (mk_stt_atomic_comp u a emp_inames_tm p q))

val stt_ghost_admit_soundness
  (#g:env)
  (#u:universe)
  (#a:term)
  (#p:term)
  (#q:term)
  (a_typing:RT.typing g a (pack_ln (Tv_Type u)))
  (p_typing:RT.typing g p vprop_tm)
  (q_typing:RT.typing g q (mk_arrow (a, Q_Explicit) vprop_tm))

  : GTot (RT.typing g
                    (mk_stt_ghost_admit u a p q)
                    (mk_stt_ghost_comp u a emp_inames_tm p q))
