module Pulse.Soundness.Par

open FStar.Reflection
open Pulse.Reflection.Util

module RT = Refl.Typing

let par_post (u:universe) (aL aR:term) (postL postR:term) (x:var) : term =
  let x_tm = RT.var_as_term x in
  let postL = pack_ln (Tv_App postL (mk_fst u u aL aR x_tm, Q_Explicit)) in
  let postR = pack_ln (Tv_App postR (mk_snd u u aL aR x_tm, Q_Explicit)) in
  let post = mk_star postL postR in
  RT.open_or_close_term' post (RT.CloseVar x) 0

val par_soundness
  (#g:env)
  (#u:universe)
  (#aL #aR:term)
  (#preL #postL:term)
  (#preR #postR:term)
  (#eL #eR:term)
  (x:var{None? (RT.lookup_bvar g x)})
  (aL_typing:RT.typing g aL (pack_ln (Tv_Type u)))
  (aR_typing:RT.typing g aR (pack_ln (Tv_Type u)))
  (preL_typing:RT.typing g preL vprop_tm)
  (postL_typing:RT.typing g postL (mk_arrow (aL, Q_Explicit) vprop_tm))
  (preR_typing:RT.typing g preR vprop_tm)
  (postR_typing:RT.typing g postR (mk_arrow (aR, Q_Explicit) vprop_tm))
  (eL_typing:RT.typing g eL (mk_stt_comp u aL preL postL))
  (eR_typing:RT.typing g eR (mk_stt_comp u aR preR postR))

  : GTot (RT.typing g
                    (mk_par u aL aR preL postL preR postR eL eR)
                    (mk_stt_comp u (mk_tuple2 u u aL aR)
                       (mk_star preL preR)
                       (mk_abs (mk_tuple2 u u aL aR) Q_Explicit (par_post u aL aR postL postR x))))
