module Pulse.Soundness.Par

open FStar.Reflection
open Refl.Typing
open Pulse.Elaborate.Pure
open Pulse.Soundness.Common
open Pulse.Elaborate.Core

module PT = Pulse.Typing

module RT = Refl.Typing

let par_soundness
  (#f:stt_env)
  (#g:PT.env)
  (#u:universe)
  (#aL #aR:term)
  (#preL #postL:term)
  (#preR #postR:term)
  (#eL #eR:term)
  (aL_typing:RT.typing (PT.extend_env_l f g) aL (pack_ln (Tv_Type u)))
  (aR_typing:RT.typing (PT.extend_env_l f g) aR (pack_ln (Tv_Type u)))
  (preL_typing:RT.typing (PT.extend_env_l f g) preL vprop_tm)
  (postL_typing:RT.typing (PT.extend_env_l f g) postL (mk_arrow (aL, Q_Explicit) vprop_tm))
  (preR_typing:RT.typing (PT.extend_env_l f g) preR vprop_tm)
  (postR_typing:RT.typing (PT.extend_env_l f g) postR (mk_arrow (aR, Q_Explicit) vprop_tm))
  (eL_typing:RT.typing (PT.extend_env_l f g) eL (mk_stt_comp u aL preL postL))
  (eR_typing:RT.typing (PT.extend_env_l f g) eR (mk_stt_comp u aR preR postR))

  = admit ()
