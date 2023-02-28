module Pulse.Soundness.Return
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

// val elab_return_typing (#f:stt_env)
//                        (#g:env)
//                        (#u:universe)
//                        (#ty:term)
//                        (#v:term)
//                        (ty_typing: universe_of f g ty u)
//                        (v_typing: tot_typing f g v ty)
//   : GTot (RT.typing (extend_env_l f g)
//                     (mk_return (elab_universe u) (elab_term ty) (elab_term v))
//                     (elab_comp (return_comp u ty v)))


// val elab_return_noeq_typing (#f:stt_env)
//                             (#g:env)
//                             (#u:universe)
//                             (#ty:term)
//                             (#r:R.term)
//                             (ty_typing: universe_of f g ty u)
//                             (r_typing: RT.typing (extend_env_l f g) r (elab_term ty))
//   : GTot (RT.typing (extend_env_l f g)
//                     (mk_return_noeq (elab_universe u) (elab_term ty) r)
//                     (elab_comp (return_comp_noeq u ty)))
