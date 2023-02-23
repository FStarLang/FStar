module Pulse.Soundness.STEquiv
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

val st_equiv_soundness (f:stt_env)
                       (g:env)
                       (c0 c1:ln_comp) 
                       (d:st_equiv f g c0 c1)
                       (r:R.term)
                       (d_r:RT.typing (extend_env_l f g) r (elab_comp c0)) 
  : GTot (RT.typing (extend_env_l f g) (elab_sub c0 c1 r) (elab_comp c1))
