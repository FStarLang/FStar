module Pulse.Soundness.STEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val st_equiv_soundness (g:stt_env)
                       (c0 c1:ln_comp) 
                       (d:st_equiv g c0 c1)
                       (r:R.term)
                       (d_r:RT.tot_typing (elab_env g) r (elab_comp c0)) 
  : GTot (RT.tot_typing (elab_env g) (elab_sub c0 c1 r) (elab_comp c1))
