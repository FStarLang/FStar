module Pulse.Soundness.VPropEquiv
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val vprop_equiv_unit_soundness (#g:stt_env) (#v0 #v1:term) 
                               (d0:tot_typing g v0 Tm_VProp)
                               (eq:vprop_equiv g v0 v1)
  : GTot (RT.tot_typing (elab_env g) (`())
            (stt_vprop_equiv (elab_term v0) (elab_term v1)))
