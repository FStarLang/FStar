module Pulse.Soundness
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val soundness_lemma
  (g:stt_env)
  (t:st_term)
  (c:comp)
  (d:st_typing g t c)
  : Lemma (ensures RT.tot_typing (elab_env g)
                                 (elab_st_typing d)
                                 (elab_comp c))
