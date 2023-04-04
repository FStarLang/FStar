module Pulse.Soundness.Admit

module R = FStar.Reflection
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Steel.Wrapper.Typing
module Comp = Pulse.Soundness.Comp

let admit_soundess
  (#f:stt_env)
  (#g:env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing f g t c{T_Admit? d})
  : GTot (RT.typing (extend_env_l f g)
                    (elab_st_typing d)
                    (elab_comp c)) =

  let T_Admit _ s c st_typing = d in

  let rt_typing, rpre_typing, rpost_typing = Comp.stc_soundness st_typing in
  match c with
  | STT ->
    WT.stt_admit_typing rt_typing rpre_typing rpost_typing
  | STT_Atomic ->
    WT.stt_atomic_admit_typing rt_typing rpre_typing rpost_typing
  | STT_Ghost ->
    WT.stt_ghost_admit_typing rt_typing rpre_typing rpost_typing
