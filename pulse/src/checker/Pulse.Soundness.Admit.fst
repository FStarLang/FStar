(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Soundness.Admit

module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Pure
open Pulse.Elaborate.Core
open Pulse.Elaborate
open Pulse.Soundness.Common

module WT = Pulse.Lib.Core.Typing
module Comp = Pulse.Soundness.Comp

let admit_soundess
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_Admit? d})
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c)) =

  let T_Admit _ c c_typing = d in
  let st_typing, _ = Pulse.Typing.Metatheory.Base.comp_typing_inversion c_typing in

  let rt_typing, rpre_typing, rpost_typing = Comp.stc_soundness st_typing in
  match c with
  | C_ST _ ->
    WT.stt_admit_typing rt_typing rpre_typing rpost_typing
  | C_STAtomic _ _ _ -> admit ()
  | C_STGhost _ _ -> admit ()

