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

module Pulse.Soundness.Frame
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing
open Pulse.Elaborate
open Pulse.Soundness.Common

val elab_frame_typing (g:stt_env)
                      (e:R.term)
                      (c:ln_comp)
                      (frame:term)
                      (frame_typing: tot_typing g frame tm_slprop)
                      (e_typing: RT.tot_typing (elab_env g) e (elab_comp c))
  : GTot (RT.tot_typing (elab_env g)
                        (elab_frame c frame e)
                        (elab_comp (add_frame c frame)))
