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

module Pulse.Soundness.Comp

open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Elaborate.Core
open Pulse.Soundness.Common

module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing

val stc_soundness
  (#g:stt_env)
  (#st:st_comp)
  (d_st:st_comp_typing g st)
  
  : GTot (RT.tot_typing (elab_env g)
                        st.res
                        (RT.tm_type st.u) &
          RT.tot_typing (elab_env g)
                        st.pre
                        slprop_tm &
          RT.tot_typing (elab_env g)
                        (mk_abs st.res R.Q_Explicit st.post)
                        (post1_type_bind st.res))

val comp_typing_soundness (g:stt_env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing g c uc)
  : GTot (RT.tot_typing (elab_env g) (elab_comp c) (RT.tm_type uc))
