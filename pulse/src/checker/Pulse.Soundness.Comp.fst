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
open Pulse.Elaborate
open Pulse.Soundness.Common

module STT = Pulse.Soundness.STT

let stc_soundness
  (#g:stt_env)
  (#st:st_comp)
  (d_st:st_comp_typing g st)
  
  : GTot (RT.tot_typing (elab_env g)
                        st.res
                        (RT.tm_type st.u) &
          RT.tot_typing (elab_env g)
                        st.pre
                        vprop_tm &
          RT.tot_typing (elab_env g)
                        (mk_abs st.res R.Q_Explicit st.post)
                        (post1_type_bind st.res)) =
   
  let STC _ st x dres dpre dpost = d_st in
  let res_typing = tot_typing_soundness dres in
  let pre_typing = tot_typing_soundness dpre in      
  calc (==) {
    RT.close_term (open_term st.post x) x;
       (==) { RT.open_term_spec st.post x }
    RT.close_term (RT.open_term st.post x) x;
       (==) { 
              RT.close_open_inverse st.post x
            }
    st.post;
  };
  let post_typing  = mk_t_abs_tot g ppname_default dres dpost in
  res_typing, pre_typing, post_typing

#push-options "--fuel 2 --ifuel 2 --z3rlimit_factor 2"
let comp_typing_soundness (g:stt_env)
                          (c:comp)
                          (uc:universe)
                          (d:comp_typing g c uc)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_comp c)
                        (RT.tm_type uc))
         (decreases d)
  = match d with
    | CT_Tot _ t _ dt ->
      tot_typing_soundness dt
      
    | CT_ST _ st d_st -> 
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_typing res_typing pre_typing post_typing

    | CT_STAtomic _ i obs st d_i d_st -> 
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_atomic_typing #(elab_observability obs) res_typing i_typing pre_typing post_typing

    | CT_STGhost _ i st d_i d_st ->
      let i_typing = tot_typing_soundness d_i in
      let res_typing, pre_typing, post_typing = stc_soundness d_st in
      STT.stt_ghost_typing res_typing i_typing pre_typing post_typing
#pop-options
