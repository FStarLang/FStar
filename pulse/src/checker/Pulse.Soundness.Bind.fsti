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

module Pulse.Soundness.Bind
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


// Wrapper.bind_stt and Wrapper.bind_sttg
val elab_bind_typing (g:stt_env)
                     (c1 c2 c:ln_comp)
                     (x:var { ~ (x `Set.mem` freevars_comp c1) })
                     (r1:R.term)
                     (r1_typing: RT.tot_typing (elab_env g) r1 (elab_comp c1))
                     (r2:R.term)
                     (r2_typing: RT.tot_typing (elab_env g) r2 
                                               (elab_term (tm_arrow (null_binder (comp_res c1)) None (close_comp c2 x))))
                     (bc:bind_comp g x c1 c2 c)
                     (t2_typing : RT.tot_typing (elab_env g) (elab_term (comp_res c2)) (RT.tm_type (comp_u c2)))
                     (post2_typing: RT.tot_typing (elab_env g) 
                                                  (elab_comp_post c2)
                                                  (post2_type_bind (elab_term (comp_res c2))))
  : Ghost (RT.tot_typing (elab_env g) (elab_bind bc r1 r2) (elab_comp c))
          (requires Bind_comp? bc)
          (ensures fun _ -> True)

val tot_bind_typing
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_TotBind? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))

val ghost_bind_typing
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c { T_GhostBind? d })
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))

val bind_fn_typing
  (#g:stt_env)
  (#t:st_term)
  (#c:comp)
  (d:st_typing g t c{T_BindFn? d})
  (soundness:soundness_t d)
  : GTot (RT.tot_typing (elab_env g)
                        (elab_st_typing d)
                        (elab_comp c))
