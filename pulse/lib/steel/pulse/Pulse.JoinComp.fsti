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

module Pulse.JoinComp

open Pulse.Syntax
open Pulse.Typing

let inames_of_comp (c:comp_st) : term =
  match c with
  | C_ST _
  | C_STGhost _ -> tm_emp_inames
  | C_STAtomic inames _ _ -> inames

let obs_of_comp (c:comp_st) : observability =
  match c with
  | C_ST _ -> Observable
  | C_STGhost _ -> Neutral
  | C_STAtomic _ obs _ -> obs

val compute_iname_join (is1 is2 : term) : term
  
effect TacS (a:Type) (pre : Type0) (post : (_:a{pre}) -> Type0) =
  Tactics.TacH a (requires (fun _ -> pre))
                 (ensures (fun _ r -> pre /\ (
                                      match r with
                                      | Tactics.Result.Success r _ -> post r
                                      | _ -> True))) // does not guarantee anything on failure

val lift_atomic_to_st
  (g : env)
  (e : st_term)
  (c : comp_st{C_STAtomic? c})
  (d : st_typing g e c)
  : Pure (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT)

val lift_ghost_to_atomic
  (g : env)
  (e : st_term)
  (c : comp_st{C_STGhost? c})
  (d : st_typing g e c)
  : TacS (c':comp_st & st_typing g e c')
         (requires True)
         (ensures fun (| c', _ |) ->
             st_comp_of_comp c' == st_comp_of_comp c /\
             ctag_of_comp_st c' == STT_Atomic /\
             tm_emp_inames == C_STAtomic?.inames c')

(* This matches the effects of the two branches, without
necessarily matching inames. *)
val join_comp_effects
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires True) // comp_pre c_then == comp_pre c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_else')

(* Takes the two branches, with already matched effect,
and matches their invariants (unless C_ST) *)
val join_comp_inames
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c_then':comp_st &
          c_else':comp_st &
          st_typing g_then e_then c_then' &
          st_typing g_else e_else c_else')
         (requires ctag_of_comp_st c_then == ctag_of_comp_st c_else)
         (ensures fun (| c_then', c_else', _, _ |) ->
            st_comp_of_comp c_then' == st_comp_of_comp c_then /\
            st_comp_of_comp c_else' == st_comp_of_comp c_else /\
            ctag_of_comp_st c_then' == ctag_of_comp_st c_then /\
            ctag_of_comp_st c_else' == ctag_of_comp_st c_else /\
            inames_of_comp c_then' == inames_of_comp c_else' /\
            obs_of_comp c_then' == obs_of_comp c_else'
         )

val join_comps
  (g_then:env)
  (e_then:st_term)
  (c_then:comp_st)
  (e_then_typing:st_typing g_then e_then c_then)
  (g_else:env)
  (e_else:st_term)
  (c_else:comp_st)
  (e_else_typing:st_typing g_else e_else c_else)
  : TacS (c:comp_st &
          st_typing g_then e_then c &
          st_typing g_else e_else c)
         (requires comp_pre c_then == comp_pre c_else)
         (ensures fun (| c, _, _ |) -> st_comp_of_comp c == st_comp_of_comp c_then)
