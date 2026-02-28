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

module Pulse.Typing.Combinators

module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing

let st_comp_with_pre (st:st_comp) (pre:term) : st_comp = { st with pre }

let nvar_as_binder (x:nvar) (t:term) : binder =
  mk_binder_ppname t (fst x)

val t_equiv (g:env) (st:st_term) (c:comp) (c':comp)
  : unit
  
val slprop_equiv_typing (g:env) (t0 t1:term)
  : GTot ((unit -> unit) &
          (unit -> unit))

let st_ghost_as_atomic (c:comp_st { C_STGhost? c }) = 
  C_STAtomic (comp_inames c) Neutral (st_comp_of_comp c)

val lift_ghost_atomic (g:env) (e:st_term) (c:comp_st { C_STGhost? c })
: T.Tac (unit)

val mk_bind (g:env)
            (pre:term)
            (e1:st_term)
            (e2:st_term)
            (c1:comp_st)
            (c2:comp_st)
            (px:nvar { ~ (Set.mem (snd px) (dom g)) })
            (post_hint:post_hint_opt g { comp_post_matches_hint c2 post_hint })
  : T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre /\
                        comp_post_matches_hint c post_hint })
           (requires
              (let _, x = px in
              comp_pre c1 == pre /\
              freshv g x /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2)))))
           (ensures fun _ -> True)


val bind_res_and_post_typing (g:env) (s2:comp_st) (x:var { fresh_wrt x g (freevars (comp_post s2)) })
                             (post_hint:post_hint_opt g { comp_post_matches_hint s2 post_hint })
  : T.Tac unit

val add_frame (g:env) (t:st_term) (c:comp_st)
  (frame:slprop)
  : t':st_term &
    c':comp_st { c' == add_frame c frame }

let frame_for_req_in_ctxt (g:env) (ctxt:term) (req:term)
   = term

let frame_of #g #ctxt #req (f:frame_for_req_in_ctxt g ctxt req) = f

val apply_frame (g:env)
                (t:st_term)
                (ctxt:term)
                (c:comp { stateful_comp c })
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Dv  (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) })

type st_typing_in_ctxt (g:env) (ctxt:slprop) (post_hint:post_hint_opt g) =
  t:st_term &
  c:comp_st { comp_pre c == ctxt /\ comp_post_matches_hint c post_hint }

val comp_for_post_hint (g:env) (pre:slprop)
  (post:post_hint_t { g `env_extends` post.g })
  (x:var { freshv g x })
  : T.Tac (c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c (PostHint post) })