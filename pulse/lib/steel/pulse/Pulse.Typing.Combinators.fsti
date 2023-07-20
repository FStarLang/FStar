module Pulse.Typing.Combinators

module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Typing

let st_comp_with_pre (st:st_comp) (pre:term) : st_comp = { st with pre }

let nvar_as_binder (x:nvar) (t:term) : binder =
  {binder_ty=t;binder_ppname=fst x}

val vprop_equiv_typing (#g:_) (#t0 #t1:term) (v:vprop_equiv g t0 t1)
  : GTot ((tot_typing g t0 tm_vprop -> tot_typing g t1 tm_vprop) &
          (tot_typing g t1 tm_vprop -> tot_typing g t0 tm_vprop))

val mk_bind (g:env)
            (pre:term)
            (e1:st_term)
            (e2:st_term)
            (c1:comp_st)
            (c2:comp_st)
            (px:nvar { ~ (Set.mem (snd px) (dom g)) })
            (d_e1:st_typing g e1 c1)
            (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
            (d_e2:st_typing (push_binding g (snd px) (fst px) (comp_res c1)) (open_st_term_nv e2 px) c2)
            (res_typing:universe_of g (comp_res c2) (comp_u c2))
            (post_typing:tot_typing (push_binding g (snd px) (fst px) (comp_res c2))
                                     (open_term_nv (comp_post c2) px)
                                     tm_vprop)
  : T.TacH (t:st_term &
            c:comp_st { st_comp_of_comp c == st_comp_with_pre (st_comp_of_comp c2) pre } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True)


val bind_res_and_post_typing (g:env) (s2:st_comp) (x:var { fresh_wrt x g (freevars s2.post) })
                             (post_hint:post_hint_opt g { comp_post_matches_hint (C_ST s2) post_hint })
  : T.Tac (universe_of g s2.res s2.u &
           tot_typing (push_binding g x ppname_default s2.res) (open_term_nv s2.post (v_as_nv x)) tm_vprop)

val add_frame (#g:env) (#t:st_term) (#c:comp_st) (t_typing:st_typing g t c)
  (#frame:vprop)
  (frame_typing:tot_typing g frame tm_vprop)
  : t':st_term &
    c':comp_st { c' == add_frame c frame } &
    st_typing g t' c'

let frame_for_req_in_ctxt (g:env) (ctxt:term) (req:term)
   = (frame:term &
      tot_typing g frame tm_vprop &
      vprop_equiv g (tm_star req frame) ctxt)

let frame_of #g #ctxt #req (f:frame_for_req_in_ctxt g ctxt req) =
  let (| frame, _, _ |) = f in frame

val apply_frame (#g:env)
                (#t:st_term)
                (#ctxt:term)
                (ctxt_typing: tot_typing g ctxt tm_vprop)
                (#c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Tot (c':comp_st { comp_pre c' == ctxt /\
                      comp_res c' == comp_res c /\
                      comp_u c' == comp_u c /\
                      comp_post c' == tm_star (comp_post c) (frame_of frame_t) } &
         st_typing g t c')

type st_typing_in_ctxt (g:env) (ctxt:vprop) (post_hint:post_hint_opt g) =
  t:st_term &
  c:comp { stateful_comp c ==> (comp_pre c == ctxt /\ comp_post_matches_hint c post_hint) } &
  st_typing g t c

let rec vprop_as_list (vp:term)
  : list term
  = match vp.t with
    | Tm_Emp -> []
    | Tm_Star vp0 vp1 -> vprop_as_list vp0 @ vprop_as_list vp1
    | _ -> [vp]

let rec list_as_vprop (vps:list term)
  : term
  = match vps with
    | [] -> tm_emp
    | hd::tl -> tm_star hd (list_as_vprop tl)
