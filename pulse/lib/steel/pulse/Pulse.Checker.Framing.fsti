module Pulse.Checker.Framing
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
module P = Pulse.Syntax.Printer
open Pulse.Checker.VPropEquiv

noeq
type framing_failure = {
  unmatched_preconditions : list term;
  remaining_context : list term;
}

val print_framing_failure (f:framing_failure) : T.Tac string

noeq
type match_result g p q = {
  matched:list vprop;
  unmatched_p:list vprop;
  unmatched_q:list vprop;
  p_eq: vprop_equiv g (list_as_vprop p) (list_as_vprop (unmatched_p @ matched));
  q_eq: vprop_equiv g (list_as_vprop q) (list_as_vprop (unmatched_q @ matched))
}

val all_matches (g:env) (p q:list vprop)
  : T.Tac (match_result g p q)

val check_vprop_equiv
  (g:env)
  (vp1 vp2:term)
  (vp1_typing:tot_typing g vp1 tm_vprop)
  : T.Tac (vprop_equiv g vp1 vp2)


let frame_for_req_in_ctxt (g:env) (ctxt:term) (req:term)
   = (frame:term &
      tot_typing g frame tm_vprop &
      vprop_equiv g (tm_star req frame) ctxt)

let frame_of #g #ctxt #req (f:frame_for_req_in_ctxt g ctxt req) =
  let (| frame, _, _ |) = f in frame


val check_frameable (#g:env)
                    (#ctxt:term)
                    (ctxt_typing: tot_typing g ctxt tm_vprop)
                    (req:term)
   : T.Tac (either (frame_for_req_in_ctxt g ctxt req)
                   framing_failure)

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


(* this just composes check_frameable and apply_frame *)
val try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre tm_vprop)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (either (c':comp_st { comp_pre c' == pre } &
                   st_typing g t c')
                  framing_failure)

val frame_empty (#g:env)
                (#pre:term)
                (pre_typing: tot_typing g pre tm_vprop)
                (#u:universe)
                (#ty:term) 
                (ut:universe_of g ty u)
                (t:st_term)
                (c0:comp_st{ comp_pre c0 == tm_emp })
                (d:st_typing g t c0)
  : T.Tac (c:comp_st { comp_pre c == pre} &
           st_typing g t c)

