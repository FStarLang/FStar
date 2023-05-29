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

noeq
type framing_failure = {
  unmatched_preconditions : list term;
  remaining_context : list term;
}

val print_framing_failure (f:framing_failure) : T.Tac string

val check_vprop_equiv
  (g:env)
  (vp1 vp2:term)
  (vp1_typing:tot_typing g vp1 Tm_VProp)
  : T.Tac (vprop_equiv g vp1 vp2)


let frame_for_req_in_ctxt (g:env) (ctxt:term) (req:term)
   = (frame:term &
      tot_typing g frame Tm_VProp &
      vprop_equiv g (Tm_Star req frame) ctxt)

let frame_of #g #ctxt #req (f:frame_for_req_in_ctxt g ctxt req) =
  let (| frame, _, _ |) = f in frame

val check_frameable (#g:env)
                    (#ctxt:term)
                    (ctxt_typing: tot_typing g ctxt Tm_VProp)
                    (req:term)
   : T.Tac (either (frame_for_req_in_ctxt g ctxt req)
                   framing_failure)

val apply_frame (#g:env)
                (#t:st_term)
                (#ctxt:term)
                (ctxt_typing: tot_typing g ctxt Tm_VProp)
                (#c:comp { stateful_comp c })
                (t_typing: st_typing g t c)
                (frame_t:frame_for_req_in_ctxt g ctxt (comp_pre c))
  : Tot (c':comp_st { comp_pre c' == ctxt /\ comp_post c' == Tm_Star (comp_post c) (frame_of frame_t)} &
         st_typing g t c')


(* this just composes check_frameable and apply_frame *)
val try_frame_pre (#g:env)
                  (#t:st_term)
                  (#pre:term)
                  (pre_typing: tot_typing g pre Tm_VProp)
                  (#c:comp_st)
                  (t_typing: st_typing g t c)
  : T.Tac (either (c':comp_st { comp_pre c' == pre } &
                   st_typing g t c')
                  framing_failure)

val frame_empty (#g:env)
                (#pre:term)
                (pre_typing: tot_typing g pre Tm_VProp)
                (#u:universe)
                (#ty:term) 
                (ut:universe_of g ty u)
                (t:st_term)
                (c0:comp_st{ comp_pre c0 == Tm_Emp })
                (d:st_typing g t c0)
  : T.Tac (c:comp_st { comp_pre c == pre} &
           st_typing g t c)

