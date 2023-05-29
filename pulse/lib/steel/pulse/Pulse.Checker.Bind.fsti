module Pulse.Checker.Bind
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Checker.Common

val mk_bind (g:env)
            (pre:term)
            (e1:st_term)
            (e2:st_term)
            (c1:comp_st)
            (c2:comp_st)
            (px:nvar)
            (d_e1:st_typing g e1 c1)
            (d_c1res:tot_typing g (comp_res c1) (tm_type (comp_u c1)))
            (d_e2:st_typing (extend (snd px) (Inl (comp_res c1)) g) (open_st_term_nv e2 px) c2)
            (res_typing:universe_of g (comp_res c2) (comp_u c2))
            (post_typing:tot_typing (extend (snd px) (Inl (comp_res c2)) g) (open_term_nv (comp_post c2) px) Tm_VProp)
  : T.TacH (t:st_term &
            c:comp { stateful_comp c ==> comp_pre c == pre } &
            st_typing g t c)
           (requires fun _ ->
              let _, x = px in
              comp_pre c1 == pre /\
              None? (lookup g x) /\
              (~(x `Set.mem` freevars_st e2)) /\
              open_term (comp_post c1) x == comp_pre c2 /\
              (~ (x `Set.mem` freevars (comp_post c2))))
           (ensures fun _ _ -> True)

val check_bind (g:env)
               (t:st_term{Tm_Bind? t.term})
               (pre:term)
               (pre_typing:tot_typing g pre Tm_VProp)
               (post_hint:post_hint_opt g)               
               (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c)

val check_tot_bind
  (g:env)
  (t:st_term{Tm_TotBind? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre Tm_VProp)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c ==> comp_pre c == pre } &
           st_typing g t c)

