module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common

val k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt

val k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2

val k_elab_equiv (#g1 #g2:env) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)
                 (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
                 (d1:vprop_equiv g1 ctxt1 ctxt1')
                 (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'

val canon_right (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  (f:vprop -> bool)
  : (ctxt':term &
     tot_typing g ctxt' Tm_VProp &
     continuation_elaborator g ctxt g ctxt')

val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (Tm_Star ctxt (comp_pre c1)) Tm_VProp)
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
             g (Tm_Star ctxt (comp_pre c1))
             (extend x (Inl (comp_res c1)) g) (Tm_Star (open_term (comp_post c1) x) ctxt))

type mk_elim_tm_t (f:vprop -> bool) = v:vprop{f v} -> st_term
type mk_elim_comp_t (f:vprop -> bool) =
  v:vprop{f v} -> c:comp{stateful_comp c /\ comp_pre c == v}
type elim_tm_typing_t (#f:vprop -> bool) (mk_t:mk_elim_tm_t f) (mk_c:mk_elim_comp_t f) =
  #g:env ->
  v:vprop{f v} ->
  tot_typing g v Tm_VProp ->
  T.Tac (st_typing g (mk_t v) (mk_c v))

val add_elims (#g:env) (#ctxt:term)
  (f:vprop -> bool)
  (mk_t:mk_elim_tm_t f)
  (mk_c:mk_elim_comp_t f) 
  (mk_typing:elim_tm_typing_t mk_t mk_c)
  (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
