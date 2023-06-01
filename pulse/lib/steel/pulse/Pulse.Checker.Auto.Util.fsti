module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory

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



//
// A canonical continuation elaborator for Bind
//
val continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (Tm_Star ctxt (comp_pre c1)) Tm_VProp)
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
             g                                (Tm_Star ctxt (comp_pre c1))
             (extend x (Inl (comp_res c1)) g) (Tm_Star (open_term (comp_post c1) x) ctxt))

//
// Scaffolding for adding elims
//
// Given a function f : vprop -> T.Tac bool that decides whether a vprop
//   should be elim-ed,
//   and an mk function to create the elim term, comp, and typing,
//   add_elims will create a continuation_elaborator
//

type mk_t =
  #g:env ->
  #v:vprop ->
  tot_typing g v Tm_VProp ->
  T.Tac (option (t:st_term &
                 c:comp { stateful_comp c /\ comp_pre c == v } &
                 st_typing g t c))

val add_elims (#g:env) (#ctxt:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')


let vprop_typing g v = tot_typing g v Tm_VProp

let ghost_comp pre post = 
  C_STGhost Tm_EmpInames { u=u_zero; res=tm_unit; pre; post }

open Pulse.Checker.VPropEquiv
noeq
type prover_state (g:env) (ctxt:vprop) = {
  (* the original context is well-typed *)
  ctxt_typing: vprop_typing g ctxt;
  (* the program whose precondition we're trying to derive *)
  t:st_term;
  c:comp_st;
  t_typing:st_typing g t c;
  (* the in-progress proof state *)
  matched_pre:term; (* conjuncts that we have already derived *)
  unmatched_pre:list term; (* conjuncts remaining to be derived *)
  remaining_ctxt:list term; (* unused conjuncts in the context *)
  (* Ghost proof steps witnessing the derivation of matched_pre from ctxt *)
  proof_steps: st_term;
  proof_steps_typing: st_typing g proof_steps (ghost_comp ctxt (Tm_Star (list_as_vprop remaining_ctxt) matched_pre));
  pre_equiv:vprop_equiv g (comp_pre c) (Tm_Star (list_as_vprop unmatched_pre) matched_pre);
}

let proof_steps_post #g #o (p:prover_state g o) : vprop = Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre

let bind_proof_steps_with #g #o (p:prover_state g o) 
                                (t:st_term)
                                (c:comp_st {comp_pre c == proof_steps_post p})
                                (t_typing:st_typing g t c)
   : (t':st_term & st_typing g t' (comp_st_with_pre c o))
   = admit()

let prover_step_t = #g:_ -> #o:_ -> p:prover_state g o -> T.Tac (option (prover_state g o))
