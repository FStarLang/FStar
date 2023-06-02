module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Typing.Metatheory

let continuation_elaborator (g:env) (ctxt:term)
                            (g':env) (ctxt':term) =
    post_hint:post_hint_opt g ->
    checker_result_t g' ctxt' post_hint ->
    T.Tac (checker_result_t g ctxt post_hint)

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

type prover_step_t = #g:_ -> #o:_ -> p:prover_state g o -> T.Tac (option (prover_state g o))

//
// result of an intro (pure, exists, rewrite) step
//   that consumes some vprop v from p.unmatched_pre
//

let intro_comp (c:comp) =
  C_STGhost? c /\ comp_u c == u_zero /\ comp_res c == tm_unit

//
// A proof step that provides v, eating away some of the ctxt
//
noeq
type proof_step (g:env) (ctxt:list vprop) (v:vprop) = {
  remaining' : list vprop;

  t' : st_term;
  c' : c:comp { intro_comp c /\ comp_post c == v };
  t'_typing : st_typing g t' c';

  remaining_equiv : vprop_equiv g (list_as_vprop ctxt)
                                  (Tm_Star (comp_pre c') (list_as_vprop remaining'));
}


// An intro step that makes progress by solving one conjunct
// v from the p.unmatched_pre
noeq
type intro_from_unmatched_step (#g:env) (#ctxt:vprop) (p:prover_state g ctxt) = {
  v : vprop;

  ps:proof_step g p.remaining_ctxt v;
 
  // new unmatched pre and remaining ctxt
  unmatched' : list vprop;
 
  // relation between new and old unmatched_pre and remaining_ctxt
  unmatched_equiv : vprop_equiv g (list_as_vprop p.unmatched_pre)
                                  (Tm_Star v (list_as_vprop unmatched'));
}

type proof_step_fn =
  #g:_ ->
  #ctxt:_ ->
  #v:vprop ->
  tot_typing g (list_as_vprop ctxt) Tm_VProp ->
  tot_typing g v Tm_VProp ->
  T.Tac (option (proof_step g ctxt v))

type intro_from_unmatched_fn =
  #g:_ ->
  #ctxt:_ ->
  p:prover_state g ctxt ->
  T.Tac (option (intro_from_unmatched_step p))

val apply_proof_step (#g:env) (#ctxt:vprop)
  (p:prover_state g ctxt)
  (v:vprop)
  (r:proof_step g p.remaining_ctxt v)  
  : T.Tac (p':prover_state g ctxt {
      p'.matched_pre == p.matched_pre /\
      p'.unmatched_pre == p.unmatched_pre /\
      p'.remaining_ctxt == v::r.remaining'
    })

val apply_intro_from_unmatched_step (#g:env) (#ctxt:vprop)
  (#p:prover_state g ctxt)
  (r:intro_from_unmatched_step p)
  : T.Tac (p':prover_state g ctxt {
      p'.matched_pre == Tm_Star p.matched_pre r.v /\
      p'.unmatched_pre == r.unmatched' /\
      p'.remaining_ctxt == r.ps.remaining'
    })
