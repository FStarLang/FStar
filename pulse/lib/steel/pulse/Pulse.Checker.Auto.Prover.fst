module Pulse.Checker.Auto.Prover
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.VPropEquiv
open Pulse.Typing.Metatheory
open Pulse.Checker.Auto.Util
module T = FStar.Tactics
module VP = Pulse.Checker.VPropEquiv
module F = Pulse.Checker.Framing

let vprop_typing g v = tot_typing g v Tm_VProp

let unit_const = Tm_FStar (`()) Range.range_0

let proof_steps_idem
  : st_term
  = { term = Tm_Return { ctag=STT_Ghost; insert_eq=false; term=unit_const};
      range = Range.range_0 }

let proof_steps_idem_typing (g:env) (ctxt:vprop)
  : st_typing g proof_steps_idem (ghost_comp ctxt ctxt)
  = magic()

assume
val post_with_emp (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (comp_st_with_post c (Tm_Star (canon_vprop (comp_post c)) Tm_Emp) )

module Metatheory = Pulse.Typing.Metatheory

let init_prover_state (#g:env) (#ctxt:vprop) (ctxt_typing: vprop_typing g ctxt)
                      (#t:st_term) (#c:comp_st) (t_typing: st_typing g t c)
  : prover_state g { ctxt; ctxt_typing; t; c; t_typing }
  = 
  { 
        matched_pre = Tm_Emp;
        unmatched_pre = vprop_as_list (comp_pre c);
        remaining_ctxt = vprop_as_list ctxt;

        pre_equiv = VE_Trans _ _ _ _ (vprop_list_equiv _ (comp_pre c))
                                     (VE_Sym _ _ _ (VP.ve_unit_r _ (canon_vprop (comp_pre c))));
        proof_steps=proof_steps_idem;
        proof_steps_typing=post_with_emp (proof_steps_idem_typing _ ctxt);
    }

let step_intro_exists : prover_step_t =
  fun #g p ->
  T.map_opt apply_intro_from_unmatched_step
    (Pulse.Checker.Auto.IntroExists.intro_exists p)

let step_intro_pure : prover_step_t =
  fun #g p ->
  T.map_opt apply_intro_from_unmatched_step
    (Pulse.Checker.Auto.IntroPure.intro_pure p)

let step_intro_rewrite : prover_step_t =
  fun #g p ->
  T.map_opt apply_intro_from_unmatched_step
    (Pulse.Checker.Auto.IntroRewrite.intro_rewrite p)

let rec first_success (l:list prover_step_t) : prover_step_t = 
  fun #g p ->
    match l with
    | [] -> None
    | s :: l -> 
      match s p with
      | None -> first_success l p
      | Some p -> Some p

(* Take one step of proving, matching at least one unmatched pre, or rewriting the context.
   If neither, then returns None; and the outer loop should fail reporting unmatched preconditions *)
let step : prover_step_t
  = first_success [ Pulse.Checker.Auto.Framing.step_match <: prover_step_t;
                    step_intro_exists <: prover_step_t;
                    step_intro_pure <: prover_step_t;
                    step_intro_rewrite <: prover_step_t ]

let finish #g #preamble (p:prover_state g preamble { p.unmatched_pre == [] })
  : (t:st_term & c:comp_st { comp_pre c == preamble.ctxt } & st_typing g t c)
  = assume (list_as_vprop [] == Tm_Emp);
    let veq1 : vprop_equiv _ (comp_pre preamble.c) p.matched_pre
      = VE_Trans _ _ _ _ p.pre_equiv (VE_Unit _ _) in
    let t_typing : st_typing g preamble.t (comp_st_with_pre preamble.c p.matched_pre)
      = st_typing_equiv_pre preamble.t_typing veq1 in
    let remaining_context_typing : vprop_typing g (list_as_vprop p.remaining_ctxt) = magic () in
    let framing_token : F.frame_for_req_in_ctxt g (proof_steps_post p) p.matched_pre =
      (| list_as_vprop p.remaining_ctxt,
         remaining_context_typing,
         VE_Comm _ _ _ |)
    in
    let ctxt_typing : vprop_typing g (proof_steps_post p) = magic () in
    let (| _, t_typing |) = F.apply_frame ctxt_typing t_typing framing_token in
    let (| t, t_typing |) = bind_proof_steps_with p _ _ t_typing in
    (| _, _, t_typing |)

let as_failure #g #preamble (p:prover_state g preamble) = {
  unmatched_preconditions = p.unmatched_pre;
  remaining_context = p.remaining_ctxt
}

let rec solve #g #preamble (p:prover_state g preamble)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == preamble.ctxt } &
         st_typing g t c)
        framing_failure)
  = match step p with
    | None -> Inr (as_failure p)
    | Some p ->
      match p.unmatched_pre with
      | [] -> Inl (finish p)
      | _ -> solve p

let prove_precondition (#g:env)
                       (#ctxt:term)
                       (ctxt_typing: tot_typing g ctxt Tm_VProp)
                       (#t:st_term)
                       (#c:comp_st)
                       (t_typing: st_typing g t c)
  : T.Tac 
    (either 
        (t:st_term &
         c:comp_st { comp_pre c == ctxt } &
         st_typing g t c)
        framing_failure)
   = solve (init_prover_state ctxt_typing t_typing)
