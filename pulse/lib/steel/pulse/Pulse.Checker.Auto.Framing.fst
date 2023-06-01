module Pulse.Checker.Auto.Framing
open Pulse.Checker.Auto.Util
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.VPropEquiv
open Pulse.Typing.Metatheory
module F = Pulse.Checker.Framing


let step_match : prover_step_t = 
  fun #g #o (p:prover_state g o) ->
    let res = F.all_matches g p.unmatched_pre p.remaining_ctxt in
    match res.matched with
    | [] -> None
    | _ ->
      let matched_pre = Tm_Star (list_as_vprop res.matched) p.matched_pre in
        // remaining_ctxt ~ res.ctxt' * res.matched
      let veq 
        : vprop_equiv_x g tm_unit 
                          (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre)
                          (Tm_Star (list_as_vprop res.unmatched_q) matched_pre)
        = magic ()
      in
        // p.unmatched_pre ~ res.unmatched @ res.matched
      let pre_equiv
          : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop res.unmatched_p) matched_pre)
          = magic ()
      in
      let proof_steps_typing = st_typing_equiv_post p.proof_steps_typing veq in
      Some 
        { p with unmatched_pre = res.unmatched_p;
                 matched_pre;
                 remaining_ctxt = res.unmatched_q;
                 proof_steps_typing;
                 pre_equiv }