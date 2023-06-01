module Pulse.Checker.Auto.Framing
open Pulse.Checker.Auto.Util
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.VPropEquiv
open Pulse.Typing.Metatheory
module F = Pulse.Checker.Framing
open FStar.List.Tot

let vprop_equiv_as_x (g:env) (p q:vprop) (_:vprop_equiv g p q) (t:term) : vprop_equiv_x g t p q = admit()

let step_match : prover_step_t = 
  fun #g #o (p:prover_state g o) ->
    let res = F.all_matches g p.unmatched_pre p.remaining_ctxt in
    match res.matched with
    | [] -> None
    | _ ->
      let matched_pre = Tm_Star (list_as_vprop res.matched) p.matched_pre in
        // remaining_ctxt ~ res.ctxt' * res.matched
      let aux  p q r s (v1:vprop_equiv g p (Tm_Star (list_as_vprop (q@r)) s))
          : vprop_equiv g p (Tm_Star (list_as_vprop q) (Tm_Star (list_as_vprop r) s))
          = let v1 : vprop_equiv g p (Tm_Star (Tm_Star (list_as_vprop q) (list_as_vprop r)) s) =
                VE_Trans _ _ _ _ v1 (VE_Ctxt _ _ _ _ _ (list_as_vprop_append _ _ _) (VE_Refl _ _))
            in
            VE_Trans _ _ _ _ v1 (VE_Sym _ _ _ (VE_Assoc _ _ _ _ ))
      in
      let veq
        : vprop_equiv g (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre)
                        (Tm_Star (list_as_vprop res.unmatched_q) matched_pre)
        = let q_eq : vprop_equiv g (list_as_vprop p.remaining_ctxt) (list_as_vprop (res.unmatched_q @ res.matched)) = res.q_eq in
          let eq : vprop_equiv g (Tm_Star (list_as_vprop p.remaining_ctxt) p.matched_pre)
                                 (Tm_Star (list_as_vprop (res.unmatched_q @ res.matched)) p.matched_pre) =
                  VE_Ctxt _ _ _ _ _ q_eq (VE_Refl _ _)
          in
          aux _ _ _ _ eq
      in
        // p.unmatched_pre ~ res.unmatched @ res.matched
      let pre_equiv
          : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop res.unmatched_p) matched_pre)
          = let p_eq : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop p.unmatched_pre) p.matched_pre) = p.pre_equiv in
            let step_eq : vprop_equiv g (list_as_vprop p.unmatched_pre) (list_as_vprop (res.unmatched_p @ res.matched)) = res.p_eq in
            let p_eq  : vprop_equiv g (comp_pre p.c) (Tm_Star (list_as_vprop (res.unmatched_p @ res.matched)) p.matched_pre) =
                VE_Trans _ _ _ _ p_eq (VE_Ctxt _ _ _ _ _ step_eq (VE_Refl _ _)) in   
            aux _ _ _ _ p_eq
      in
      let proof_steps_typing = st_typing_equiv_post p.proof_steps_typing (vprop_equiv_as_x _ _ _ veq _) in
      Some 
        { p with unmatched_pre = res.unmatched_p;
                 matched_pre;
                 remaining_ctxt = res.unmatched_q;
                 proof_steps_typing;
                 pre_equiv }