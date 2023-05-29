module Pulse.Checker.Auto.Util
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.Framing
open Pulse.Checker.VPropEquiv
module Metatheory = Pulse.Typing.Metatheory
module T = FStar.Tactics

let k_elab_unit (g:env) (ctxt:term)
  : continuation_elaborator g ctxt g ctxt
  = fun p r -> r

let k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let k_elab_equiv (#g1 #g2:env) (#ctxt1 #ctxt1' #ctxt2 #ctxt2':term)                 
                 (k:continuation_elaborator g1 ctxt1 g2 ctxt2)
                 (d1:vprop_equiv g1 ctxt1 ctxt1')
                 (d2:vprop_equiv g2 ctxt2 ctxt2')
  : continuation_elaborator g1 ctxt1' g2 ctxt2'
  =  fun post_hint res -> 
        let framing_token2 : frame_for_req_in_ctxt g2 ctxt2 ctxt2' = 
            let d : vprop_equiv g2 (Tm_Star ctxt2' Tm_Emp) ctxt2 = 
              VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) (VE_Sym _ _ _ d2)) in
            (| Tm_Emp, emp_typing, d |)
        in
        let framing_token1 : frame_for_req_in_ctxt g1 ctxt1' ctxt1 = 
            let d = VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) d1) in
            (| Tm_Emp, emp_typing, d |)
        in
        let (| st, c, st_d |) = res in
        if not (stateful_comp c)
        then T.fail "Unexpected non-stateful comp in continuation elaborate"
        else (
            let (| _, pre_typing, _, _ |) =
                Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
            let (| c', st_d' |) = Pulse.Checker.Framing.apply_frame (vprop_equiv_typing_bk pre_typing d2) st_d framing_token2 in
            let (| st, c, st_d |) = k post_hint (| st, c', st_d' |) in
            if not (stateful_comp c)
            then T.fail "Unexpected non-stateful comp in continuation elaborate"
            else 
                let (| _, pre_typing, _, _ |) =
                    Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness st_d))) in
                let (| c', st_d' |) =
                    Pulse.Checker.Framing.apply_frame
                        (vprop_equiv_typing_fwd pre_typing d1)
                        st_d
                        framing_token1 in
                (| st, c', st_d' |)
        )

