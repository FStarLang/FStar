module Pulse.Checker.Auto.ElimPure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Typing
module Metatheory = Pulse.Typing.Metatheory
module VP = Pulse.Checker.VPropEquiv
open Pulse.Reflection.Util
let k_elab_trans (#g0 #g1 #g2:env) (#ctxt0 #ctxt1 #ctxt2:term)
                 (k0:continuation_elaborator g0 ctxt0 g1 ctxt1)
                 (k1:continuation_elaborator g1 ctxt1 g2 ctxt2 { g1 `env_extends` g0})
   : continuation_elaborator g0 ctxt0 g2 ctxt2
   = fun post_hint res -> k0 post_hint (k1 post_hint res)

let elim_pure_head =
    let elim_pure_explicit_lid = mk_steel_wrapper_lid "elim_pure_explicit" in
    tm_fvar (as_fv elim_pure_explicit_lid)

let elim_pure_head_ty = 
    let open Pulse.Steel.Wrapper in
    let open Steel.Effect.Common in
    `(p:prop -> stt_ghost (squash p) emp_inames
                          (pure p)
                          (fun _ -> emp))

let tm_fstar t = Tm_FStar t Range.range_0

let elim_pure_head_typing (g:env)
    : tot_typing g elim_pure_head (tm_fstar elim_pure_head_ty)
    = admit()

let mk_elim_pure (p:term)
  : st_term
  = let t = Tm_STApp { head = elim_pure_head;
                       arg_qual = None;
                       arg = p }
    in
    wr t


let elim_pure_comp (p:host_term) =
    let st : st_comp = {
        u=u_zero;
        res=tm_fstar (T.mk_squash p);
        pre=Tm_Pure (tm_fstar p);
        post=Tm_Emp
    } in
    C_STGhost Tm_EmpInames st
    
let elim_pure_typing (g:env) (p:host_term)
                     (p_prop:tot_typing g (tm_fstar p) (tm_fstar RT.tm_prop))
   : st_typing g (mk_elim_pure (tm_fstar p)) (elim_pure_comp p)
   = admit();
     T_STApp g elim_pure_head (tm_fstar (`(prop))) None (elim_pure_comp p) _ (elim_pure_head_typing g) p_prop

let pure_typing_inversion (#g:env) (#p:term) (_:tot_typing g (Tm_Pure p) Tm_VProp)
   : tot_typing g p (tm_fstar RT.tm_prop)
   = admit()

let elim_one_pure (#g:env) (ctxt:term) (p:term)
                  (ctxt_p_typing:tot_typing g (Tm_Star ctxt (Tm_Pure p)) Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            tot_typing g' ctxt Tm_VProp &
            continuation_elaborator g (Tm_Star ctxt (Tm_Pure p)) g' ctxt)
   = let ctxt_typing, pure_typing = star_typing_inversion ctxt_p_typing in
     let p_prop = pure_typing_inversion pure_typing in
     let v_eq = VE_Comm g ctxt (Tm_Pure p) in
     let framing_token = 
        (| ctxt, ctxt_typing, VE_Comm g ctxt (Tm_Pure p) |)
     in
     match p with
     | Tm_FStar pp _ ->
       let _ = Pulse.Checker.Framing.apply_frame ctxt_p_typing (elim_pure_typing g pp p_prop) in
       let x = fresh g in
       let b = (Inl (comp_res (elim_pure_comp pp))) in
       let g' = extend x b g in
       let k : continuation_elaborator g (Tm_Star ctxt (Tm_Pure p)) g' ctxt =
           fun post_hint res -> admit()

       in
       Pulse.Checker.Common.extends_extends_env g x b;
       (| g', Metatheory.tot_typing_weakening x b ctxt_typing, k |)
     | _ -> T.fail "unexpected pure term"
                 
let rec elim_pure_right (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
   = match ctxt with
     | Tm_Star ctxt' (Tm_Pure p) ->
       let (| g', ctxt_typing', k |) = elim_one_pure ctxt' p ctxt_typing in
       let (| g'', ctxt'', ctxt_typing'', k' |) = elim_pure_right ctxt_typing' in
       (| g'', ctxt'', ctxt_typing'', k_elab_trans k k' |)
     | _ ->
        extends_env_refl g;
        let k : continuation_elaborator g ctxt g ctxt = fun post_hint res -> res in
       (| g, ctxt, ctxt_typing, k |)

module F = Pulse.Checker.Framing
open Pulse.Checker.VPropEquiv
                        
let rec canon_pure_right_aux (g:env) (vps:list vprop)
  : vps':list vprop &
    pures:list vprop &
    vprop_equiv g (list_as_vprop vps) (list_as_vprop (vps' @ pures))
  = match vps with
    | [] -> (| [], [], VE_Refl _ _ |)
    | [Tm_Pure p] -> (| [], [Tm_Pure p], VE_Refl _ _ |)
    | Tm_Pure p :: rest -> 
      let (| vps', pures, v_eq |) = canon_pure_right_aux g rest in
      let v_eq
         : vprop_equiv g (list_as_vprop vps)
                         (list_as_vprop ((Tm_Pure p) :: (vps' @ pures)))
         = list_as_vprop_ctx g [Tm_Pure p] _ rest (vps' @ pures) (VE_Refl _ _) v_eq    
      in  
      let v_eq
         : vprop_equiv g (list_as_vprop vps)
                         (list_as_vprop ((vps'@[Tm_Pure p]) @ pures))
         = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (vprop_equiv_swap_equiv _ _ _ (Tm_Pure p) _ (VE_Refl _ _)))
      in
      let v_eq 
        :  vprop_equiv g (list_as_vprop vps)
                         (list_as_vprop (vps'@(Tm_Pure p::pures)))
        = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (list_as_vprop_assoc _ _ _ _)) in
      (| vps', Tm_Pure p :: pures, v_eq |)
    | hd::rest ->
      let (| vps', pures, v_eq |) = canon_pure_right_aux g rest in
      let v_eq = list_as_vprop_ctx g [hd] _ _ _ (VE_Refl _ _) v_eq in
      (| hd::vps', pures, v_eq |)

let vprop_equiv_typing_fwd (#g:env) (#ctxt:_) (ctxt_typing:tot_typing g ctxt Tm_VProp)
                           (#p:_) (d:vprop_equiv g ctxt p)
  : tot_typing g p Tm_VProp 
  = let fwd, _ = vprop_equiv_typing d in
    fwd ctxt_typing

let canon_pure_right (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  : (ctxt':term &
     tot_typing g ctxt' Tm_VProp &
     continuation_elaborator g ctxt g ctxt')
  = let ctxt' = canon_vprop ctxt in
    let (| vps', pures, veq |) = canon_pure_right_aux g (vprop_as_list ctxt) in
    let veq : vprop_equiv g ctxt (list_as_vprop (vps'@pures)) =
        VE_Trans _ _ _ _ (vprop_list_equiv g ctxt) veq
    in
    let veq' :vprop_equiv g (Tm_Star (list_as_vprop (vps'@pures)) Tm_Emp) ctxt =
        VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Trans _ _ _ _ (VE_Unit _ _) (VE_Sym _ _ _ veq))
    in 
    let framing_token : Pulse.Checker.Framing.frame_for_req_in_ctxt g ctxt (list_as_vprop (vps'@pures)) = 
        (| Tm_Emp, emp_typing, veq' |) in
    let k : continuation_elaborator g ctxt g (list_as_vprop (vps'@pures)) =
        fun post_hint res -> 
            let (| st, c, st_d |) = res in
            if not (stateful_comp c)
            then T.fail "Unexpected non-stateful comp in continuation elaborate"
            else (
                let (| c', st_d' |) = Pulse.Checker.Framing.apply_frame ctxt_typing st_d framing_token in
                (| _, _, st_d' |)
            )
    in
    (| _, vprop_equiv_typing_fwd ctxt_typing veq, k |)

  
                
let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
   = let (| ctxt', ctxt'_typing, k |) = canon_pure_right ctxt_typing in
     let (| g', ctxt'', ctxt''_typing, k' |) = elim_pure_right ctxt'_typing in
     extends_env_refl g;
     (| g', ctxt'', ctxt''_typing, k_elab_trans k k' |)
     




// let rec maybe_add_elims
//            (g:env)
//            (ctxt:list term)
//            (t:st_term)
//   : T.Tac st_term
//   = let wr t' = { term = t'; range = t.range } in
//     match ctxt with
//     | [] -> t
//     | Tm_ExistsSL u ty b se :: rest ->
//       let e = wr (Tm_Protect { t = wr (Tm_ElimExists { p = Tm_ExistsSL u ty b se }) }) in
//       let x = fresh g in
//       let px = v_as_nv x in
//       let g = extend x (Inl ty) g in
//       let b = open_term_nv b px in
//       let t = maybe_add_elims g [b] t in
//       let t = close_st_term t x in
//       let t = Tm_Bind { binder = default_binder_annot;
//                         head = e;
//                         body = wr (Tm_Protect { t }) } in
//       maybe_add_elims g rest (wr t)
//     | Tm_Pure p :: rest ->
//       let elim_pure_tm = 
//         wr (Tm_STApp { head = tm_fvar (as_fv elim_pure_explicit_lid);
//                        arg_qual = None;
//                        arg = p })
//       in
//       wr (
//         Tm_Bind { binder = default_binder_annot;
//                   head = wr (Tm_Protect { t = elim_pure_tm } );
//                   body = wr (Tm_Protect { t = maybe_add_elims g rest t }) }
//       )

//     | Tm_Star p q :: rest ->
//       maybe_add_elims g (p :: q :: rest) t    
      
//     | _ :: rest ->
//       maybe_add_elims g rest t