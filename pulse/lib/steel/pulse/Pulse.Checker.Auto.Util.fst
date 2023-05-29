module Pulse.Checker.Auto.Util

module T = FStar.Tactics

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Checker.Framing
open Pulse.Checker.VPropEquiv

module VP = Pulse.Checker.VPropEquiv
module F = Pulse.Checker.Framing
module Metatheory = Pulse.Typing.Metatheory


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

let rec canon_right_aux (g:env) (vps:list vprop) (f:vprop -> bool)
  : vps' : list vprop &
    fvps : list vprop { forall (v:vprop). List.Tot.memP v fvps ==> f v } &
    vprop_equiv g (list_as_vprop vps) (list_as_vprop (vps' @ fvps)) =

  match vps with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::rest ->
    if f hd
    then begin
      let (| vps', fvps, v_eq |) = canon_right_aux g rest f in
      let v_eq
        : vprop_equiv g (list_as_vprop vps)
                        (list_as_vprop (hd :: (vps' @ fvps)))
        = list_as_vprop_ctx g [hd] _ rest (vps' @ fvps) (VE_Refl _ _) v_eq    
      in  
      let v_eq
        : vprop_equiv g (list_as_vprop vps)
                        (list_as_vprop ((vps'@[hd]) @ fvps))
        = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (vprop_equiv_swap_equiv _ _ _ hd _ (VE_Refl _ _)))
      in
      let v_eq 
        :  vprop_equiv g (list_as_vprop vps)
                         (list_as_vprop (vps'@(hd::fvps)))
        = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (list_as_vprop_assoc _ _ _ _)) in
      (| vps', hd :: fvps, v_eq |)
    end
    else begin
      let (| vps', pures, v_eq |) = canon_right_aux g rest f in
      let v_eq = list_as_vprop_ctx g [hd] _ _ _ (VE_Refl _ _) v_eq in
      (| hd::vps', pures, v_eq |)
    end

let canon_right (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  (f:vprop -> bool)
  : (ctxt':term &
     tot_typing g ctxt' Tm_VProp &
     continuation_elaborator g ctxt g ctxt')
  = let ctxt' = canon_vprop ctxt in
    let (| vps', pures, veq |) = canon_right_aux g (vprop_as_list ctxt) f in
    let veq : vprop_equiv g ctxt (list_as_vprop (vps'@pures)) =
        VE_Trans _ _ _ _ (vprop_list_equiv g ctxt) veq
    in
    (| _, VP.vprop_equiv_typing_fwd ctxt_typing veq, k_elab_equiv (k_elab_unit _ _) (VE_Refl _ _) veq |)

#push-options "--query_stats --fuel 2 --ifuel 2 --split_queries no --z3rlimit_factor 4"
let continuation_elaborator_with_bind (#g:env) (ctxt:term)
  (#c1:comp{stateful_comp c1})
  (#e1:st_term)
  (e1_typing:st_typing g e1 c1)
  (ctxt_pre1_typing:tot_typing g (Tm_Star ctxt (comp_pre c1)) Tm_VProp)
  : T.Tac (x:var { None? (lookup g x) } &
           continuation_elaborator
             g (Tm_Star ctxt (comp_pre c1))
             (extend x (Inl (comp_res c1)) g) (Tm_Star (open_term (comp_post c1) x) ctxt)) =

  let pre1 = comp_pre c1 in
  let res1 = comp_res c1 in
  let post1 = comp_post c1 in
  let ctxt_typing, pre1_typing = star_typing_inversion ctxt_pre1_typing in
  // let p_prop = Metatheory.pure_typing_inversion pure_typing in
  let v_eq = VE_Comm g ctxt pre1 in
  let framing_token : F.frame_for_req_in_ctxt g (Tm_Star ctxt pre1) pre1 = 
    (| ctxt, ctxt_typing, VE_Comm g pre1 ctxt  |)
  in
  let (| c1, e1_typing |) =
    Pulse.Checker.Framing.apply_frame ctxt_pre1_typing e1_typing framing_token in
  let (| u_of_1, pre_typing, _, _ |) =
    Metatheory.(st_comp_typing_inversion (comp_typing_inversion (st_typing_correctness e1_typing))) in
  let x = fresh g in
  let b = Inl res1 in
  let g' = extend x b g in
  
  let post1_opened = open_term_nv post1 (v_as_nv x) in
  let k : continuation_elaborator g (Tm_Star ctxt pre1) g' (Tm_Star post1_opened ctxt) =
    fun post_hint res ->
    let (| e2, c2, e2_typing |) = res in
    if not (stateful_comp c2) // || None? post_hint
    then T.fail "Unexpected non-stateful comp in continuation elaborate"
    else (
      let e2_typing : st_typing g' e2 c2 = e2_typing in
      let e2_closed = close_st_term e2 x in
      assume (open_st_term e2_closed x == e2);
      assert (comp_pre c1 == (Tm_Star ctxt pre1));
      assert (comp_post c1 == Tm_Star post1 ctxt);
      assert (comp_pre c2 == Tm_Star post1_opened ctxt);
      assert (open_term (comp_post c1) x == Tm_Star post1_opened (open_term ctxt x));
      // ctxt is well-typed, hence ln
      assume (open_term ctxt x == ctxt);
      assert (open_term (comp_post c1) x == comp_pre c2);
      // e2 is well-typed in g, so its fvs should be a subset of g
      assume (~ (x `Set.mem` freevars_st e2));
      if x `Set.mem` freevars (comp_post c2)
      then T.fail "Impossible"
      else (
        let t_typing, post_typing =
          Pulse.Checker.Bind.bind_res_and_post_typing g (st_comp_of_comp c2) x post_hint in
        let (| e, c, e_typing |) =
          Pulse.Checker.Bind.mk_bind
            g (Tm_Star ctxt pre1) 
            e1 e2_closed c1 c2 (v_as_nv x) e1_typing
            u_of_1 
            e2_typing
            t_typing
            post_typing
        in
        (| e, c, e_typing |)
      )
    )

  in
  (| x, k |)
#pop-options
