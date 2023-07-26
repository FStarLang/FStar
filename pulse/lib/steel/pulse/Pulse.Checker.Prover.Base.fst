module Pulse.Checker.Prover.Base

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Typing.Combinators

module T = FStar.Tactics.V2
module PS = Pulse.Checker.Prover.Substs

let rec list_as_vprop' (vp:vprop) (fvps:list vprop)
  : Tot vprop (decreases fvps) =
  match fvps with
  | [] -> vp
  | hd::tl -> list_as_vprop' (tm_star vp hd) tl

let rec canon_right_aux (g:env) (vps:list vprop) (f:vprop -> T.Tac bool)
  : T.Tac (vps' : list vprop &
           fvps : list vprop &
           vprop_equiv g (list_as_vprop vps) (list_as_vprop' (list_as_vprop vps') fvps)) =

  match vps with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::rest ->
    if f hd
    then begin
      let (| vps', fvps, _ |) = canon_right_aux g rest f in
      let v_eq = magic () in
      // let v_eq
      //   : vprop_equiv g (list_as_vprop vps)
      //                   (list_as_vprop (hd :: (vps' @ fvps)))
      //   = list_as_vprop_ctx g [hd] _ rest (vps' @ fvps) (VE_Refl _ _) v_eq    
      // in  
      // let v_eq
      //   : vprop_equiv g (list_as_vprop vps)
      //                   (list_as_vprop ((vps'@[hd]) @ fvps))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (vprop_equiv_swap_equiv _ _ _ hd _ (VE_Refl _ _)))
      // in
      // let v_eq 
      //   :  vprop_equiv g (list_as_vprop vps)
      //                    (list_as_vprop (vps'@(hd::fvps)))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (list_as_vprop_assoc _ _ _ _)) in
      (| vps', hd :: fvps, v_eq |)
    end
    else begin
      let (| vps', pures, _ |) = canon_right_aux g rest f in
      let v_eq = magic () in //list_as_vprop_ctx g [hd] _ _ _ (VE_Refl _ _) v_eq in
      (| hd::vps', pures, v_eq |)
    end

module VP = Pulse.Checker.VPropEquiv

let canon_right (#g:env) (#ctxt:term) (#frame:term)
  (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (f:vprop -> T.Tac bool)
  : T.Tac (ctxt':term &
           tot_typing g (tm_star ctxt' frame) tm_vprop &
           continuation_elaborator g (tm_star ctxt frame) g (tm_star ctxt' frame))
  = let (| vps', pures, veq |) = canon_right_aux g (vprop_as_list ctxt) f in
    let veq : vprop_equiv g ctxt (list_as_vprop' (list_as_vprop vps') pures)
      = magic () in
    let veq : vprop_equiv g (tm_star ctxt frame) (tm_star (list_as_vprop' (list_as_vprop vps') pures) frame)
      = VE_Ctxt _ _ _ _ _ veq (VE_Refl _ _) in
    (| _, VP.vprop_equiv_typing_fwd ctxt_frame_typing veq, k_elab_equiv (k_elab_unit _ _) (VE_Refl _ _) veq |)


let elim_one (#g:env)
  (ctxt:term) (frame:vprop) (p:vprop)
  (ctxt_frame_p_typing:tot_typing g (tm_star (tm_star ctxt frame) p) tm_vprop)
  (nx:ppname) (e1:st_term) (c1:comp { stateful_comp c1 /\ comp_pre c1 == p })
  (e1_typing:st_typing g e1 c1)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (tm_star ctxt' frame) tm_vprop &
           continuation_elaborator g (tm_star (tm_star ctxt frame) p) g' (tm_star ctxt' frame)) =
  
  let ctxt_frame_typing = star_typing_inversion_l ctxt_frame_p_typing in
  let x = fresh (push_env g uvs) in
  let ppname = mk_ppname_no_range "_pelim" in
  let k =
    continuation_elaborator_with_bind (tm_star ctxt frame) e1_typing ctxt_frame_p_typing (ppname, x) in
  let g' = push_binding g x nx (comp_res c1) in
  let ctxt' = tm_star (open_term_nv (comp_post c1) (v_as_nv x)) ctxt in
  let veq
    : vprop_equiv g' (tm_star (open_term_nv (comp_post c1) (v_as_nv x)) (tm_star ctxt frame))
                     (tm_star ctxt' frame) = VE_Assoc _ _ _ _ in
  let k
    : continuation_elaborator
        g  (tm_star (tm_star ctxt frame) p)
        g' (tm_star ctxt' frame) =
    k_elab_equiv
      #g #g'
      #(tm_star (tm_star ctxt frame) p)
      #(tm_star (tm_star ctxt frame) p)
      #(tm_star (open_term_nv (comp_post c1) (v_as_nv x)) (tm_star ctxt frame))
      #(tm_star ctxt' frame)
      k (VE_Refl g (tm_star (tm_star ctxt frame) p)) veq in
 
  let ctxt'_frame_typing : tot_typing g' (tm_star ctxt' frame) tm_vprop = magic () in
  env_extends_push g x ppname_default (comp_res c1);
  (| g', ctxt', ctxt'_frame_typing, k |)

let rec elim_all (#g:env)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (#ctxt:term) (#frame:term) (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (bool & 
           (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_vprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame)))
   = match ctxt.t with
     | Tm_Star ctxt' p ->
       let p_typing =
         star_typing_inversion_r #_ #ctxt' #p (star_typing_inversion_l ctxt_frame_typing) in
       if f p
       then match mk #_ #p p_typing with
            | Some (| nx, e1, c1, e1_typing |) ->
              let (| g', _, ctxt_typing', k |) =
                elim_one ctxt' frame p (magic ()) nx e1 c1 e1_typing uvs in
              let k
                : continuation_elaborator g (tm_star (tm_star ctxt' frame) p)
                                          g' (tm_star _ frame) = k in
              let k
                : continuation_elaborator g (tm_star (tm_star ctxt' p) frame)
                                          g' (tm_star _ frame) =
                k_elab_equiv k
                  (magic ()) (VE_Refl _ _) in
              let _, (| g'', ctxt'', ctxt_typing'', k' |) =
                elim_all #g' f mk ctxt_typing' uvs in
              true, (| g'', ctxt'', ctxt_typing'', k_elab_trans k k' |)
            | None ->
              false, (| g, ctxt, ctxt_frame_typing, k_elab_unit _ _ |)
       else begin
         false, (| g, ctxt, ctxt_frame_typing, k_elab_unit _ _ |)
       end
     | _ ->
       false, (| g, ctxt, ctxt_frame_typing, k_elab_unit _ _ |)

let add_elims_aux (#g:env) (#ctxt:term) (#frame:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (bool & 
           (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_vprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame)))
   = let (| ctxt', ctxt'_typing, k |) = canon_right ctxt_frame_typing f in
     let progress, (| g', ctxt'', ctxt''_typing, k' |) =
         elim_all f mk ctxt'_typing uvs in
      progress, (| g', ctxt'', ctxt''_typing, k_elab_trans k k' |)

let rec add_elims (#g:env) (#ctxt:term) (#frame:term)
  (f:vprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g (tm_star ctxt frame) tm_vprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_vprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame))
   = let progress, res = add_elims_aux f mk ctxt_typing uvs in
     if not progress
     then res
     else (
      let (| g', ctxt', ctxt'_typing, k |) = res in
      let (| g'', ctxt'', ctxt''_typing, k' |) = add_elims f mk ctxt'_typing uvs in
      (| g'', ctxt'', ctxt''_typing, k_elab_trans k k' |)
     )
