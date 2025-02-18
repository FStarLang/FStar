(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Checker.Prover.Base

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Typing.Combinators
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2

let rec list_as_slprop' (vp:slprop) (fvps:list slprop)
  : Tot slprop (decreases fvps) =
  match fvps with
  | [] -> vp
  | hd::tl -> list_as_slprop' (tm_star vp hd) tl

let rec canon_right_aux (g:env) (vps:list slprop) (f:slprop -> T.Tac bool)
  : T.Tac (vps' : list slprop &
           fvps : list slprop &
           slprop_equiv g (list_as_slprop vps) (list_as_slprop' (list_as_slprop vps') fvps)) =

  match vps with
  | [] -> (| [], [], VE_Refl _ _ |)
  | hd::rest ->
    if f hd
    then begin
      let (| vps', fvps, _ |) = canon_right_aux g rest f in
      let v_eq = RU.magic #(slprop_equiv _ _ _) () in
      // let v_eq
      //   : slprop_equiv g (list_as_slprop vps)
      //                   (list_as_slprop (hd :: (vps' @ fvps)))
      //   = list_as_slprop_ctx g [hd] _ rest (vps' @ fvps) (VE_Refl _ _) v_eq    
      // in  
      // let v_eq
      //   : slprop_equiv g (list_as_slprop vps)
      //                   (list_as_slprop ((vps'@[hd]) @ fvps))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (slprop_equiv_swap_equiv _ _ _ hd _ (VE_Refl _ _)))
      // in
      // let v_eq 
      //   :  slprop_equiv g (list_as_slprop vps)
      //                    (list_as_slprop (vps'@(hd::fvps)))
      //   = VE_Trans _ _ _ _ v_eq (VE_Sym _ _ _ (list_as_slprop_assoc _ _ _ _)) in
      (| vps', hd :: fvps, v_eq |)
    end
    else begin
      let (| vps', pures, _ |) = canon_right_aux g rest f in
      let v_eq = RU.magic #(slprop_equiv _ _ _ ) () in //list_as_slprop_ctx g [hd] _ _ _ (VE_Refl _ _) v_eq in
      (| hd::vps', pures, v_eq |)
    end

module VP = Pulse.Checker.SLPropEquiv

let canon_right (#g:env) (#ctxt:term) (#frame:term)
  (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_slprop)
  (f:slprop -> T.Tac bool)
  : T.Tac (ctxt':term &
           tot_typing g (tm_star ctxt' frame) tm_slprop &
           continuation_elaborator g (tm_star ctxt frame) g (tm_star ctxt' frame))
  = let (| vps', pures, veq |) = canon_right_aux g (slprop_as_list ctxt) f in
    let veq : slprop_equiv g ctxt (list_as_slprop' (list_as_slprop vps') pures)
      = RU.magic () in
    let veq : slprop_equiv g (tm_star ctxt frame) (tm_star (list_as_slprop' (list_as_slprop vps') pures) frame)
      = VE_Ctxt _ _ _ _ _ veq (VE_Refl _ _) in
    (| _, VP.slprop_equiv_typing_fwd ctxt_frame_typing veq, k_elab_equiv (k_elab_unit _ _) (VE_Refl _ _) veq |)


let elim_one (#g:env)
  (ctxt:term) (frame:slprop) (p:slprop)
  (ctxt_frame_p_typing:tot_typing g (tm_star (tm_star ctxt frame) p) tm_slprop)
  (nx:ppname) (e1:st_term) (c1:comp { stateful_comp c1 /\ comp_pre c1 == p })
  (e1_typing:st_typing g e1 c1)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (tm_star ctxt' frame) tm_slprop &
           continuation_elaborator g (tm_star (tm_star ctxt frame) p) g' (tm_star ctxt' frame)) =
  
  let ctxt_frame_typing = star_typing_inversion_l ctxt_frame_p_typing in
  let x = fresh (push_env g uvs) in
  let k =
    continuation_elaborator_with_bind (tm_star ctxt frame) e1_typing ctxt_frame_p_typing (nx, x) in
  let g' = push_binding g x nx (comp_res c1) in
  let ctxt' = tm_star (open_term_nv (comp_post c1) (nx, x)) ctxt in
  let veq
    : slprop_equiv g' (tm_star (open_term_nv (comp_post c1) (nx, x)) (tm_star ctxt frame))
                     (tm_star ctxt' frame) = VE_Assoc _ _ _ _ in
  let k
    : continuation_elaborator
        g  (tm_star (tm_star ctxt frame) p)
        g' (tm_star ctxt' frame) =
    k_elab_equiv
      #g #g'
      #(tm_star (tm_star ctxt frame) p)
      #(tm_star (tm_star ctxt frame) p)
      #(tm_star (open_term_nv (comp_post c1) (nx, x)) (tm_star ctxt frame))
      #(tm_star ctxt' frame)
      k (VE_Refl g (tm_star (tm_star ctxt frame) p)) veq in
 
  let ctxt'_frame_typing : tot_typing g' (tm_star ctxt' frame) tm_slprop = RU.magic () in
  env_extends_push g x ppname_default (comp_res c1);
  (| g', ctxt', ctxt'_frame_typing, k |)

let rec elim_all (#g:env)
  (f:slprop -> T.Tac bool)
  (mk:mk_t)
  (#ctxt:term) (#frame:term) (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_slprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (bool & 
           (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_slprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame)))
   = match inspect_term ctxt with
     | Tm_Star ctxt' p ->
       let p_typing =
         star_typing_inversion_r #_ #ctxt' #p (star_typing_inversion_l ctxt_frame_typing) in
       if f p
       then match mk #_ #p p_typing with
            | Some (| nx, e1, c1, e1_typing |) ->
              let (| g', _, ctxt_typing', k |) =
                elim_one ctxt' frame p (RU.magic ()) nx e1 c1 e1_typing uvs in
              let k
                : continuation_elaborator g (tm_star (tm_star ctxt' frame) p)
                                          g' (tm_star _ frame) = k in
              let k
                : continuation_elaborator g (tm_star (tm_star ctxt' p) frame)
                                          g' (tm_star _ frame) =
                k_elab_equiv k
                  (RU.magic ()) (VE_Refl _ _) in
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
  (f:slprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_frame_typing:tot_typing g (tm_star ctxt frame) tm_slprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (bool & 
           (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_slprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame)))
   = let (| ctxt', ctxt'_typing, k |) = canon_right ctxt_frame_typing f in
     let progress, (| g', ctxt'', ctxt''_typing, k' |) =
         elim_all f mk ctxt'_typing uvs in
      progress, (| g', ctxt'', ctxt''_typing, k_elab_trans k k' |)

let rec add_elims (#g:env) (#ctxt:term) (#frame:term)
  (f:slprop -> T.Tac bool)
  (mk:mk_t)
  (ctxt_typing:tot_typing g (tm_star ctxt frame) tm_slprop)
  (uvs:env { disjoint uvs g })
   : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
            ctxt':term &
            tot_typing g' (tm_star ctxt' frame) tm_slprop &
            continuation_elaborator g (tm_star ctxt frame) g' (tm_star ctxt' frame))
   = let progress, res = add_elims_aux f mk ctxt_typing uvs in
     if not progress
     then res
     else (
      let (| g', ctxt', ctxt'_typing, k |) = res in
      let (| g'', ctxt'', ctxt''_typing, k' |) = add_elims f mk ctxt'_typing uvs in
      (| g'', ctxt'', ctxt''_typing, k_elab_trans k k' |)
     )
