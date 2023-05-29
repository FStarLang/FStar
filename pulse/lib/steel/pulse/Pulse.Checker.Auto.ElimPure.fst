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
module F = Pulse.Checker.Framing
open Pulse.Reflection.Util
open Pulse.Checker.Auto.Util
    

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

let elim_one_pure (#g:env) (ctxt:term) (p:term)
                  (ctxt_p_typing:tot_typing g (Tm_Star ctxt (Tm_Pure p)) Tm_VProp)
  : T.Tac (g':env { env_extends g' g } &
           tot_typing g' ctxt Tm_VProp &
           continuation_elaborator g (Tm_Star ctxt (Tm_Pure p)) g' ctxt) =
  
  let ctxt_typing, pure_typing = star_typing_inversion ctxt_p_typing in
  let p_prop = Metatheory.pure_typing_inversion pure_typing in

  match p with
  | Tm_FStar pp _ ->
    let e1 = mk_elim_pure (tm_fstar pp) in
    let c1 = elim_pure_comp pp in
    let e1_typing = elim_pure_typing g pp p_prop in
    let (| x, k |) = continuation_elaborator_with_bind ctxt e1_typing ctxt_p_typing in
    let g' = extend x (Inl (comp_res c1)) g in
    let ctxt_g'_typing : tot_typing g' ctxt Tm_VProp =
      Metatheory.tot_typing_weakening x (Inl (comp_res c1)) ctxt_typing in
    let k
      : continuation_elaborator
          g (Tm_Star ctxt (Tm_Pure p))
          g' (Tm_Star Tm_Emp ctxt) =
      k in
    let k
      : continuation_elaborator
          g (Tm_Star ctxt (Tm_Pure p))
          g' ctxt =
      k_elab_equiv k (VE_Refl _ _) (VE_Unit _ ctxt) in
    Pulse.Checker.Common.extends_extends_env g x (Inl (comp_res c1));
    (| g', ctxt_g'_typing, k |)

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
       (| g, ctxt, ctxt_typing, k_elab_unit _ _ |)

let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
   : T.Tac (g':env { env_extends g' g } &
            ctxt':term &
            tot_typing g' ctxt' Tm_VProp &
            continuation_elaborator g ctxt g' ctxt')
   = let (| ctxt', ctxt'_typing, k |) = canon_right ctxt_typing Tm_Pure? in
     let (| g', ctxt'', ctxt''_typing, k' |) = elim_pure_right ctxt'_typing in
     extends_env_refl g;
     (| g', ctxt'', ctxt''_typing, k_elab_trans k k' |)
