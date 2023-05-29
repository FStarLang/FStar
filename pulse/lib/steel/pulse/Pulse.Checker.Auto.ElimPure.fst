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

let is_elim_pure (vp:term) =
  match vp with
  | Tm_Pure (Tm_FStar _ _) -> true
  | _ -> false

let get_pure_prop (vp:term{is_elim_pure vp}) =
  match vp with
  | Tm_Pure (Tm_FStar pp _) -> pp

let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' Tm_VProp &
           continuation_elaborator g ctxt g' ctxt') =
  
  add_elims
    is_elim_pure
    (fun v -> mk_elim_pure (tm_fstar (get_pure_prop v)))
    (fun v -> elim_pure_comp (get_pure_prop v))
    (fun #g v v_typing ->
     let p_typing = Metatheory.pure_typing_inversion #g #(tm_fstar (get_pure_prop v)) v_typing in
     elim_pure_typing g (get_pure_prop v) p_typing)
    ctxt_typing
 