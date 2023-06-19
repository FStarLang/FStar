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
open Pulse.Reflection.Util
open Pulse.Checker.Auto.Elims

let elim_pure_head =
    let elim_pure_explicit_lid = mk_steel_wrapper_lid "elim_pure_explicit" in
    tm_fvar (as_fv elim_pure_explicit_lid)

let elim_pure_head_ty = 
    let open Pulse.Steel.Wrapper in
    let open Steel.Effect.Common in
    let squash_p = mk_squash u0 (RT.bound_var 0) in
    let pure_p = mk_pure (RT.bound_var 0) in
    let post =
      mk_abs squash_p R.Q_Explicit (R.pack_ln (R.Tv_FVar (R.pack_fv emp_lid)))
    in
    let cod = mk_stt_ghost_comp u0 squash_p emp_inames_tm pure_p post in
    mk_arrow
      (R.pack_ln (R.Tv_FVar (R.pack_fv R.prop_qn)), R.Q_Explicit)
      cod
    // Following crashes in extraction
    // `(p:prop -> stt_ghost (squash p) emp_inames
    //                       (pure p)
    //                       (fun _ -> emp))

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
        res=tm_fstar (mk_squash u0 p);
        pre=Tm_Pure (tm_fstar p);
        post=Tm_Emp
    } in
    C_STGhost Tm_EmpInames st

#push-options "--admit_smt_queries true"    
let elim_pure_typing (g:env) (p:host_term)
                     (p_prop:tot_typing g (tm_fstar p) (tm_fstar RT.tm_prop))
   : st_typing g (mk_elim_pure (tm_fstar p)) (elim_pure_comp p)
   = T_STApp g elim_pure_head (tm_fstar (`(prop))) None (elim_pure_comp p) _ (elim_pure_head_typing g) p_prop
#pop-options

let is_elim_pure (vp:term) : T.Tac bool =
  match vp with
  | Tm_Pure (Tm_FStar _ _) -> true
  | _ -> false

let mk (#g:env) (#v:vprop) (v_typing:tot_typing g v Tm_VProp)
  : T.Tac (option (x:ppname &
                   t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =
  match v with
  | Tm_Pure (Tm_FStar pp _) ->
    let p_typing =
      Metatheory.pure_typing_inversion #g #(tm_fstar pp) v_typing in
    Some (| ppname_default,
            mk_elim_pure (tm_fstar pp),
            elim_pure_comp pp,
            elim_pure_typing g pp p_typing |)
  | _ -> None

let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt Tm_VProp)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' Tm_VProp &
           continuation_elaborator g ctxt g' ctxt') =
  
  add_elims is_elim_pure mk ctxt_typing
 