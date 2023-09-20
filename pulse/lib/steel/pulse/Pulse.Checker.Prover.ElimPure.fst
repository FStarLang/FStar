module Pulse.Checker.Prover.ElimPure

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Checker.Pure
open Pulse.Checker.VPropEquiv

open Pulse.Typing
open Pulse.Typing.Combinators
module Metatheory = Pulse.Typing.Metatheory
open Pulse.Reflection.Util
open Pulse.Checker.Prover.Base

let elim_pure_head =
    let elim_pure_explicit_lid = mk_pulse_lib_core_lid "elim_pure_explicit" in
    tm_fvar (as_fv elim_pure_explicit_lid)

let elim_pure_head_ty = 
    // let open Pulse.Steel.Wrapper in
    // let open Steel.Effect.Common in
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

let tm_fstar t = tm_fstar t Range.range_0

let elim_pure_head_typing (g:env)
    : tot_typing g elim_pure_head (tm_fstar elim_pure_head_ty)
    = admit()

let mk_elim_pure (p:term)
  : st_term
  = let t = Tm_STApp { head = elim_pure_head;
                       arg_qual = None;
                       arg = p }
    in
    wtag (Some STT_Ghost) t


let elim_pure_comp (p:host_term) =
    let st : st_comp = {
        u=u_zero;
        res=tm_fstar (mk_squash u0 p);
        pre=tm_pure (tm_fstar p);
        post=tm_emp
    } in
    C_STGhost tm_emp_inames st

#push-options "--admit_smt_queries true"    
let elim_pure_typing (g:env) (p:host_term)
                     (p_prop:tot_typing g (tm_fstar p) (tm_fstar RT.tm_prop))
   : st_typing g (mk_elim_pure (tm_fstar p)) (elim_pure_comp p)
   = T_STApp g elim_pure_head (tm_fstar RT.tm_prop) None (elim_pure_comp p) _ (elim_pure_head_typing g) p_prop
#pop-options

let is_elim_pure (vp:term) : T.Tac bool =
  match vp.t with
  | Tm_Pure {t=Tm_FStar _} -> true
  | _ -> false

let mk (#g:env) (#v:vprop) (v_typing:tot_typing g v tm_vprop)
  : T.Tac (option (x:ppname &
                   t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =
  match v.t with
  | Tm_Pure {t=Tm_FStar pp} ->
    let p_typing =
      Metatheory.pure_typing_inversion #g #(tm_fstar pp) v_typing in
    Some (| ppname_default,
            mk_elim_pure (tm_fstar pp),
            elim_pure_comp pp,
            elim_pure_typing g pp p_typing |)
  | _ -> None

let elim_pure_frame (#g:env) (#ctxt:term) (#frame:term)
  (ctxt_frame_typing:tot_typing g (ctxt * frame) tm_vprop)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (ctxt' * frame) tm_vprop &
           continuation_elaborator g (ctxt * frame) g' (ctxt' * frame)) =
  add_elims is_elim_pure mk ctxt_frame_typing uvs

let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_vprop)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' tm_vprop &
           continuation_elaborator g ctxt g' ctxt') =
  let ctxt_emp_typing : tot_typing g (tm_star ctxt tm_emp) tm_vprop = magic () in
  let (| g', ctxt', ctxt'_emp_typing, k |) =
    elim_pure_frame ctxt_emp_typing (mk_env (fstar_env g)) in
  let k = k_elab_equiv k (VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _))
                         (VE_Trans _ _ _ _ (VE_Comm _ _ _) (VE_Unit _ _)) in
  (| g', ctxt', star_typing_inversion_l ctxt'_emp_typing, k |)
 
// a lot of this is copy-pasted from elim_exists_pst,
//   can add a common function to Prover.Common
let elim_pure_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved }) =

  let (| g', remaining_ctxt', ty, k |) =
    elim_pure_frame
      #pst.pg
      #(list_as_vprop pst.remaining_ctxt)
      #(preamble.frame * pst.ss.(pst.solved))
      (magic ())
      pst.uvs in

  let k
    : continuation_elaborator
        pst.pg (list_as_vprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
        g' (remaining_ctxt' * (preamble.frame * pst.ss.(pst.solved))) = k in
  
  // some *s
  let k
    : continuation_elaborator
        pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    
    k_elab_equiv k (magic ()) (magic ()) in

  let k_new
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    k_elab_trans pst.k k in
  
  assume (list_as_vprop (vprop_as_list remaining_ctxt') == remaining_ctxt');

  { pst with
    pg = g';
    remaining_ctxt = vprop_as_list remaining_ctxt';
    remaining_ctxt_frame_typing = magic ();
    k = k_new;
    goals_inv = magic ();  // weakening of pst.goals_inv
    solved_inv = ();
  }
