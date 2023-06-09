module Pulse.Checker.Auto.IntroPure

module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot

open Pulse.Syntax
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Checker.VPropEquiv

open Pulse.Typing

module Metatheory = Pulse.Typing.Metatheory

module RT = FStar.Reflection.Typing

// let is_pure (p:term) =
//   match p with
//   | Tm_Pure (Tm_FStar _ _) -> true
//   | _ -> false

// let intro_pure_tm (p:term) =
//   let open Pulse.Reflection.Util in
//   wr (Tm_STApp
//         { head =
//             tm_pureapp (tm_fvar (as_fv (mk_steel_wrapper_lid "intro_pure")))
//                        None
//                        p;
//           arg_qual = None;
//           arg = Tm_FStar (`()) Range.range_0 })

// let intro_pure_comp (p:term) =
//   C_STGhost Tm_EmpInames {
//       u=u_zero;
//       res=tm_unit;
//       pre=Tm_Emp;
//       post=Tm_Pure p }

// let intro_pure_typing (#g:env) (#p:term)
//   (p_typing:tot_typing g p tm_prop)
//   (p_valid:tot_typing g (Tm_FStar (`()) Range.range_0) p)

//   : st_typing g (intro_pure_tm p) (intro_pure_comp p) =

//   let open Pulse.Reflection.Util in
//   assume (open_comp_with (intro_pure_comp p) (Tm_FStar (`()) Range.range_0) ==
//           intro_pure_comp p);
//   T_STApp g
//     (tm_pureapp (tm_fvar (as_fv (mk_steel_wrapper_lid "intro_pure"))) None p)
//     p
//     None
//     (intro_pure_comp p)
//     (Tm_FStar (`()) Range.range_0)
//     (magic ())  // typing of head
//     p_valid


// let intro_pure_proof_step_aux (#g:env) (ctxt:list vprop)
//   (v:vprop{is_pure v})
//   (v_typing:tot_typing g v Tm_VProp)

//   : T.Tac (option (proof_step g ctxt v)) =
  
//   let Tm_Pure p = v in
//   let p_typing : tot_typing g p (Tm_FStar RT.tm_prop Range.range_0) =
//     Metatheory.pure_typing_inversion v_typing in
  
//   match T.check_prop_validity (elab_env g) (elab_term p) with
//   | Some e, _ ->
//     let d : squash (T.typing_token (elab_env g) e (T.E_Total, (elab_term p))) =
//       FStar.Squash.get_proof _ in
//     let d : RT.typing (elab_env g) e (T.E_Total, (elab_term p)) =
//       RT.T_Token _ _ _ d in
//     let d : RT.typing (elab_env g) (`()) (T.E_Total, (elab_term p)) =
//       RT.T_PropIrrelevance _ _ _ _ T.E_Total d (magic ()) in
//     let d : tot_typing g (Tm_FStar (`()) Range.range_0) p = E d in
//     let d = intro_pure_typing p_typing d in
//     let pre_eq : vprop_equiv g (list_as_vprop ctxt)
//                                (Tm_Star Tm_Emp (list_as_vprop ctxt)) = magic () in  

//     Some {
//       remaining' = ctxt;

//       t' = intro_pure_tm p;
//       c' = intro_pure_comp p;
//       t'_typing = d;
    
//       remaining_equiv = pre_eq;
//     }
//   | _ -> None

// let intro_pure_proof_step =
//   fun #g #ctxt #v _ v_typing ->
//   if is_pure v
//   then intro_pure_proof_step_aux ctxt v v_typing
//   else None
// let get_one_pure (g:env) (l:list vprop)
//   : option (v:vprop { is_pure v } &
//             rest:list vprop &
//             vprop_equiv g (list_as_vprop l) (Tm_Star v (list_as_vprop rest))) =
//   admit ()

// let intro_pure : intro_from_unmatched_fn =
  
//   fun #g pst ->
//   match get_one_pure g pst.unmatched_pre with
//   | None -> None
//   | Some (| v, rest, veq |) ->
//     let v_typing : tot_typing g v Tm_VProp = magic () in
//     match intro_pure_proof_step_aux pst.remaining_ctxt v v_typing with
//     | Some ps ->
//       Some {
//         v;
//         ps;
//         unmatched' = rest;
//         unmatched_equiv = veq;
//       }
//     | None -> None
