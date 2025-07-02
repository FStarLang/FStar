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

module Pulse.Checker.Prover.ElimPure

module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Checker.Pure
open Pulse.Checker.SLPropEquiv

open Pulse.Typing
open Pulse.Typing.Combinators
module Metatheory = Pulse.Typing.Metatheory
open Pulse.Reflection.Util
open Pulse.Checker.Prover.Base
open Pulse.Checker.Prover.Util
module PS = Pulse.Checker.Prover.Substs
module RU = Pulse.RuntimeUtils

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
    let cod = mk_stt_ghost_comp u0 squash_p tm_emp_inames pure_p post in
    mk_arrow
      (R.pack_ln (R.Tv_FVar (R.pack_fv R.prop_qn)), R.Q_Explicit)
      cod
    // Following crashes in extraction
    // `(p:prop -> stt_ghost (squash p) emp_inames
    //                       (pure p)
    //                       (fun _ -> emp))

let wr t = wr t Range.range_0

let elim_pure_head_typing (g:env)
    : tot_typing g elim_pure_head (wr elim_pure_head_ty)
    = admit()

let mk_elim_pure (p:term)
  : st_term
  = let t = Tm_STApp { head = elim_pure_head;
                       arg_qual = None;
                       arg = p }
    in
    wtag (Some STT_Ghost) t


let elim_pure_comp (p:term) =
    let st : st_comp = {
        u=u_zero;
        res=wr (mk_squash u0 p);
        pre=tm_pure (wr p);
        post=tm_emp
    } in
    C_STGhost tm_emp_inames st

#push-options "--admit_smt_queries true"    
let elim_pure_typing (g:env) (p:term)
                     (p_prop:tot_typing g (wr p) (wr RT.tm_prop))
   : st_typing g (mk_elim_pure (wr p)) (elim_pure_comp p)
   = T_STApp g elim_pure_head (wr RT.tm_prop) None (elim_pure_comp p) _ (elim_pure_head_typing g) p_prop
#pop-options

let is_elim_pure (vp:term) : T.Tac bool =
  match inspect_term vp with
  | Tm_Pure _ -> true
  | _ -> false

let mk (#g:env) (#v:slprop) (v_typing:tot_typing g v tm_slprop)
  : T.Tac (option (x:ppname &
                   t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =
  match inspect_term v with
  | Tm_Pure pp ->
    let p_typing =
      Metatheory.pure_typing_inversion #g #(wr pp) v_typing in
    debug_prover g (fun _ -> Printf.sprintf "elim_pure: %s\n" (T.term_to_string pp));
    Some (| ppname_default,
            mk_elim_pure (wr pp),
            elim_pure_comp pp,
            elim_pure_typing g pp p_typing |)
  | _ -> None

let elim_pure_frame (#g:env) (#ctxt:term) (#frame:term)
  (ctxt_frame_typing:tot_typing g (ctxt * frame) tm_slprop)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (ctxt' * frame) tm_slprop &
           continuation_elaborator g (ctxt * frame) g' (ctxt' * frame)) =
  add_elims is_elim_pure mk ctxt_frame_typing uvs

let elim_pure (#g:env) (#ctxt:term) (ctxt_typing:tot_typing g ctxt tm_slprop)
  : T.Tac (g':env { env_extends g' g } &
           ctxt':term &
           tot_typing g' ctxt' tm_slprop &
           continuation_elaborator g ctxt g' ctxt') =
  let ctxt_emp_typing : tot_typing g (tm_star ctxt tm_emp) tm_slprop = RU.magic () in
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
      #(list_as_slprop pst.remaining_ctxt)
      #(preamble.frame * pst.ss.(pst.solved))
      (RU.magic ())
      pst.uvs in

  let ss : PS.ss_t = // extends pst.ss with new rewrites_to_p substitutions
    RewritesTo.get_new_substs_from_env pst.pg g' pst.ss in

  let k
    : continuation_elaborator
        pst.pg (list_as_slprop pst.remaining_ctxt * (preamble.frame * ss.(pst.solved)))
        g' (remaining_ctxt' * (preamble.frame * ss.(pst.solved))) =
    admit (); k in

  // some *s
  let k
    : continuation_elaborator
        pst.pg ((list_as_slprop pst.remaining_ctxt * preamble.frame) * ss.(pst.solved))
        g' ((remaining_ctxt' * preamble.frame) * ss.(pst.solved)) =
    
    k_elab_equiv k (RU.magic ()) (RU.magic ()) in

  let k_new
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        g' ((remaining_ctxt' * preamble.frame) * ss.(pst.solved)) =
    k_elab_trans pst.k k in
  
  assume (list_as_slprop (slprop_as_list remaining_ctxt') == remaining_ctxt');

  { pst with
    pg = g';
    remaining_ctxt = slprop_as_list remaining_ctxt';
    remaining_ctxt_frame_typing = RU.magic ();
    ss;
    nts = None;
    k = k_new;
    goals_inv = RU.magic ();  // weakening of pst.goals_inv
    solved_inv = ();
  }
