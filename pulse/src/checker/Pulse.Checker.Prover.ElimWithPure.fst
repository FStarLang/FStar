(*
   Copyright 2025 Microsoft Research

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

module Pulse.Checker.Prover.ElimWithPure

module T = FStar.Tactics.V2
open Pulse.Syntax

open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Checker.Prover.Base
open Pulse.Checker.Prover.Util
module PS = Pulse.Checker.Prover.Substs
module RU = Pulse.RuntimeUtils

let elim_with_pure_head =
    let elim_pure_explicit_lid = ["Pulse"; "Lib"; "WithPure"; "elim_with_pure"] in
    tm_fvar (as_fv elim_pure_explicit_lid)

let wr t = wr t Range.range_0

let mk_elim_with_pure (pred: term) (p:term)
  : st_term
  = let t =
      Tm_ST { 
       t = T.mk_app
            (tm_pureapp elim_with_pure_head None pred)
            [tm_pureabs ppname_default.name (mk_squash u0 pred) None p Range.range_0, T.Q_Explicit];
       args = [];
      }
    in
    wtag (Some STT_Ghost) t


let elim_with_pure_comp (p:term) (n:ppname) (v:term) =
    let st : st_comp = {
        u=u_zero;
        res=wr (mk_squash u0 p);
        pre=tm_with_pure (wr p) n (wr v);
        post=open_term' v unit_const 0;
    } in
    C_STGhost tm_emp_inames st

let is_elim_with_pure (vp:term) : T.Tac bool =
  match inspect_term vp with
  | Tm_WithPure .. -> true
  | _ -> false

#push-options "--fuel 0 --ifuel 0"
let mk (#g:env) (#v:slprop) (v_typing:tot_typing g v tm_slprop)
  : T.Tac (option (x:ppname &
                   t:st_term &
                   c:comp { stateful_comp c /\ comp_pre c == v } &
                   st_typing g t c)) =
  match inspect_term v with
  | Tm_WithPure pred n pp ->
    debug_prover g (fun _ -> Printf.sprintf "elim_with_pure: %s\n" (T.term_to_string v));
    let t = mk_elim_with_pure (wr pred) (wr pp) in
    let c = elim_with_pure_comp pred n pp in
    let typ : st_typing g t c = RU.magic () in
    Some (| ppname_default, t, c, typ |)
  | _ -> None

let elim_with_pure_frame (#g:env) (#ctxt:term) (#frame:term)
  (ctxt_frame_typing:tot_typing g (ctxt * frame) tm_slprop)
  (uvs:env { disjoint uvs g })
  : T.Tac (g':env { env_extends g' g /\ disjoint uvs g' } &
           ctxt':term &
           tot_typing g' (ctxt' * frame) tm_slprop &
           continuation_elaborator g (ctxt * frame) g' (ctxt' * frame)) =
  add_elims is_elim_with_pure mk ctxt_frame_typing uvs

// a lot of this is copy-pasted from elim_exists_pst,
//   can add a common function to Prover.Common
#push-options "--z3rlimit_factor 4 --ifuel 1"
let elim_with_pure_pst (#preamble:_) (pst:prover_state preamble)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        pst'.unsolved == pst.unsolved }) =

  let prog = T.existsb is_elim_with_pure pst.remaining_ctxt in
  if not prog then pst else
  let (| g', remaining_ctxt', ty, k |) =
    elim_with_pure_frame
      #pst.pg
      #(list_as_slprop pst.remaining_ctxt)
      #(preamble.frame * pst.ss.(pst.solved))
      (RU.magic ())
      pst.uvs in

  let rwr_ss : PS.ss_t = // extends pst.ss with new rewrites_to_p substitutions
    RewritesTo.get_new_substs_from_env pst.pg g' pst.rwr_ss in

  let k
    : continuation_elaborator
        pst.pg (list_as_slprop pst.remaining_ctxt * (preamble.frame * pst.ss.(pst.solved)))
        g' (remaining_ctxt' * (preamble.frame * pst.ss.(pst.solved))) = k in

  // some *s
  let k
    : continuation_elaborator
        pst.pg ((list_as_slprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    
    k_elab_equiv k (RU.magic ()) (RU.magic ()) in

  let k_new
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        g' ((remaining_ctxt' * preamble.frame) * pst.ss.(pst.solved)) =
    k_elab_trans pst.k k in
  
  assume (list_as_slprop (slprop_as_list remaining_ctxt') == remaining_ctxt');

  { pst with
    progress=true;
    pg = g';
    remaining_ctxt = slprop_as_list remaining_ctxt';
    remaining_ctxt_frame_typing = RU.magic ();
    rwr_ss;
    nts = None;
    k = k_new;
    goals_inv = RU.magic ();  // weakening of pst.goals_inv
    solved_inv = ();
  }
#pop-options
#pop-options