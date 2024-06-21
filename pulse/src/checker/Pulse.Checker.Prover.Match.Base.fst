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

module Pulse.Checker.Prover.Match.Base

open FStar.Tactics.V2
open FStar.List.Tot
open FStar.Ghost

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base
open Pulse.Checker.Prover.Base
open Pulse.PP

module RU = Pulse.RuntimeUtils
module T  = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs

let vprop_list_equiv_refl (g:env) (vs:list vprop) : vprop_list_equiv g vs vs = admit()
let vprop_list_equiv_append (g:env) (vs1 vs2 vs3 vs4 : list vprop)
  (d1 : vprop_list_equiv g vs1 vs2)
  (d2 : vprop_list_equiv g vs3 vs4)
  : vprop_list_equiv g (vs1 @ vs3) (vs2 @ vs4)
  = admit()
let vprop_list_equiv_trans (g:env) (vs1 vs2 vs3 : list vprop)
  (d1 : vprop_list_equiv g vs1 vs2)
  (d2 : vprop_list_equiv g vs2 vs3)
  : vprop_list_equiv g vs1 vs3
  = admit()
let vprop_list_equiv_assoc_l (g:env) (vs1 vs2 vs3 : list vprop)
  : vprop_list_equiv g (vs1 @ (vs2 @ vs3)) ((vs1 @ vs2) @ vs3)
  = admit()
let vprop_list_equiv_assoc_r (g:env) (vs1 vs2 vs3 : list vprop)
  : vprop_list_equiv g ((vs1 @ vs2) @ vs3) (vs1 @ (vs2 @ vs3))
  = admit()
let vprop_list_equiv_elim_append (g:env) (vs1 vs2 : list vprop)
  : vprop_equiv g (list_as_vprop (vs1 @ vs2)) (list_as_vprop vs1 * list_as_vprop vs2)
  = admit()
let vprop_list_equiv_elim_append' (g:env) (vs1 vs2 : list vprop)
  : vprop_equiv g (list_as_vprop (vs1 @ vs2)) (list_as_vprop vs2 * list_as_vprop vs1)
  = admit()

(* local aliases *)
let (>>>) #g #t0 #t1 #t2 = VE_Trans g t0 t1 t2
let (>>*) #g #t0 #t1 #t2 = vprop_list_equiv_trans g t0 t1 t2
let cong_r #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t0 * t1) (t0 * t2) =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) d
let cong_l #g #t0 #t1 #t2 (d : vprop_equiv g t1 t2) : vprop_equiv g (t1 * t0) (t2 * t0) =
  VE_Ctxt _ _ _ _ _ d (VE_Refl _ _)
let ve_refl_pf (#g:env) (p q : vprop) (s : squash (p == q)) : vprop_equiv g p q = VE_Refl g p

(* MORE LEMMAS *)

(* This is not trivial since list_as_vprop distinguishes the singleton case...
maybe it should not? *)
let list_as_vprop_cons_equiv 
  (g : env)
  (p : vprop)
  (ps : list vprop)
  : vprop_equiv g (list_as_vprop (p::ps)) (p * list_as_vprop ps)
= match ps with
  | [] ->
    let pf : vprop_equiv g p (p * tm_emp) =
      VE_Sym _ _ _ (VE_Unit _ _) >>> VE_Comm _ _ _
    in
    pf
  | _  -> VE_Refl _ _

let vprop_list_equiv_cons g p q ps qs d1 d2 =
  list_as_vprop_cons_equiv g p ps >>>
  VE_Ctxt _ _ _ _ _ d1 d2 >>>
  VE_Sym _ _ _ (list_as_vprop_cons_equiv g q qs)

let star_flip g p q r =
  VE_Assoc _ _ _ _ >>>
  VE_Ctxt _ _ _ _ _ (VE_Comm _ _ _) (VE_Refl _ _) >>>
  VE_Sym _ _ _ (VE_Assoc _ _ _ _)

let vprop_list_equiv_flip g p q ps =
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) (list_as_vprop_cons_equiv g q ps) >>>
  star_flip _ _ _ _ >>>
  VE_Ctxt _ _ _ _ _ (VE_Refl _ _) (VE_Sym _ _ _ <| list_as_vprop_cons_equiv g p ps)

let vprop_list_equiv_push_append g p ps qs = admit()

let vprop_list_equiv_append_r g ps qs rs pf = vprop_list_equiv_append _ _ _ _ _ (VE_Refl _ _) pf

let subst_append ss ps qs =
  List.Tot.Properties.map_append
    (fun t -> PS.ss_term t ss)
    ps qs

let subst_append_equiv g ss ps qs =
  subst_append ss ps qs;
  VE_Refl _ _

let subst_list_as_vprop = admit()

(* Is this somewhere else? *)
let subst_star ss p q = admit()
(* Compose two match pass results. *)
let compose_mpr (g:env) (ss : PS.ss_t) (ctxt0 unsolved0 ctxt1 unsolved1 : list vprop)
  (mpr1 : match_pass_result g ss ctxt0 unsolved0)
  (mpr2 : match_pass_result g mpr1.ss' mpr1.ctxt1 mpr1.unsolved1)
  : match_pass_result g ss ctxt0 unsolved0
= { ss' = mpr2.ss';

    ctxt_matched = mpr1.ctxt_matched @ mpr2.ctxt_matched;
    ctxt1        = mpr2.ctxt1;
    ctxt_ok      = 
      (* quite brittle to write these proofs. *)
      mpr1.ctxt_ok >>*
      (vprop_list_equiv_append _ _ _ _ _ (vprop_list_equiv_refl _ _) mpr2.ctxt_ok) >>*
      (vprop_list_equiv_assoc_l _ _ _ _)
    ;
    
    unsolved_matched = mpr1.unsolved_matched @ mpr2.unsolved_matched;
    unsolved1 = mpr2.unsolved1;
    unsolved_ok = (
      subst_append ss mpr1.unsolved_matched mpr2.unsolved_matched; (* lemma call *)
      (* proof: *)
      mpr1.unsolved_ok >>*
      (vprop_list_equiv_append _ _ _ _ _ (vprop_list_equiv_refl _ _) mpr2.unsolved_ok) >>*
      (vprop_list_equiv_assoc_l _ _ _ _)
    );

    match_ok = (
      assume (mpr1.ss' $$ mpr1.unsolved_matched == mpr2.ss' $$ mpr1.unsolved_matched);
      (* ^ should hold since mpr1.ss' fully defines the variables in unsolved_matched *)
      vprop_list_equiv_append _ _ _ _ _ mpr1.match_ok mpr2.match_ok >>*
      // VE_Sym _ _ _ (subst_append_equiv _ _ _ _) >>*
      vprop_list_equiv_append _ _ _ _ _
        (ve_refl_pf #g
           (list_as_vprop <| (mpr1.ss' $$ mpr1.unsolved_matched))
           (list_as_vprop <| (mpr2.ss' $$ mpr1.unsolved_matched))
           ()) (* relies on assumption above *)
        (VE_Refl _ _)
      >>* VE_Sym _ _ _ (subst_append_equiv _ _ _ _)
    );
  }

let apply_mpr_vequiv_proof
  (#preamble:_) (pst:prover_state preamble)
  (mpr : mpr_t pst)
  : vprop_equiv (push_env pst.pg pst.uvs)
                ((list_as_vprop pst.remaining_ctxt * preamble.frame) * (mpr.ss'.(pst.solved)))
                ((list_as_vprop mpr.ctxt1 * preamble.frame) * (mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved)))
=
  let pf0 : vprop_equiv (push_env pst.pg pst.uvs)
             (list_as_vprop pst.remaining_ctxt)
             (list_as_vprop mpr.ctxt_matched * list_as_vprop mpr.ctxt1)
  = mpr.ctxt_ok >>>
    vprop_list_equiv_elim_append _ _ _
  in
  let pf1 : vprop_equiv (push_env pst.pg pst.uvs)
             (list_as_vprop mpr.ctxt_matched * list_as_vprop mpr.ctxt1)
             (list_as_vprop mpr.ctxt1 * (mpr.ss'.(list_as_vprop mpr.unsolved_matched)))
  = subst_list_as_vprop mpr.ss' mpr.unsolved_matched;
    VE_Comm _ _ _ >>>
    VE_Ctxt _ _ _ _ _ (VE_Refl _ _) mpr.match_ok
  in
  let pf2 : vprop_equiv (push_env pst.pg pst.uvs)
             ((list_as_vprop pst.remaining_ctxt * preamble.frame) * (mpr.ss'.(pst.solved)))
             ((list_as_vprop mpr.ctxt1 * (mpr.ss'.(list_as_vprop mpr.unsolved_matched) * preamble.frame)) * (mpr.ss'.(pst.solved)))
  = cong_l (cong_l (pf0 >>> pf1)) >>>
    cong_l (VE_Sym _ _ _ (VE_Assoc _ _ _ _))
  in
  let eq : squash ((mpr.ss'.(list_as_vprop mpr.unsolved_matched) * mpr.ss'.(pst.solved))
                    ==
                   mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved))
  = subst_star mpr.ss' (list_as_vprop mpr.unsolved_matched) pst.solved;
    ()
  in
  let pf3 : vprop_equiv (push_env pst.pg pst.uvs)
             ((list_as_vprop mpr.ctxt1 * (mpr.ss'.(list_as_vprop mpr.unsolved_matched) * preamble.frame)) * (mpr.ss'.(pst.solved)))
             ((list_as_vprop mpr.ctxt1 * preamble.frame) * (mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved)))
  = 
    FStar.Pure.BreakVC.break_vc ();
    // ^ this line seems to make the proof much faster
    // and more reliable, and work without splitting!
    VE_Sym _ _ _ (VE_Assoc _ _ _ _) >>>
    cong_r (
      cong_l (VE_Comm _ _ _) >>>
      VE_Sym _ _ _ (VE_Assoc _ _ _ _) >>>
      cong_r (ve_refl_pf ((mpr.ss'.(list_as_vprop mpr.unsolved_matched)) * mpr.ss'.(pst.solved))
                         (mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved))
                         eq)
    ) >>>
    VE_Assoc _ _ _ _
  in
  pf2 >>> pf3

(* Apply a match pass result to the prover state. *)
let apply_mpr
  (#preamble:_) (pst:prover_state preamble)
  (mpr : mpr_t pst)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst })
= { pst with
      pg  = pst.pg;
      uvs = pst.uvs;
      ss  = mpr.ss';
      
      nts = None; (* Clear substitution cache *)
 
      remaining_ctxt = mpr.ctxt1;
      remaining_ctxt_frame_typing = RU.magic (); (* inversion? otherwise prove *)

      unsolved = mpr.unsolved1;
      solved   = list_as_vprop mpr.unsolved_matched * pst.solved;
      solved_inv = RU.magic (); (* freevars *)
      
      (* boring proof *)
      goals_inv =
          pst.goals_inv >>>
          (VE_Ctxt _ _ _ _ _
            (VE_Trans _ _ _ _ mpr.unsolved_ok (vprop_list_equiv_elim_append' _ _ _))
            (VE_Refl _ _)) >>>
          (VE_Sym _ _ _ <| VE_Assoc _ _ _ _)
      ;

      k = (
        assume (pst.pg == push_env pst.pg pst.uvs); // FIXME!!! Is the environment on the continuation_elaborator right??
        let k0 : continuation_elaborator
                   preamble.g0 (preamble.ctxt * preamble.frame) 
                   pst.pg      ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
        = pst.k
        in
        let k1 : continuation_elaborator
                   pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * pst.ss.(pst.solved))
                   pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * mpr.ss'.(pst.solved))
        = (admit(); k_elab_unit _ _)
        in
        let k2 : continuation_elaborator
                   pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * mpr.ss'.(pst.solved))
                   pst.pg ((list_as_vprop mpr.ctxt1          * preamble.frame) * mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved))
        = k_elab_equiv (k_elab_unit pst.pg ((list_as_vprop pst.remaining_ctxt * preamble.frame) * mpr.ss'.(pst.solved)))
            (VE_Refl _ _)
            (apply_mpr_vequiv_proof pst mpr)
        in
        let k3 : continuation_elaborator 
                   preamble.g0 (preamble.ctxt * preamble.frame) 
                   pst.pg ((list_as_vprop mpr.ctxt1          * preamble.frame) * mpr.ss'.(list_as_vprop mpr.unsolved_matched * pst.solved))
        = k0 `k_elab_trans` k1 `k_elab_trans` k2
        in
        k3
      );

      (* Set progress=true if we matched something. *)
      progress = pst.progress || Cons? mpr.ctxt_matched;
  }

