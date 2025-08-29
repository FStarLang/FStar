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

module Pulse.Checker.Prover.IntroWithPure

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Typing.Metatheory
open Pulse.Checker.Pure
open Pulse.Checker.SLPropEquiv
open Pulse.Checker.Prover.Base
open Pulse.Checker.Base
open Pulse.Checker.Prover.Util
open Pulse.PP
module RU = Pulse.RuntimeUtils
module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs

let coerce_eq (#a #b:Type) (x:a) (_:squash (a == b)) : y:b{y == x} = x

let open_with_unit_const (v: slprop) : slprop =
  open_term' v unit_const 0

let intro_with_pure_head =
    let intro_pure_explicit_lid = ["Pulse"; "Lib"; "WithPure"; "intro_with_pure"] in
    tm_fvar (as_fv intro_pure_explicit_lid)

let wr t = wr t Range.range_0

let mk_intro_with_pure (pred: term) (p:term)
  : st_term
  = let t =
      Tm_ST {
          t = T.mk_app (tm_pureapp (tm_pureapp intro_with_pure_head None pred) None
                          (tm_pureabs ppname_default.name (mk_squash u0 pred) None p Range.range_0))
                        [unit_const, T.Q_Explicit];
          args = []
      }
    in
    wtag (Some STT_Ghost) t

let intro_with_pure_comp (p:term) (n:ppname) (v:term) =
    let st : st_comp = {
        u=u_zero;
        res=tm_unit;
        pre=open_with_unit_const v;
        post=tm_with_pure (wr p) n (wr v);
    } in
    C_STGhost tm_emp_inames st

let k_intro_with_pure (g:env) (p: term) (n: ppname) (v: slprop)
  (d:tot_typing g p tm_prop)
  (token:prop_validity g p) (frame:slprop)
  
  : T.Tac (continuation_elaborator g (frame * open_with_unit_const v) g (frame * tm_pure p)) =

  let t = mk_intro_with_pure p v in
  let c = intro_with_pure_comp p n v in
  let d : st_typing g t c = RU.magic () in

  let x = fresh g in

  let ppname = n in
  let k : continuation_elaborator
            g (frame * open_with_unit_const v)
            (push_binding g x ppname_default tm_unit) (tm_with_pure p n v * frame) =
    admit ();
    continuation_elaborator_with_bind frame d (RU.magic ()) (ppname, x) in

  let k : continuation_elaborator
            g frame
            (push_binding g x ppname_default tm_unit) (frame * tm_pure p) =
    k_elab_equiv k (RU.magic ()) (RU.magic ()) in

  fun post_hint r ->
  let (| t1, c1, d1 |) = r in
  let d1 : st_typing g t1 c1 = d1 in
  let empty_env = mk_env (fstar_env g) in
  assert (equal g (push_env g empty_env));
  assert (equal (push_env (push_binding g x ppname_default tm_unit) empty_env)
                (push_binding g x ppname_default tm_unit));
  let d1 : st_typing (push_binding g x ppname_default tm_unit) t1 c1 =
    st_typing_weakening
      g
      empty_env
      t1 c1 d1
      (push_binding g x ppname_default tm_unit) in

  k post_hint (| t1, c1, d1 |)

module R = FStar.Reflection.V2

module RF = FStar.Reflection.V2.Formula

let intro_with_pure (#preamble:_) (pst:prover_state preamble)
  (p: term) (n: ppname) (v: term)
  (unsolved':list slprop)
  (_:squash (pst.unsolved == (tm_with_pure p n v)::unsolved'))
  (prover:prover_t)
  : T.Tac (pst':prover_state preamble { pst' `pst_extends` pst /\
                                        is_terminal pst' }) =
  let p_ss = pst.ss.(p) in

  debug_prover pst.pg (fun _ ->
    Printf.sprintf "Intro with pure trying to typecheck prop: %s with uvs: %s\n"
      (P.term_to_string p_ss)
      (env_to_string pst.uvs));

  let _ = 
    let fvs = freevars p_ss in
    if check_disjoint pst.uvs fvs
    then ()
    else 
      fail_doc pst.pg (Some (Pulse.RuntimeUtils.range_of_term p_ss))
        [prefix 2 1 (text "Could not resolve all free variables in the proposition:")
                    (pp p_ss);]
  in

  let d = core_check_tot_term pst.pg p_ss tm_prop in
  let d_valid = T.with_policy T.ForceSMT (fun () -> check_prop_validity pst.pg p_ss d) in

  admit ();

  let preamble_sub = {
    g0 = pst.pg;
    ctxt = list_as_slprop pst.remaining_ctxt;
    frame = preamble.frame * pst.ss.(pst.solved);
    ctxt_frame_typing = RU.magic ();
    goals = open_with_unit_const v * (list_as_slprop unsolved'); 
  } in

  let k_sub:
    continuation_elaborator
      preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
      pst.pg ((list_as_slprop (slprop_as_list preamble_sub.ctxt) * preamble_sub.frame) * pst.ss.(tm_emp)) =
    coerce_eq (k_elab_unit preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)) (RU.magic ())
  in
  assume (pst.ss.(tm_emp) == tm_emp);
  let pst_sub : prover_state preamble_sub = {
    pg = pst.pg;
    remaining_ctxt = slprop_as_list preamble_sub.ctxt;
    remaining_ctxt_frame_typing = RU.magic ();
    uvs = pst.uvs;
    ss = pst.ss;
    rwr_ss = pst.rwr_ss;
    nts = None;
    solved = tm_emp;
    unsolved = (slprop_as_list (open_with_unit_const v)) @ unsolved';
    k = k_sub;
    goals_inv = RU.magic ();
    solved_inv = ();
    progress = false;
    allow_ambiguous = pst.allow_ambiguous;
  } in
  let pst_sub = prover pst_sub in
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_slprop pst_sub.remaining_ctxt * preamble_sub.frame) * pst_sub.ss.(pst_sub.solved)) =
    pst_sub.k in

  let k_intro_with_pure
    : continuation_elaborator
        pst_sub.pg ((list_as_slprop pst_sub.remaining_ctxt *
                     preamble_sub.frame *
                     pst_sub.ss.(list_as_slprop unsolved')) *
                    (pst_sub.ss.(open_with_unit_const v)))
        pst_sub.pg ( _ *
                    (tm_with_pure pst_sub.ss.(p) n pst_sub.ss.(v))) =
    k_intro_with_pure
      pst_sub.pg
      p n v
      d
      d_valid
      (list_as_slprop pst_sub.remaining_ctxt * preamble_sub.frame * pst_sub.ss.(list_as_slprop unsolved'))
  in
  let k_sub
    : continuation_elaborator
        preamble_sub.g0 (preamble_sub.ctxt * preamble_sub.frame)
        pst_sub.pg ((list_as_slprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * tm_with_pure p n v * list_as_slprop unsolved'))) =
    k_elab_trans k_sub k_intro_with_pure in

  let k
    : continuation_elaborator
        preamble.g0 (preamble.ctxt * preamble.frame)
        pst_sub.pg ((list_as_slprop pst_sub.remaining_ctxt * preamble.frame) *
                    (pst_sub.ss.(pst.solved * list_as_slprop pst.unsolved))) =
    k_elab_trans pst.k k_sub in

  let pst' : prover_state preamble = {
    pg = pst_sub.pg;
    remaining_ctxt = pst_sub.remaining_ctxt;
    remaining_ctxt_frame_typing = RU.magic ();
    uvs = pst_sub.uvs;
    ss = pst_sub.ss;
    rwr_ss = pst_sub.rwr_ss;
    nts = None;
    solved = preamble.goals;
    unsolved = [];
    k;
    goals_inv = RU.magic ();
    solved_inv = RU.magic ();
    progress = false;
    allow_ambiguous = pst_sub.allow_ambiguous;
  } in

  assume pst' `pst_extends` pst;

  pst'