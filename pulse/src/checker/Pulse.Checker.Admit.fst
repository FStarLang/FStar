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

module Pulse.Checker.Admit

module T = FStar.Tactics.V2

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Base
open Pulse.Checker.Prover

module P = Pulse.Syntax.Printer

let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_Admit? t.term })

  : T.Tac (checker_result_t g pre post_hint) =

  let t0 : st_term = t in
  let g = Pulse.Typing.Env.push_context g "check_admit" t.range in

  let Tm_Admit { ctag = c; typ=t; post } = t.term in

  let x = fresh g in
  let px = v_as_nv x in
  let res
    : (c:comp_st { comp_pre c == pre /\ comp_post_matches_hint c post_hint } &
       comp_typing g c (universe_of_comp c))
    = match post, post_hint with
      | None, None ->
        fail g None "could not find a post annotation on admit, please add one"

      | Some post1, Some post2 ->
        fail g None
          (Printf.sprintf "found two post annotations on admit: %s and %s, please remove one"
             (P.term_to_string post1)
             (P.term_to_string post2.post))
      
      | Some post, _ ->
        let (| u, t_typing |) = check_universe g t in    
        let post_opened = open_term_nv post px in      
        let (| post_opened, post_typing |) = 
          check_tot_term (push_binding g x (fst px) t) post_opened tm_slprop
        in
        let post = close_term post_opened x in
        let s : st_comp = {u;res=t;pre;post} in
        assume (open_term (close_term post_opened x) x == post_opened);
        let d_s : st_comp_typing _ s = STC _ s x t_typing pre_typing post_typing in
        (match c with
         | STT -> (| _,  CT_ST _ _ d_s |)
         | STT_Ghost -> (| _, CT_STGhost _ tm_emp_inames _ (magic ()) d_s |)
         | STT_Atomic -> (| _, CT_STAtomic _ tm_emp_inames Neutral _ (magic ()) d_s |))

      | _, Some post -> Pulse.Typing.Combinators.comp_for_post_hint pre_typing post x
  in
  let (| c, d_c |) = res in
  let d = T_Admit _ _ d_c in
  FStar.Tactics.BreakVC.break_vc ();
  // ^ This makes a big difference! Would be good to distill into
  // a smaller F*-only example and file an issue.
  let ide = T.ide () in
  let admit_diag = T.ext_getv "pulse:admit_diag" = "1" in
  let no_admit_diag = T.ext_getv "pulse:no_admit_diag" = "1" in
  (if admit_diag || (ide && not no_admit_diag) then begin
    (* If we're running interactively, print out the context and environment. *)
    let open Pulse.PP in
    let msg = [
      text "Admitting continuation.";
      text "Current context:" ^^
        indent (pp <| canon_slprop_print pre)
    ] in
    info_doc_env g (Some t0.range) msg
  end else ()) <: T.Tac unit;
  checker_result_for_st_typing (| _, _, d |) res_ppname
