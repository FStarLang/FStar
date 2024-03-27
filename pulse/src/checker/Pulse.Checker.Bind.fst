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

module Pulse.Checker.Bind

open Pulse.Syntax
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Base
open Pulse.Checker.Pure
open Pulse.Checker.Prover

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module PS = Pulse.Checker.Prover.Substs
module Abs = Pulse.Checker.Abs


#push-options "--query_stats --z3rlimit_factor 4 --split_queries no"
let check_bind_fn
  (g:env)
  (ctxt:vprop)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term {Tm_Bind? t.term})
  (check:check_t)
: T.Tac (checker_result_t g ctxt post_hint)
= let Tm_Bind { binder; head; body } = t.term in
  match head.term with
  | Tm_Abs _ -> (
    let (| t, c, head_typing |) = Abs.check_abs g head check in
    if not (C_Tot? c)
    then fail g (Some t.range) "check_bind_fn: head is not a total abstraction";
    if None? post_hint
    then fail g (Some t.range) "check_bind: please annotate the postcondition";

    let x = fresh g in
    let b = { binder with binder_ty = comp_res c } in
    let g' = push_binding g x (binder.binder_ppname) b.binder_ty in
    let ctxt_typing' : tot_typing g' ctxt tm_vprop =
      Metatheory.tot_typing_weakening_single ctxt_typing x b.binder_ty in
    let r = check g' _ ctxt_typing' post_hint res_ppname (open_st_term_nv body (binder.binder_ppname, x)) in
    let body_typing = apply_checker_result_k #_ #_ #(Some?.v post_hint) r res_ppname in
    let k = Pulse.Checker.Base.continuation_elaborator_with_bind_fn ctxt_typing b head_typing (binder.binder_ppname, x) in
    let d = k post_hint body_typing in
    checker_result_for_st_typing d res_ppname
  )
  | _ -> fail g (Some t.range) "check_bind_fn: head is not an abstraction"
#pop-options

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check_bind
  (g:env)
  (ctxt:vprop)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term {Tm_Bind? t.term})
  (check:check_t)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_bind" t.range in

  debug_prover g (fun _ ->
    Printf.sprintf "checking bind:\n%s\n" (P.st_term_to_string t));
 
  if None? post_hint
  then fail g (Some t.range) "check_bind: post hint is not set, please add an annotation";

  let Tm_Bind { binder; head=e1; body=e2 } = t.term in
  if Tm_Admit? e1.term
  then ( //Discard the continuation if the head is an admit
    check g ctxt ctxt_typing post_hint res_ppname e1
  )
  else if Tm_Abs? e1.term
  then (
    check_bind_fn g ctxt ctxt_typing post_hint res_ppname t check
  )
  else (
    let (| x, g1, _, (| ctxt', ctxt'_typing |), k1 |) =
      let r = check g ctxt ctxt_typing None binder.binder_ppname e1 in
      (* Check that the type matches the annotation, if any *)
      let ty = binder.binder_ty in
      begin match inspect_term ty with
      | Some Tm_Unknown -> ()
      | _ ->
        let (| ty, _, _ |) = compute_tot_term_type g ty in //elaborate it first
        let (| _, _, (| _, t, _ |), _, _ |) = r in
        // TODO: once we have the rename operation then we should
        // ditch this check and just elaborate the bind
        //   let x : ty = stapp in ...
        // to
        //   let x0 = stapp in
        //   let x : t = x0 in
        //   rename x0 x; ...
        // to leverage the pure case
        if not (eq_tm ty t) then
          fail g (Some e1.range)
            (Printf.sprintf "Type mismatch: expected %s, got %s" (P.term_to_string ty) (P.term_to_string t))
      end;
      r
    in
    let g1 = reset_context g1 g in
    let d : st_typing_in_ctxt g1 ctxt' post_hint =
      let ppname = mk_ppname_no_range "_bind_c" in
      let r =
        check g1 ctxt' ctxt'_typing post_hint ppname (open_st_term_nv e2 (binder.binder_ppname, x)) in
        apply_checker_result_k #_ #_ #(Some?.v post_hint) r ppname in
    let d : st_typing_in_ctxt g ctxt post_hint = k1 post_hint d in

    checker_result_for_st_typing d res_ppname
  )


let check_tot_bind
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_TotBind? t.term })
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint) =

  let g = Pulse.Typing.Env.push_context g "check_tot_bind" t.range in

  if None? post_hint
  then fail g (Some t.range) "check_tot_bind: post hint is not set, please add an annotation";


  let Tm_TotBind { binder=b; head=e1; body=e2 } = t.term in
  match Pulse.Checker.Base.is_stateful_application g e1 with
  | Some st_app -> (
    let t = { t with term = Tm_Bind { binder=b; head=st_app; body=e2 } } in
    check_bind g pre pre_typing post_hint res_ppname t check
  )

  | None -> (
    let head = Tm_Return { expected_type = b.binder_ty; term = e1; insert_eq = true } in
    let head = { term = head; range = Pulse.RuntimeUtils.range_of_term e1; effect_tag = default_effect_hint } in
    let t = { t with term = Tm_Bind { binder=b; head; body=e2 } } in
    check_bind g pre pre_typing post_hint res_ppname t check
  )
