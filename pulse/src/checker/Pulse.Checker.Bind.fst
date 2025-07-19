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
open Pulse.Show
open Pulse.Checker.Util

module T = FStar.Tactics.V2
module P = Pulse.Syntax.Printer
module Metatheory = Pulse.Typing.Metatheory
module Abs = Pulse.Checker.Abs
module RU = Pulse.Reflection.Util

#push-options "--z3rlimit_factor 4 --split_queries no"
let check_bind_fn
  (g:env)
  (ctxt:slprop)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
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
    if not (PostHint? post_hint)
    then fail g (Some t.range) "check_bind: please annotate the postcondition";

    let x = fresh g in
    let b = { binder with binder_ty = comp_res c } in
    let g' = push_binding g x (binder.binder_ppname) b.binder_ty in
    let ctxt_typing' : tot_typing g' ctxt tm_slprop =
      Metatheory.tot_typing_weakening_single ctxt_typing x b.binder_ty in
    let r = check g' _ ctxt_typing' post_hint res_ppname (open_st_term_nv body (binder.binder_ppname, x)) in
    let body_typing = apply_checker_result_k #_ #_ #(PostHint?.v post_hint) r res_ppname in
    let k = Pulse.Checker.Base.continuation_elaborator_with_bind_fn ctxt_typing b head_typing (binder.binder_ppname, x) in
    let d = k post_hint body_typing in
    checker_result_for_st_typing d res_ppname
  )
  | _ -> fail g (Some t.range) "check_bind_fn: head is not an abstraction"
#pop-options

let check_if_seq_lhs
  (g:env) (ctxt : slprop) (post_hint : post_hint_opt g)
  (r:checker_result_t g ctxt post_hint) (e1:st_term)
  : T.Tac unit
=
  if T.unseal e1.seq_lhs then begin
    let (| _x, g, (| u, ty, ty_wf |), _ctxt', _k |) = r in
    let open Pulse.PP in
    if T.Tv_Arrow? ty then
      fail_doc g (Some e1.range) [
        prefix 2 1 (text "This function is partially applied. Remaining type:") (pp ty);
        text "Did you forget to apply some arguments?";
      ]
    else if None? (fst <| T.is_non_informative (elab_env g) ty) then (
      if None? (Pulse.Checker.Pure.try_get_non_informative_witness g u ty ty_wf) then
        fail_doc g (Some e1.range) [
          prefix 2 1 (text "This statement returns a value of type:") (pp ty);
          text "Did you forget to assign it or ignore it?";
        ]
    ) else
      () (* ok *)
  end

let check_binder_typ
  (g:env) (ctxt : slprop) (post_hint : post_hint_opt g)
  (r:checker_result_t g ctxt post_hint)
  (b:binder) (e1:st_term)
  : T.Tac unit
=
  (* Check that the type matches the annotation, if any *)
  let ty = b.binder_ty in
  begin match inspect_term ty with
  | Tm_Unknown -> ()
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
      let open Pulse.PP in
      fail_doc g (Some e1.range) [
        text "Type mismatch (NB: this is a syntactic check)";
        prefix 2 1 (text "Expected:") (pp ty);
        prefix 2 1 (text "Got:") (pp t);
      ]
  end

let check_bind'
  (maybe_elaborate:bool)
  (g:env)
  (ctxt:slprop)
  (ctxt_typing:tot_typing g ctxt tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term {Tm_Bind? t.term})
  (check:check_t)
: T.Tac (checker_result_t g ctxt post_hint)
= let g = Pulse.Typing.Env.push_context g "check_bind" t.range in

  debug_prover g (fun _ ->
    Printf.sprintf "checking bind:\n%s\n" (P.st_term_to_string t));
  
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
    let dflt () =
      let r0 = check g ctxt ctxt_typing NoHint binder.binder_ppname e1 in
      check_if_seq_lhs g ctxt _ r0 e1;
      check_binder_typ g ctxt _ r0 binder e1;
      let (| x, g1, _, (| ctxt', ctxt'_typing |), k1 |) = r0 in
      let g1 = reset_context g1 g in
      let r1 = check g1 ctxt' ctxt'_typing post_hint ppname_default (open_st_term_nv e2 (binder.binder_ppname, x)) in
      Pulse.Checker.Base.compose_checker_result_t r0 r1 
    in
    if not maybe_elaborate then dflt()
    else (
      match e1.term with
      | Tm_Return { expected_type; insert_eq; term=tm } -> (
        let rebuild (head:either term st_term) : T.Tac st_term =
          match head with
          | Inr st_term -> { t with term = Tm_Bind { binder; head=st_term; body=e2 } }
          | Inl tm' -> 
            let head = Tm_Return { expected_type; term=tm'; insert_eq } in
            let head = mk_term head (Pulse.RuntimeUtils.range_of_term tm') in
            { t with term = Tm_Bind { binder; head; body=e2 } }
        in
        match Pulse.Checker.Base.hoist_stateful_apps g (Inl tm) false rebuild with
        | Some t -> //something was elaborated, go back to the top checking loop
          debug_prover g (fun _ -> Printf.sprintf "Bind was elaborated to %s\n" (show t));
          check g ctxt ctxt_typing post_hint res_ppname t
        | None -> 
          debug_prover g (fun _ -> "No elaboration in check_bind, proceeding to check head\n");
          dflt()
      )
      | _ ->
        let rebuild (head:either term st_term { Inr? head }) : T.Tac st_term =
          let Inr e1' = head in
          { t with term = Tm_Bind { binder; head=e1'; body=e2 } }
        in
        match Pulse.Checker.Base.hoist_stateful_apps g (Inr e1) false rebuild with
        | Some t -> //something was elaborated, go back to the top checking loop
          debug_prover g (fun _ -> Printf.sprintf "Bind was elaborated to %s\n" (show t));
          check g ctxt ctxt_typing post_hint res_ppname t
        | None -> 
          debug_prover g (fun _ -> "No elaboration in check_bind, proceeding to check head\n");
          dflt()
    )
  )

let check_bind = check_bind' true

let check_tot_bind
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (t:st_term { Tm_TotBind? t.term })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= let g = Pulse.Typing.Env.push_context g "check_tot_bind" t.range in

  let Tm_TotBind { binder=b; head=e1; body=e2 } = t.term in
  let rebuild (head:either term st_term) : T.Tac (t:st_term { Tm_Bind? t.term }) =
    match head with
    | Inl e1' ->
      let head = Tm_Return { expected_type = b.binder_ty; term = e1'; insert_eq = true } in
      let head = mk_term head (Pulse.RuntimeUtils.range_of_term e1') in
      { t with term = Tm_Bind { binder=b; head; body=e2 } }
    | Inr e1' ->
      { t with term = Tm_Bind { binder=b; head=e1'; body=e2 } }
  in
  match Pulse.Checker.Base.hoist_stateful_apps g (Inl e1) false rebuild with
  | None -> //no stateful apps; just return the head and check it
    let t = rebuild (Inl e1) in
    debug_prover g (fun _ -> Printf.sprintf "No elaboration in check_tot_bind, proceeding to check\n%s\n" (show t));
    check_bind' false g pre pre_typing post_hint res_ppname t check
  | Some t' ->
    debug_prover g (fun _ -> Printf.sprintf "Elaborated and proceeding back to top-level\n%s\nto\n%s\n" 
      (show t)
      (show t'));
    check g pre pre_typing post_hint res_ppname t'