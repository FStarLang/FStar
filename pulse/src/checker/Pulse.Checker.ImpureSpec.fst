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

module Pulse.Checker.ImpureSpec
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
open FStar.List.Tot
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Checker.Prover.RewritesTo
open Pulse.Checker.Prover.Normalize
open Pulse.Checker.Pure
open Pulse.Typing.Env
open Pulse.Checker.Base
open Pulse.Readback
open Pulse.Syntax.Naming
open Pulse.Reflection.Util
open Pulse.PP
open Pulse.Show

let old_lid = Pulse.Reflection.Util.mk_pulse_lib_core_lid "old"

let debug g (s: unit -> T.Tac (list Pprint.document)) : T.Tac unit =
  if RU.debug_at_level (fstar_env g) "pulse.impure_spec"
  then info_doc g None (s ())

let rec get_rewrites_to_from_post (g: env) xres (post: slprop) : T.Tac (option R.term) =
  match inspect_term post with
  | Tm_Star p q ->
    (match get_rewrites_to_from_post g xres p with
    | None -> get_rewrites_to_from_post g xres q
    | Some res -> Some res)
  | Tm_Pure p ->
    (match is_rewrites_to_p p with
    | None -> None
    | Some (lhs, rhs) ->
      match R.inspect_ln lhs with
      | R.Tv_Var x ->
        let x = R.inspect_namedv x in
        if x.uniq = xres then
          (debug g (fun _ -> [ text "get_rewrites_to_from_post found"; pp rhs; ]);
          // TODO: check that rhs does not contain xres
          Some rhs)
        else
          None
      | _ -> None)
  | _ -> None

let prove (g: env) (goal: slprop) (ctxt: slprop) (r: range) : T.Tac unit =
  let allow_amb = true in
  let (| g', ctxt', _ |) = Pulse.Checker.Prover.prove r g ctxt goal allow_amb in
  ()

let symb_eval_stateful_app (g: env) (ctxt: slprop) (t: term) : T.Tac R.term =
  let t, ty, _ = tc_term_phase1 g t in
  debug g (fun _ -> [ text "impure spec inferred type"; pp t; pp ty ]);
  match readback_comp ty with
  | None | Some (C_Tot ..) ->
    T.fail_doc_at [text "Impossible: not a stateful application type"; pp ty] (Some (RU.range_of_term t))
  | Some c -> match c with
  | C_STAtomic _ _ { pre; post } | C_STGhost _ { pre; post } | C_ST { pre; post } ->
    let x = fresh g in
    let x_ppn = mk_ppname_no_range "result" in
    let g' = push_binding g x (mk_ppname_no_range "result") ty in
    let post = open_term_nv post (x_ppn, x) in
    let (| post, _ |) = normalize_slprop g' post true in 
    match get_rewrites_to_from_post g x post with
    | None ->
      let head, _ = T.collect_app_ln t in
      T.fail_doc_at [
        text "Cannot use" ^/^ pp head ^/^ text "in impure spec, cannot find rewrites_to in post:";
        pp post;
      ] (Some (RU.range_of_term t))
    | Some rwr ->
      let allow_amb = true in
      prove g pre ctxt (RU.range_of_term t);
      debug g (fun _ -> [text "evaluated" ^/^ pp t ^/^ text "to" ^/^ pp rwr]);
      let rwr = RU.deep_compress rwr in // TODO: maybe this fails on uvars...
      rwr

let rec symb_eval_subterms (g:env) (ctxt: ctxt) (t:R.term) : T.Tac (bool & R.term) = 
  match R.inspect_ln t with
  | R.Tv_Abs b body ->
    debug g (fun _ -> [text "symb eval subterms abs 0"; pp t]);
    let b = R.inspect_binder b in
    let x = fresh g in
    let ppname = mk_ppname_no_range (T.unseal b.ppname) in
    let changed1, b_ty = symb_eval_subterms g ctxt b.sort in
    let b_ty, b_u = tc_type_phase1 g b_ty in
    debug g (fun _ -> [text "symb eval subterms abs 1"; pp changed1; pp b_ty]);
    let b = { b with sort = b_ty } in
    let g' = push_binding g x ppname b.sort in
    let body = open_term_nv body (ppname, x) in
    let changed2, body = symb_eval_subterms g' ctxt body in
    debug g (fun _ -> [text "symb eval subterms abs 2"; pp changed2; pp body]);
    if changed1 || changed2 then
      true, R.pack_ln (R.Tv_Abs (R.pack_binder b) (close_term body x))
    else
      false, t

  | R.Tv_Refine b body ->
    debug g (fun _ -> [text "symb eval subterms refine 0"; pp t]);
    let b = R.inspect_binder b in
    let x = fresh g in
    let ppname = mk_ppname_no_range (T.unseal b.ppname) in
    let changed1, b_ty = symb_eval_subterms g ctxt b.sort in
    let b_ty, b_u = tc_type_phase1 g b_ty in
    debug g (fun _ -> [text "symb eval subterms refine 1"; pp changed1; pp b_ty]);
    let b = { b with sort = b_ty } in
    let g' = push_binding g x ppname b.sort in
    let body = open_term_nv body (ppname, x) in
    let changed2, body = symb_eval_subterms g' ctxt body in
    debug g (fun _ -> [text "symb eval subterms refine 2"; pp changed2; pp body]);
    if changed1 || changed2 then
      true, R.pack_ln (R.Tv_Refine (R.pack_binder b) (close_term body x))
    else
      false, t

  | _ ->
    let head, args = T.collect_app_ln t in
    let fallback () =
      let g, changed, args = symb_eval_subterms_args g ctxt args in
      match is_stateful_application g t with
      | Some _ ->
        let t = RU.mk_app_flat head args (T.range_of_term t) in
        let t' = symb_eval_stateful_app g ctxt.ctxt_now t in
        true, t'
      | None ->
        if changed then
          let t = RU.mk_app_flat head args (T.range_of_term t) in
          changed, t
        else
          false, t
      in
    let r = Some (RU.range_of_term t) in
    match R.inspect_ln head, args with
    | R.Tv_FVar fv, [t, _] ->
      if R.inspect_fv fv = old_lid then
        // let t = RU.mk_app_flat head args (T.range_of_term t) in
        match is_stateful_application g t, ctxt.ctxt_old with
        | _, None ->
          T.fail_doc_at [
            text "'old' can only be used in postconditions";
          ] r
        | None, _ ->
          T.fail_doc_at [
            text "'old' needs to be applied to a stateful computation, not:";
            pp t;
          ] r
        | Some _, Some ctxt_old ->
          let head, args = T.collect_app_ln t in
          let g, changed, args = symb_eval_subterms_args g ctxt args in
          let t = RU.mk_app_flat head args (T.range_of_term t) in
          let t' = symb_eval_stateful_app g ctxt_old t in
          true, t'
      else
        fallback ()
    | _ ->
      fallback ()

and symb_eval_subterms_args (g:env) (ctxt: ctxt) (args:list T.argv)
: T.Tac (env & bool & list T.argv)
= T.fold_right
    (fun (arg, q) (g, changed, args) ->
      let changed', arg = symb_eval_subterms g ctxt arg in
      let changed = changed' || changed in
      g, changed, (arg, q)::args)
    args
    (g, false, [])

let rec run_elim_core (g: env) (ctxt: list slprop) : T.Tac (env & list nvar & list slprop) =
  match ctxt with
  | [] ->
    g, [], []
  | c::ctxt ->
    match inspect_term c with
    | Tm_WithPure p n b ->
      run_elim_core g (open_term_list' ctxt unit_const 0)
    | Tm_ExistsSL u b body ->
      let x = fresh g in
      let px = b.binder_ppname, x in
      let g' = push_binding g x (fst px) b.binder_ty in
      let body = open_term_nv body px in
      let g', xs, ctxt' = run_elim_core g' (body::ctxt) in
      g', px::xs, ctxt'
    | Tm_Star a b ->
      run_elim_core g (a::b::ctxt)
    | Tm_Pure _ | Tm_Emp ->
      run_elim_core g ctxt
    | _ ->
      let g', xs, ctxt' = run_elim_core g ctxt in
      g', xs, c::ctxt'

let run_elim (g: env) (ctxt: slprop) : T.Tac (env & list nvar & slprop) =
  let (| ctxt, _ |) = normalize_slprop g ctxt true in
  let g', xs, ctxt = run_elim_core g (slprop_as_list ctxt) in
  g', xs, list_as_slprop ctxt

(* Adds add to the ctxt in a way that the prover will prefer it when ambiguous. *)
let push_ctxt ctxt add = { ctxt with ctxt_now = tm_star add ctxt.ctxt_now }

let un_uinst (t: term) : R.term_view =
  match R.inspect_ln t with
  | R.Tv_UInst fv _ -> R.Tv_FVar fv
  | tv -> tv

let inspect_ast_term (t: term) : term_view =
  let default_view = Tm_FStar t in
  let head, args = T.collect_app_ln t in
  match un_uinst head, args with
  | R.Tv_FVar fv, [a1, R.Q_Explicit] ->
    if R.inspect_fv fv = exists_lid || R.inspect_fv fv = forall_lid then
      match R.inspect_ln a1 with
      | R.Tv_Abs b body ->
        let bview = R.inspect_binder b in
        let b = mk_binder_ppname bview.sort (mk_ppname bview.ppname (RU.binder_range b)) in
        if R.inspect_fv fv = exists_lid
        then Tm_ExistsSL u_unknown b body
        else Tm_ForallSL u_unknown b body
      | _ -> default_view
    else if R.inspect_fv fv = with_pure_lid then
      Tm_WithPure a1 ppname_default tm_emp
    else
      default_view
  | R.Tv_FVar fv, [a1, R.Q_Explicit; a2, R.Q_Explicit] ->
    if R.inspect_fv fv = star_lid then
      Tm_Star a1 a2
    else if R.inspect_fv fv = with_pure_lid then
      match R.inspect_ln a2 with
      | R.Tv_Abs b body ->
        let bview = R.inspect_binder b in
        let b = mk_ppname bview.ppname (RU.binder_range b) in
        Tm_WithPure a1 b body
      | _ -> default_view
    else
      default_view
  | _ ->
    default_view

let literally_lid = mk_pulse_lib_core_lid "literally"

let is_literally (t: term) : option term =
  let default_view = Tm_FStar t in
  let head, args = T.collect_app_ln t in
  match un_uinst head, args with
  | R.Tv_FVar fv, [a1, R.Q_Explicit] ->
    if R.inspect_fv fv = literally_lid then
      Some a1
    else
      None
  | _ -> None

let tc_term_phase1_with_type_twice g t ty =
  // If we call phase1 TC only once, then the universe instantiation in
  // coercion-inserted reveal calls remains a uvar.
  let t, eff = tc_term_phase1_with_type g t ty in
  let t, eff = tc_term_phase1_with_type g t ty in
  t, eff

let or_emp (t: option slprop) : slprop =
  match t with Some t -> t | None -> tm_emp

let rec purify_spec_core (g: env) (ctxt: ctxt) (ts: list slprop) : T.Tac (option slprop) =
  match ts with
  | [] -> None
  | t::ts ->
    match inspect_ast_term t with
    | Tm_Star t s ->
      purify_spec_core g ctxt (t::s::ts)

    | Tm_ExistsSL _ b body ->
      let x = fresh g in
      let px = b.binder_ppname, x in
      let x_ty, x_u = tc_type_phase1 g b.binder_ty in
      let b = { b with binder_ty = x_ty } in
      let g' = push_binding g x (fst px) x_ty in
      let body = open_term_nv body px in
      let body = purify_spec_core g' ctxt (body :: ts) |> or_emp in
      let body = close_term body x in
      Some (tm_exists_sl x_u b body)

    | Tm_Emp ->
      purify_spec_core g ctxt ts

    | Tm_WithPure p n body ->
      let x = fresh g in
      let px = n, x in
      let _, p = symb_eval_subterms g ctxt p in
      let p, _ = tc_type_phase1 g p in
      let x_ty = mk_squash u0 p in
      let g' = push_binding g x (fst px) x_ty in
      let body = open_term_nv body px in
      let body = purify_spec_core g' ctxt (body :: ts) |> or_emp in
      let body = close_term body x in
      Some (tm_with_pure p n body)

    | _ -> match is_literally t with

    | Some _ -> // literally t
      // NOTE: we cannot unfold the literally here, or the abs checker might
      // turn the nested exists* into a function argument.
      let t, _ = tc_term_phase1_with_type_twice g t tm_slprop in
      (match purify_spec_core g ctxt ts with
      | None -> Some t
      | Some todo -> Some (tm_star t todo))

    | None ->
      let _, t = symb_eval_subterms g ctxt t in
      debug g (fun _ -> [text "purify spec atom 1"; pp t]);
      let t, _ = tc_term_phase1_with_type_twice g t tm_slprop in

      let steps = [unascribe; primops; iota; delta_attr ["Pulse.Lib.Core.pulse_eager_unfold"]] in
      let t = T.norm_term_env (elab_env g) steps t in
      extrude g ctxt [t] ts

and extrude (g: env) (ctxt: ctxt) (todo: list slprop) (ts: list slprop) : T.Tac (option slprop) =
  match todo with
  | [] -> purify_spec_core g ctxt ts
  | t::todo ->
    match inspect_term t with
    | Tm_Star t s -> extrude g ctxt (t::s::todo) ts

    | Tm_Emp -> extrude g ctxt todo ts

    | Tm_ExistsSL u b body ->
      let x = fresh g in
      let px = b.binder_ppname, x in
      let g' = push_binding g x (fst px) b.binder_ty in
      let body = open_term_nv body px in
      let body = extrude g' ctxt (body::todo) ts |> or_emp in
      let body = close_term body x in
      Some (tm_exists_sl u b body)

    | Tm_WithPure p n body ->
      let x = fresh g in
      let px = n, x in
      let p, _ = tc_type_phase1 g p in
      let x_ty = mk_squash u0 p in
      let g' = push_binding g x (fst px) x_ty in
      let body = open_term_nv body px in
      let body = extrude g' ctxt (body::todo) ts |> or_emp in
      let body = close_term body x in
      Some (tm_with_pure p n body)

    | _ ->
      let g', xs, t' = run_elim g t in
      let ctxt = push_ctxt ctxt t' in
      match extrude g' ctxt todo ts with
      | None -> Some t
      | Some todo ->
        // TODO: check that xs is not free in todo
        Some (tm_star t todo)

let run_elim_ctxt (g: env) (ctxt: ctxt) =
  let g, xs, now = run_elim g ctxt.ctxt_now in
  let g, ys, old =
    match ctxt.ctxt_old with
    | None -> g, [], None
    | Some old ->
      let g, ys, old = run_elim g old in
      g, ys, Some old in
  g, xs @ ys, { ctxt_old = old; ctxt_now = now }

let purify_term (g: env) (ctxt: ctxt) (t: term) : T.Tac term =
  let g', xs, ctxt = run_elim_ctxt g ctxt in
  let _, t = symb_eval_subterms g ctxt t in
  t

let purify_spec (g: env) (ctxt: ctxt) (t0: slprop) : T.Tac slprop =
  let t = t0 in
  let g', xs, ctxt = run_elim_ctxt g ctxt in
  let t = purify_spec_core g' ctxt [t] |> or_emp in
  // TODO: check that xs is not free in t
  // If we call phase1 TC only once, then the universe instantiation in
  // op_Exists_Star can remain unresolved.
  let t, _ = tc_term_phase1_with_type g t tm_slprop in
  debug g (fun _ -> [ text "purified" ^/^ pp t0; text "to" ^/^ pp t ]);
  t

let purify_and_check_spec (g: env) (ctxt: ctxt) (t: slprop) =
  check_slprop g (purify_spec g ctxt t)