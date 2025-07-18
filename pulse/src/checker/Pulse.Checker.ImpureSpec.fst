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
module PS = Pulse.Checker.Prover.Substs
open FStar.List.Tot
open Pulse.Syntax.Base
open Pulse.Syntax.Pure
open Pulse.Checker.Prover.RewritesTo
open Pulse.Checker.Pure
open Pulse.Typing.Env
open Pulse.Checker.Base
open Pulse.Readback
open Pulse.Syntax.Naming
open Pulse.Reflection.Util
open Pulse.PP
open Pulse.Checker.Prover.Substs
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

let mk_uvar (g: env) (ty: term) : T.Tac term =
  // FIXME
  tc_term_phase1_with_type g tm_unknown false ty

let prove_this (g: env) (goal: slprop) (ctxt: list slprop) : T.Tac (option (list slprop)) =
  match inspect_term goal with
  | Tm_Pure p ->
    // TODO: pure (x == ?u)
    Some []
  | Tm_ExistsSL u b body ->
    let uv = mk_uvar g b.binder_ty in
    Some (slprop_as_list (open_term' body uv 0))
  | Tm_WithPure p _ body ->
    Some (tm_pure p :: slprop_as_list (open_term' body unit_const 0))
  | Tm_Star a b ->
    Some [a; b]
  | _ ->
    let rec try_match (ctxt: list slprop) : bool =
      match ctxt with
      | [] -> false
      | c::ctxt ->
        if RU.teq_nosmt_force (elab_env g) goal c then
          true
        else
          try_match ctxt
      in
    if try_match ctxt then
      Some []
    else
      None

let rec prove_step (g: env) (goals: list slprop) (ctxt: list slprop) : T.Tac (option (list slprop)) =
  match goals with
  | [] -> None
  | goal::goals ->
    match prove_this g goal ctxt with
    | Some new_goals -> Some (new_goals @ goals)
    | None ->
      match prove_step g goals ctxt with
      | Some stepped -> Some (goal :: stepped)
      | None -> None

let rec prove_loop (g: env) (goals: list slprop) (ctxt: list slprop) : T.Tac (list slprop) =
  match prove_step g goals ctxt with
  | Some new_goals -> prove_loop g new_goals ctxt
  | None -> goals

let prove (g: env) (goal: slprop) (ctxt: slprop) (r: range) : T.Tac unit =
  let (| goal, _ |) = Pulse.Checker.Prover.normalize_slprop g goal true in
  let goal = slprop_as_list goal in
  let (| ctxt, _ |) = Pulse.Checker.Prover.normalize_slprop g ctxt true in
  let ctxt = slprop_as_list ctxt in
  match prove_loop g goal ctxt with
  | [] -> ()
  | unsolved_goals ->
    T.fail_doc_at [
      text "Cannot prove remaining precondition:";
      separate (break_ 1) (T.map pp unsolved_goals);
      text "from context:";
      separate (break_ 1) (T.map pp ctxt);
    ] (Some r)

let symb_eval_stateful_app (g: env) (ctxt: slprop) (t: term) : T.Tac R.term =
  let t, ty = tc_term_phase1 g t false in
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
    let (| post, _ |) = Pulse.Checker.Prover.normalize_slprop g' post true in 
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
    let b_ty, b_u = tc_term_phase1 g b_ty false in
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
    let b_ty, b_u = tc_term_phase1 g b_ty false in
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

let tc_term_phase1_with_type_twice g t must_tot ty =
  // If we call phase1 TC only once, then the universe instantiation in
  // coercion-inserted reveal calls remains a uvar.
  let t = tc_term_phase1_with_type g t must_tot ty in
  let t = tc_term_phase1_with_type g t must_tot ty in
  t

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
      let x_ty, x_u = tc_type_phase1 g b.binder_ty false in
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
      let p, _ = tc_type_phase1 g p false in
      let x_ty = mk_squash u0 p in
      let g' = push_binding g x (fst px) x_ty in
      let body = open_term_nv body px in
      let body = purify_spec_core g' ctxt (body :: ts) |> or_emp in
      let body = close_term body x in
      Some (tm_with_pure p n body)

    | _ ->
      let _, t = symb_eval_subterms g ctxt t in
      debug g (fun _ -> [text "purify spec atom 1"; pp t]);
      let t = tc_term_phase1_with_type_twice g t true tm_slprop in

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
      let p, _ = tc_type_phase1 g p false in
      let x_ty = mk_squash u0 p in
      let g' = push_binding g x (fst px) x_ty in
      let body = open_term_nv body px in
      let body = extrude g' ctxt (body::todo) ts |> or_emp in
      let body = close_term body x in
      Some (tm_with_pure p n body)

    | _ ->
      let ctxt = push_ctxt ctxt t in
      match extrude g ctxt todo ts with
      | None -> Some t
      | Some todo -> Some (tm_star t todo)

let purify_spec (g: env) (ctxt: ctxt) (t0: slprop) : T.Tac slprop =
  let t = t0 in
  let t = purify_spec_core g ctxt [t] |> or_emp in
  // If we call phase1 TC only once, then the universe instantiation in
  // op_Exists_Star can remain unresolved.
  let t = tc_term_phase1_with_type g t true tm_slprop in
  debug g (fun _ -> [ text "purified" ^/^ pp t0; text "to" ^/^ pp t ]);
  t

let purify_and_check_spec (g: env) (ctxt: ctxt) (t: slprop) =
  check_slprop g (purify_spec g ctxt t)