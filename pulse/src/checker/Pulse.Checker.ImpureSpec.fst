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
open Pulse.Typing
module R = FStar.Reflection.V2
module T = FStar.Tactics.V2
module RU = Pulse.RuntimeUtils
module RT = FStar.Reflection.Typing
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

(* ------------------------------------------------------------------------ *)
(* Opening the branches of a `match` occurring in a spec.

   A spec-level pattern-`let` (`let (a, b) = e in ...`) desugars to a
   single-branch `match`, and specs emitted by transpilers routinely put their
   whole `requires` under one to destructure an `erased` witness. The
   pattern-`let` is not replaceable by `fst`/`snd` there: the caller has to
   solve the witness by unification, and `pts_to x (fst ?w)` is inert because
   F* does not reduce projectors.

   Unlike the `Tv_Let` case below, we cannot inline by substitution (that
   would reintroduce exactly those projectors), so we open the pattern's
   binders as fresh bindings, recurse, and close back up — as the `Tv_Abs`
   and `Tv_Refine` cases do.

   We deliberately do not reuse `FStar.Tactics.NamedView.open_branch`: it
   allocates binders with the global `fresh ()` counter, which can collide
   with the env-derived variables Pulse allocates with `fresh g`. *)

(* The opening substitution for a list of terms given left to right: de Bruijn
   index 0 refers to the *last* one, as in `FStar.Tactics.NamedView.open_pat`
   (which pushes `DB 0 nv` and shifts the rest) and in `open_st_term_bs` in
   Pulse.Checker.Match. *)
let db_opening (ts: list term) : subst =
  let rec aux (ts: list term) (i:nat) : Tot subst (decreases ts) =
    match ts with
    | [] -> []
    | t::ts -> RT.DT i t :: aux ts (i+1)
  in
  aux (List.Tot.rev ts) 0

let pat_opening (bs: list (nvar & typ)) : subst =
  db_opening (List.Tot.map (fun (nv, _) -> term_of_nvar nv) bs)

(* The head fv of a (possibly universe-instantiated) term. *)
let un_uinst_fv (t: R.term) : option R.fv =
  match R.inspect_ln t with
  | R.Tv_FVar fv
  | R.Tv_UInst fv _ -> Some fv
  | _ -> None

(* The inductive a type belongs to: its parameter binders and its
   constructors, looked up from the head of the type. *)
let inductive_of_ty (g: env) (ty: typ) : T.Tac (option (list R.binder & list (R.name & typ))) =
  let hd, _ = T.collect_app_ln ty in
  match un_uinst_fv hd with
  | None -> None
  | Some ind -> (
    match R.lookup_typ (fstar_env g) (R.inspect_fv ind) with
    | None -> None
    | Some se -> (
      match R.inspect_sigelt se with
      | R.Sg_Inductive _ _ params _ cts -> Some (params, cts)
      | _ -> None
    )
  )

(* Collect the variables bound by a pattern, left to right, pushing each into
   the environment. Also returns the term the pattern elaborates to (which is
   what its siblings' types are stated in terms of), and whether the pattern
   is irrefutable, i.e. guaranteed to match: a constructor pattern is when its
   inductive has a single constructor (tuples and records, which is what a
   pattern-`let` produces) and all its sub-patterns are.

   The type of each binder is computed here rather than taken from the
   `Pat_Var`'s own sealed sort, or from the parameters recorded in the
   `Pat_Dot_Term`s: purification runs *before* the spec is typechecked, so
   both are typically still `Tv_Unknown` at this point, and pushing that into
   the environment blows up later in the unifier. Instead the constructor's
   declared type is instantiated with the arguments of the scrutinee's *type*
   for the inductive's parameters, and with the terms elaborated from the
   preceding sub-patterns for the rest. Mirrors
   `FStar.Reflection.Typing.elaborate_pat`, but produces the bindings rather
   than consuming them.

   Fails (via `T.fail`) if the shapes do not line up, e.g. for an inductive
   with indices; callers treat that as "do not descend into this match". *)
let rec pat_bindings_ty (g: env) (p: R.pattern) (ty: typ) (bs: list (nvar & typ))
  : T.Tac (env & list (nvar & typ) & term & bool)
= match p with
  | R.Pat_Constant c -> g, bs, R.pack_ln (R.Tv_Const c), false
  | R.Pat_Dot_Term (Some t) -> g, bs, subst_term t (pat_opening bs), true
  | R.Pat_Dot_Term None -> T.fail "pat_bindings_ty: dot pattern with no term"
  | R.Pat_Var _ ppname ->
    let x = fresh g in
    let n = mk_ppname_no_range (T.unseal ppname) in
    let g = push_binding g x n ty in
    let bs = bs @ [((n, x), ty)] in
    g, bs, term_of_nvar (n, x), true

  | R.Pat_Cons fv us subpats ->
    let params, cts =
      match inductive_of_ty g ty with
      | Some r -> r
      | None -> T.fail "pat_bindings_ty: scrutinee is not of inductive type"
    in
    let cty =
      match List.Tot.find (fun (nm, _) -> nm = R.inspect_fv fv) cts with
      | Some (_, cty) -> cty
      | None -> T.fail "pat_bindings_ty: constructor not found in its inductive"
    in
    let np = List.Tot.length params in
    let _, ty_args = T.collect_app_ln ty in
    if List.Tot.length ty_args < np then
      T.fail "pat_bindings_ty: scrutinee type has too few arguments";
    let param_args = List.Tot.map fst (fst (List.Tot.splitAt np ty_args)) in
    let cbs, _ = R.collect_arr_ln_bs cty in
    let nsub = List.Tot.length subpats in
    (* Line the constructor's binders up with the sub-patterns. The
       constructor's declared type may or may not repeat the inductive's
       parameters, and the sub-patterns may or may not carry a dot pattern per
       parameter (they do not yet, at the point purification runs). Whichever
       way, the parameters' values are read off the scrutinee's *type*, and
       `args` is primed with them because that is the de Bruijn context the
       remaining binders' sorts live in. *)
    let ncb = List.Tot.length cbs in
    let params_of_ty = List.Tot.map (fun a -> (a, R.Q_Implicit)) param_args in
    let cbs, params_todo, args0 =
      if ncb = nsub + np then
        (* parameters are binders of `cty`, but not sub-patterns *)
        snd (List.Tot.splitAt np cbs), [], params_of_ty
      else if ncb = nsub then
        (* parameters are neither *)
        cbs, [], params_of_ty
      else if ncb + np = nsub then
        (* parameters are sub-patterns (dot patterns), but not binders *)
        params @ cbs, param_args, []
      else
        T.fail "pat_bindings_ty: constructor arity mismatch"
    in
    let ctor = R.pack_ln (match us with
                          | Some us -> R.Tv_UInst fv us
                          | None -> R.Tv_FVar fv) in
    let g, bs, _, _, args, irref =
      T.fold_left
        (fun (g, bs, cbs, params, args, irref) (sp, _) ->
          match cbs with
          | [] -> g, bs, [], params, args, irref
          | cb::cbs ->
            let cb = R.inspect_binder cb in
            let q = match cb.qual with
                    | R.Q_Meta _ -> R.Q_Implicit
                    | q -> q in
            match params with
            | par::params ->
              (* An inductive parameter: its value is fixed by the scrutinee's
                 type, and the corresponding sub-pattern is a dot pattern. *)
              g, bs, cbs, params, args @ [(par, q)], irref
            | [] ->
              (* `cb`'s sort lives in the context of the preceding constructor
                 arguments, so instantiate it with the arguments seen so far. *)
              let cb_ty = subst_term cb.sort (db_opening (List.Tot.map fst args)) in
              let g, bs, a, irref' = pat_bindings_ty g sp cb_ty bs in
              g, bs, cbs, [], args @ [(a, q)], irref && irref')
        (g, bs, cbs, params_todo, args0, List.Tot.length cts = 1) subpats
    in
    g, bs, RU.mk_app_flat ctor args FStar.Range.range_0, irref

(* Returns `None` if the scrutinee or the pattern cannot be handled here, in
   which case the caller leaves the match alone rather than descending. The
   boolean says whether the pattern is irrefutable. *)
let pat_bindings (g: env) (sc: term) (p: R.pattern)
  : T.Tac (option (env & list (nvar & typ) & bool))
= let go () : T.Tac (env & list (nvar & typ) & bool) =
    (* `tc_term_phase1`, not `T.tc`: purification runs before the spec is
       elaborated, so the scrutinee may still carry unresolved implicits. *)
    let _, sc_ty, _ = tc_term_phase1 g sc in
    let g, bs, _, irref = pat_bindings_ty g p sc_ty [] in
    g, bs, irref
  in
  match T.catch go with
  | FStar.Pervasives.Inl _ -> None
  | FStar.Pervasives.Inr r -> Some r

let open_branch_body (bs: list (nvar & typ)) (body: term) : term =
  subst_term body (pat_opening bs)

let close_branch_body (bs: list (nvar & typ)) (body: term) : term =
  close_term_n body (List.Tot.map (fun ((_, x), _) -> x) bs)

(* ------------------------------------------------------------------------ *)


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

let is_no_proof_app (g: env) (t: term) : T.Tac bool =
  Pulse.Reflection.Util.head_has_attr_string "Pulse.Lib.Core.pulse_impure_spec_no_proof_required" t

let symb_eval_stateful_app (g: env) (ctxt: slprop) (t: term) : T.Tac R.term =
  let t, ty, _ = tc_term_phase1 g t in
  debug g (fun _ -> [ text "impure spec inferred type"; pp t; pp ty ]);
  match readback_comp ty with
  | None | Some (C_Tot ..) ->
    T.fail_doc_at [text "Impossible: not a stateful application type"; fquotes (pp ty)] (Some (RU.range_of_term t))
  | Some c -> match c with
  | C_STAtomic _ _ { pre; post } | C_STGhost _ { pre; post } | C_ST { pre; post } | C_STDiv { pre; post } ->
    let x = fresh g in
    let x_ppn = mk_ppname_no_range "result" in
    let g' = push_binding g x (mk_ppname_no_range "result") ty in
    let post = open_term_nv post (x_ppn, x) in
    let post = normalize_slprop g' post true in 
    match get_rewrites_to_from_post g x post with
    | None ->
      let head, _ = T.collect_app_ln t in
      T.fail_doc_at [
        text "Cannot use" ^/^ fquotes (pp head) ^/^ text "in impure spec, cannot find rewrites_to in post:";
        fquotes (pp post);
      ] (Some (RU.range_of_term t))
    | Some rwr ->
      let allow_amb = true in
      (if not (is_no_proof_app g t) then prove g pre ctxt (RU.range_of_term t));
      debug g (fun _ -> [text "evaluated" ^/^ pp t ^/^ text "to" ^/^ pp rwr]);
      let rwr = RU.deep_compress rwr in // TODO: maybe this fails on uvars...
      rwr

noeq type ctxt' = {
  ctxt: ctxt;
  in_old: in_old:bool { in_old ==> Some? ctxt.ctxt_old };
}

let cur_ctxt c =
  if c.in_old then Some?.v c.ctxt.ctxt_old else c.ctxt.ctxt_now

let rec symb_eval_subterms (g:env) (ctxt: ctxt') (t:R.term) : T.Tac (bool & R.term) = 
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

  | R.Tv_Let recf attrs b def body ->
    (* A `let p = def in body` occurring in a spec (e.g. `let p = x in
       exists* v. pts_to p #1.0R v ** observe (!p)`, issue #4421). Without
       this case the `let` was left completely unprocessed by the fallback
       branch below (it is not an application), so any stateful read (e.g.
       `!p`) nested in its body was never rewritten to its pure result. *)
    debug g (fun _ -> [text "symb eval subterms let 0"; pp t]);
    let changed_def, def = symb_eval_subterms g ctxt def in
    let b = R.inspect_binder b in
    let x = fresh g in
    let ppname = mk_ppname_no_range (T.unseal b.ppname) in
    let changed1, b_ty = symb_eval_subterms g ctxt b.sort in
    let b_ty, b_u = tc_type_phase1 g b_ty in
    debug g (fun _ -> [text "symb eval subterms let 1"; pp changed1; pp b_ty]);
    let b = { b with sort = b_ty } in
    let g' = push_binding g x ppname b.sort in
    let body = open_term_nv body (ppname, x) in
    let changed2, body = symb_eval_subterms g' ctxt body in
    debug g (fun _ -> [text "symb eval subterms let 2"; pp changed2; pp body]);
    if changed_def || changed1 || changed2 then
      true, R.pack_ln (R.Tv_Let recf attrs (R.pack_binder b) def (close_term body x))
    else
      false, t

  | R.Tv_Match sc ret brs ->
    (* A `match` occurring in a spec, in practice a desugared pattern-`let`
       such as `let (a, b) = reveal w in ...`; a follow-up to the `let` case
       of #4421, which this generalizes. Previously only the
       scrutinee was traversed and the branches were passed through untouched,
       so a stateful read or a `rewrites_to` ghost call under a pattern-`let`
       was never elaborated away.

       All branches are traversed, whatever the shape of the match: this is an
       alpha-safe traversal, and each stateful application elaborated here has
       its precondition discharged against the ambient `ctxt`, which holds
       independently of which branch is taken. *)
    debug g (fun _ -> [text "symb eval subterms match 0"; pp t]);
    let changed_sc, sc = symb_eval_subterms g ctxt sc in
    let changed_brs, brs =
      T.fold_left
        (fun (changed, brs) (p, body) ->
          match pat_bindings g sc p with
          | None -> changed, (p, body) :: brs
          | Some (g', bs, _) ->
            let body = open_branch_body bs body in
            let changed', body = symb_eval_subterms g' ctxt body in
            changed || changed', (p, close_branch_body bs body) :: brs)
        (false, []) brs
    in
    let brs = List.Tot.rev brs in
    debug g (fun _ -> [text "symb eval subterms match 1"; pp (changed_sc || changed_brs)]);
    if changed_sc || changed_brs then
      true, R.pack_ln (R.Tv_Match sc ret brs)
    else
      false, t

  | _ ->
    let head, args = T.collect_app_ln t in
    let fallback () =
      let g, changed, args = symb_eval_subterms_args g ctxt args in
      match is_stateful_application g t with
      | Some _ ->
        let t = RU.mk_app_flat head args (T.range_of_term t) in
        let t' = symb_eval_stateful_app g (cur_ctxt ctxt) t in
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
        if not (Some? ctxt.ctxt.ctxt_old) then
          T.fail_doc_at [
            text "'old' can only be used in postconditions";
          ] (Some (RU.range_of_term t))
        else (
          (if ctxt.in_old then
            warn_doc g r [
              text "'old' only needs to be specified once";
            ]);
          symb_eval_subterms g { ctxt with in_old = true } t
        )
      else
        fallback ()
    | _ ->
      fallback ()

and symb_eval_subterms_args (g:env) (ctxt: ctxt') (args:list T.argv)
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
  let ctxt = normalize_slprop g ctxt true in
  let g', xs, ctxt = run_elim_core g (slprop_as_list ctxt) in
  g', xs, list_as_slprop ctxt

(* Adds add to the ctxt in a way that the prover will prefer it when ambiguous. *)
let push_ctxt (ctxt: ctxt') add =
  { ctxt with ctxt = { ctxt.ctxt with ctxt_now = tm_star add ctxt.ctxt.ctxt_now } }

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

(* Reflection helpers to descend into slprop-typed arguments of predicate
   combinators when purifying impure specs (issue #4347). These mirror the
   `type_of_fv`/`binder_is_pred` helpers in Pulse.Checker.Prover, which are
   not exported through its interface. *)

let type_of_fv (g:env) (fv:R.fv) : T.Tac (option R.term) =
  let n = R.inspect_fv fv in
  match R.lookup_typ (fstar_env g) n with
  | None -> None
  | Some se ->
    match R.inspect_sigelt se with
    | R.Unk -> None
    | R.Sg_Let _ lbs ->
      tryPick
        (fun lb ->
          let lbv = R.inspect_lb lb in
          if R.inspect_fv lbv.lb_fv = n then Some lbv.lb_typ else None)
        lbs
    | R.Sg_Val _ _ t -> Some t
    | R.Sg_Inductive _ _ _ _ _ -> None

(* If the binder's sort is `t1 -> ... -> tn -> slprop`, returns `Some [t1;
   ...; tn]` (the domain types of the predicate); `Some []` means the binder
   is itself an slprop. Returns `None` otherwise. Only whether the list is
   empty matters downstream: direct slprop arguments (`Some []`) are descended
   into, predicate arguments (`Some (_::_)`) are not. *)
let binder_is_pred (b:R.binder) : option (list R.term) =
  let doms, c = R.collect_arr_ln (R.inspect_binder b).sort in
  match R.inspect_comp c with
  | R.C_Total res | R.C_GTotal res ->
    if T.term_eq tm_slprop res then Some doms else None
  | _ -> None

let combinator_head_fv (t: term) : option R.fv =
  match R.inspect_ln t with
  | R.Tv_FVar fv
  | R.Tv_UInst fv _ -> Some fv
  | _ -> None

let is_explicit_aqual (q:R.aqualv) : bool =
  match q with
  | R.Q_Explicit -> true
  | _ -> false

let is_explicit_binder (b:R.binder) : bool =
  is_explicit_aqual (R.inspect_binder b).qual

(* Classify each applied argument by the corresponding binder of the head's
   type. The result list has the same length as `args`. Implicit arguments are
   never descended into (classified `None`); each explicit argument is matched
   with the next explicit binder of the head's type (implicit binders such as
   `#p` are skipped, so a `#p:slprop` type parameter is not mistaken for a
   descendable slprop argument). Extra explicit arguments with no matching
   binder are classified as `None`. *)
let rec align_preds (bs_exp: list R.binder) (args: list T.argv) : list (option (list R.term)) =
  match args with
  | [] -> []
  | (_, q) :: args' ->
    if is_explicit_aqual q then
      match bs_exp with
      | [] -> None :: align_preds [] args'
      | b :: bs_exp' -> binder_is_pred b :: align_preds bs_exp' args'
    else
      None :: align_preds bs_exp args'

(* Returns the per-argument classification when `head` is a pure combinator
   (a total function returning an slprop) with at least one slprop/predicate
   argument. Structural slprop connectives are excluded, so they keep their
   existing handling. Returns `None` (meaning: do not descend) otherwise. *)
let combinator_arg_preds (g:env) (head: term) (args: list T.argv)
  : T.Tac (option (list (option (list R.term))))
= match combinator_head_fv head with
  | None -> None
  | Some fv ->
    let n = R.inspect_fv fv in
    if n = forall_lid || n = exists_lid || n = star_lid || n = with_pure_lid then
      None
    else (
      match type_of_fv g fv with
      | None -> None
      | Some ty ->
        let bs, _ = R.collect_arr_ln_bs ty in
        let bs_exp = filter is_explicit_binder bs in
        let preds = align_preds bs_exp args in
        if existsb Some? preds then Some preds else None
    )

let rec purify_spec_core (g: env) (ctxt: ctxt') (ts: list slprop) : T.Tac (option slprop) =
  match ts with
  | [] -> None
  | t::ts ->
    match R.inspect_ln t with
    | R.Tv_Let false _ _ def body ->
      (* Issue #4421: a spec-level `let p = def in body` (e.g. `let p = x in
         exists* v. pts_to p #1.0R v ** observe (!p)`) is a pure alias, not
         an effectful binding. Inline it by substituting `def` for the
         let-bound variable in `body` (rather than opening `body` with a
         fresh, unrelated variable), so that any slprop structure
         (`exists*`, `**`, etc.) nested inside becomes visible to the same
         splitting logic below, exactly as if `p` had been written as `def`
         directly. Recursive lets fall through to the generic atom handling
         below instead. *)
      let _, def = symb_eval_subterms g ctxt def in
      let body = open_term' body def 0 in
      purify_spec_core g ctxt (body :: ts)

    | R.Tv_Match sc ret [(p, body)] ->
      (
      (* A spec that *is* a pattern-`let`, i.e. a single-branch match on an
         irrefutable pattern; the slprop-level counterpart of the `Tv_Match`
         case in `symb_eval_subterms`, and a follow-up to the `let` case of
         #4421 just above. Without this case the whole match
         was treated as one opaque atom, so its conjuncts were never split
         and the resources inside it were never extruded into the context —
         which is what makes a `!r` or a `rewrites_to` ghost call under a
         pattern-`let` fail to elaborate.

         Unlike the `let` case above we cannot inline by substitution: that
         would replace the pattern binders by `fst`/`snd` projections, which
         F* does not reduce and which therefore cannot be solved by
         unification at the call site. So we open the pattern's binders and
         recurse under them, pushing the remaining conjuncts `ts` inside the
         branch exactly as the `exists*` and `with_pure` cases below do.

         This is sound because a single irrefutable branch always matches:
         `match e with | p -> A` is `A[e/p]`, hence
         `(match e with | p -> A) ** B == match e with | p -> (A ** B)`.
         Anything extruded into `ctxt` inside the branch stays inside the
         recursive call, since `ctxt` is passed by value.

         Multi-branch and refutable matches are deliberately *not* split
         here: each branch's conjuncts would have to be justified under that
         branch's hypothesis, which this pass has no access to. They fall
         through to the opaque-atom path below, as before. *)
      let _, sc = symb_eval_subterms g ctxt sc in
      match pat_bindings g sc p with
      | Some (g', bs, true) ->
        let body = open_branch_body bs body in
        let body = purify_spec_core g' ctxt (body :: ts) |> or_emp in
        let body = close_branch_body bs body in
        Some (R.pack_ln (R.Tv_Match sc ret [(p, body)]))
      | _ -> purify_spec_default g ctxt t ts
      )

    | _ -> purify_spec_default g ctxt t ts

and purify_spec_default (g: env) (ctxt: ctxt') (t: slprop) (ts: list slprop) : T.Tac (option slprop) =
    match inspect_ast_term t with
    | Tm_Star t s ->
      purify_spec_core g ctxt (t::s::ts)

    | Tm_ExistsSL _ b body ->
      let x = fresh g in
      let px = b.binder_ppname, x in
      let _, x_ty = symb_eval_subterms g ctxt b.binder_ty in
      let x_ty, x_u = tc_type_phase1 g x_ty in
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
      let p, _ = tc_term_phase1_with_type g p tm_prop in
      let x_ty = mk_squash p in
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
      let t = purify_combinator g ctxt t in
      debug g (fun _ -> [text "purify spec atom 1"; pp t]);
      let t, _ = tc_term_phase1_with_type_twice g t tm_slprop in

      let steps = [unascribe; primops; iota; delta_attr ["Pulse.Lib.Core.pulse_eager_unfold"]] in
      let t = T.norm_term_env (elab_env g) steps t in
      extrude g ctxt [t] ts

(* Purify a spec atom, descending with the full purification machinery into
   the slprop-typed arguments of a predicate combinator (issue #4347). This
   makes sibling resources inside a combinator argument (e.g. the `pts_to`
   next to a `!r` in `id_wrap (pts_to r v ** p_pred (!r))`) available when
   evaluating stateful reads. Falls back to `symb_eval_subterms` when `t` is
   not such a combinator application. *)
and purify_combinator (g: env) (ctxt: ctxt') (t: term) : T.Tac term =
  let head, args = T.collect_app_ln t in
  match combinator_arg_preds g head args with
  | None -> snd (symb_eval_subterms g ctxt t)
  | Some preds ->
    let args = purify_args g ctxt args preds in
    RU.mk_app_flat head args (T.range_of_term t)

and purify_args (g: env) (ctxt: ctxt') (args: list T.argv) (preds: list (option (list R.term)))
  : T.Tac (list T.argv)
= match args, preds with
  | (a, q)::args', pred::preds' ->
    let a =
      match pred with
      | Some [] ->
        (* Direct slprop argument: descend and purify (issue #4347) so nested
           stars/existentials are normalized and sibling resources become
           available to stateful reads inside the argument (e.g. the `pts_to`
           next to a `!r` in `id_wrap (pts_to r v ** p_pred (!r))`). *)
        purify_spec_core g ctxt [a] |> or_emp
      | Some (_::_) ->
        (* Predicate-abstraction argument (`fun x -> ...`): do NOT descend
           under the lambda. Re-elaborating a predicate body is error-prone
           (it can trip pre-existing typechecker issues with unannotated
           binders or tuple projections, e.g. `forall+ (xy:a&b). f xy._1
           xy._2`), so predicate arguments keep their existing handling. *)
        snd (symb_eval_subterms g ctxt a)
      | None -> snd (symb_eval_subterms g ctxt a)
    in
    (a, q) :: purify_args g ctxt args' preds'
  | _, _ -> args

and extrude (g: env) (ctxt: ctxt') (todo: list slprop) (ts: list slprop) : T.Tac (option slprop) =
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
      let p, _ = tc_term_phase1_with_type g p tm_prop in
      let x_ty = mk_squash p in
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
  let ctxt = { ctxt; in_old = false } in
  let _, t = symb_eval_subterms g ctxt t in
  t

let purify_spec (g: env) (ctxt: ctxt) (t0: slprop) : T.Tac slprop =
  let t = t0 in
  let g', xs, ctxt = run_elim_ctxt g ctxt in
  let ctxt = { ctxt; in_old = false } in
  let t = purify_spec_core g' ctxt [t] |> or_emp in
  // TODO: check that xs is not free in t
  // If we call phase1 TC only once, then the universe instantiation in
  // op_Exists_Star can remain unresolved.
  let t, _ = tc_term_phase1_with_type g t tm_slprop in
  debug g (fun _ -> [ text "purified" ^/^ pp t0; text "to" ^/^ pp t ]);
  t

let purify_and_check_spec (g: env) (ctxt: ctxt) (t: slprop) =
  // purify_spec already elaborates the term via tc_term_phase1_with_type,
  // so we only need the core checker for validation (skip instantiate_term_implicits)
  let t = purify_spec g ctxt t in
  check_slprop_with_core g t;
  t