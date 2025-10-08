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

module Pulse.Checker.AssertWithBinders

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Checker.ImpureSpec
open Pulse.Elaborate.Pure
open Pulse.Typing.Env

module L = FStar.List.Tot
module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module PC = Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module PS = Pulse.Checker.Prover.Substs
module Prover = Pulse.Checker.Prover
open Pulse.Checker.Prover.Normalize
module Env = Pulse.Typing.Env
open Pulse.Show
module RU = Pulse.RuntimeUtils

let is_host_term (t:R.term) = not (R.Tv_Unknown? (R.inspect_ln t))

let debug_log = Pulse.Typing.debug_log "with_binders"

let rec open_binders_with_uvars (g:env) (bs:list binder) (v:term) (body:st_term) (us: list term)
  : T.Tac (uvs: list term & term & st_term) =

  match bs with
  | [] -> (| List.rev us, v, body |)
  | {binder_ty}::bs ->
    let binder_ty, _ = PC.tc_type_phase1 g binder_ty in
    let u, _ = PC.tc_term_phase1_with_type g tm_unknown binder_ty in
    let ss = [ RT.DT 0 u ] in
    let bs = L.mapi (fun i b ->
      assume (i >= 0);
      subst_binder b (shift_subst_n i ss)) bs in
    let v = subst_term v (shift_subst_n (L.length bs) ss) in
    let body = subst_st_term body (shift_subst_n (L.length bs) ss) in
    open_binders_with_uvars g bs v body (u::us)

let unfold_all (g : env) (names : list string) (t:term)
  : T.Tac term
  = let rg = elab_env g in
    let t = T.norm_term_env rg [primops; iota; delta_only names] t in
    t

(* unused *)
let def_of_fv (g:T.env) (fv:R.fv)
  : T.Tac (option R.term)
  = let n = R.inspect_fv fv in
    match R.lookup_typ g n with
    | None -> None
    | Some se ->
      match R.inspect_sigelt se with
      | R.Unk -> None
      | R.Sg_Let _ lbs -> (
        L.tryPick
          (fun lb ->
            let lbv = R.inspect_lb lb in
            if R.inspect_fv lbv.lb_fv = n
            then Some lbv.lb_def
            else None)
          lbs
      )
      | R.Sg_Val _ _ t -> Some t
      | R.Sg_Inductive _nm _univs params typ _ -> None

let unfold_head (g : env) (t:term)
  : T.Tac (term & string)
  = let rg = elab_env g in
    match T.hua t with
    | Some (fv, u, args) -> (
      (* zeta to allow unfolding recursive definitions. Should be only once
      unless it appears on the head of its own definition.. which should be impossible? *)
      let head_symbol = T.implode_qn (T.inspect_fv fv) in
      let t = T.norm_term_env rg [hnf; zeta; delta_only [head_symbol]] t in
      t, head_symbol
      (* Something like this would be better, but we need to instantiate
         the universes, and we don't have a good way to do that yet.
      match def_of_fv rg fv with
      | None ->
        fail g (Some (RU.range_of_term t))
          (Printf.sprintf "Cannot unfold %s, the head is not a defined symbol" (show t))

      | Some (us, fv_def) ->
          let tm = T.mk_app fv_def args in
          T.norm_term_env rg [hnf] tm
    *)
    )
    | None ->
      fail g (Some (RU.range_of_term t))
        (Printf.sprintf "Cannot unfold %s, the head is not an fvar" (T.term_to_string t))

let unfold_defs' (g:env) (defs:option (list string)) (t:term)
  : T.Tac (term & string)
  = let t, head_sym = unfold_head g t in
    let t =
      match defs with
      | None -> t
      | Some defs -> unfold_all g defs t
    in
    let t = T.norm_term_env (elab_env g) [hnf; iota; primops] t in
    t, head_sym

let unfold_defs (g:env) (defs:option (list string)) (t:term)
: T.Tac (term & string)
= RU.profile (fun () -> unfold_defs' g defs t) 
             (T.moduleof (fstar_env g))
            "Pulse.Checker.Unfold"

let check_unfoldable g (v:term) : T.Tac unit =
  match inspect_term v with
  | Tm_FStar _ -> ()
  | _ -> 
   fail g 
      (Some (Pulse.RuntimeUtils.range_of_term v))
      (Printf.sprintf "`fold` and `unfold` expect a single user-defined predicate as an argument, \
                        but %s is a primitive term that cannot be folded or unfolded"
                        (P.term_to_string v))

let warn_nop (g:env) (goal:term) : T.Tac unit =
  let open Pulse.PP in
  warn_doc g None [
    text "No rewrites performed.";
    text "Rewriting in: " ^^
      indent (pp <| canon_slprop_print goal);
  ]

let visit_and_rewrite (p: (R.term & R.term)) (t:term) : T.Tac term =
  let open FStar.Reflection.TermEq in
  let lhs, rhs = p in
  let visitor (t:R.term) : T.Tac R.term =
    if term_eq t lhs then rhs else t
  in
  match R.inspect_ln lhs with
  | R.Tv_Var n -> (
    let nv = R.inspect_namedv n in
    assume (is_host_term rhs);
    subst_term t [RT.NT nv.uniq (wr rhs (Pulse.RuntimeUtils.range_of_term t))]
    ) 
  | _ -> FStar.Tactics.Visit.visit_tm visitor t
    
let visit_and_rewrite_conjuncts (p: (R.term & R.term)) (tms:list term) : T.Tac (list term) =
  T.map (visit_and_rewrite p) tms

let visit_and_rewrite_conjuncts_all (g:env) (p: list (R.term & R.term)) (goal:term) : T.Tac term =
  let tms = slprop_as_list goal in
  let tms' = T.fold_left (fun tms p -> visit_and_rewrite_conjuncts p tms) tms p in
  list_as_slprop tms'

let disjoint (dom:list var) (cod:Set.set var) =
  L.for_all (fun d -> not (Set.mem d cod)) dom

let rec as_subst (p : list (term & term)) 
                 (out:list subst_elt)
                 (domain:list var)
                 (codomain:Set.set var)
  : option (list subst_elt) =
  match p with
  | [] -> 
    if disjoint domain codomain
    then Some out
    else None
  | (e1, e2)::p -> (
    match R.inspect_ln e1 with
    | R.Tv_Var n -> (
      let nv = R.inspect_namedv n in
      as_subst p 
        (RT.NT nv.uniq e2::out) 
        (nv.uniq ::domain )
        (Set.union codomain (freevars e2))
    ) 
    | _ -> None
  )



let rewrite_all (is_source:bool) (g:env) (p: list (term & term)) (t:term) pre elaborated tac_opt : T.Tac (term & list (term & term)) =
  (* We only use the rewrites_to substitution if there is no tactic attached to the
  rewrite. Otherwise, tactics may become brittle as the goal is changed unexpectedly
  by other things in the context. See tests/Match.fst. *)
  let use_rwr = None? tac_opt in
  let norm (t:term) : T.Tac term = dfst <| normalize_slprop g t use_rwr in
  let t =
    let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t None true in
    let t = dfst <| normalize_slprop g t use_rwr in
    t
  in
  let maybe_purify t = if elaborated then t else purify_term g {ctxt_now=pre;ctxt_old=None} t in
  let elab_pair (lhs rhs : R.term) : T.Tac (R.term & R.term) =
    let lhs = maybe_purify lhs in
    let rhs = maybe_purify rhs in
    let lhs, lhs_typ = Pulse.Checker.Pure.instantiate_term_implicits g lhs None true in
    let rhs, rhs_typ = Pulse.Checker.Pure.instantiate_term_implicits g rhs (Some lhs_typ) true in
    let lhs = norm lhs in
    let rhs = norm rhs in
    lhs, rhs
  in
  let p : list (R.term & R.term) = T.map (fun (e1, e2) -> elab_pair e1 e2) p in
  match as_subst p [] [] Set.empty with
  | Some s ->
    let t' = subst_term t s in
    if is_source && eq_tm t t' then
      warn_nop g t;
    t', p
  | _ ->
    let rhs = visit_and_rewrite_conjuncts_all g p t in
    if is_source && eq_tm t rhs then
      warn_nop g t;
    debug_log g (fun _ -> Printf.sprintf "Rewrote %s to %s" (P.term_to_string t) (P.term_to_string rhs));
    rhs, p

open Pulse.PP
let check_equiv_with_tac (g:env) (rng:Range.range) (lhs rhs ty:term) (tac_tm:term)
: T.Tac (option T.issues)
= let g_env = elab_env g in
  match Pulse.Typing.Util.universe_of_now g_env ty with
  | None, issues ->
    fail_doc_with_subissues g (Some rng) issues [
      text "rewrite: could not determine the universe of";
      pp ty;
    ]
  | Some u, _ ->
    let goal = mk_squash u0 (RT.eq2 u ty lhs rhs) in
    let goal_typing 
      : my_erased (T.typing_token (elab_env g) goal (RT.E_Total, R.pack_ln (R.Tv_Type u0)))
      = magic()
    in
    let goal_typing_tok : squash (T.typing_token (elab_env g) goal (RT.E_Total, R.pack_ln (R.Tv_Type u0))) =
      match goal_typing with | E x -> ()
    in
    let res, issues = T.call_subtac_tm g_env tac_tm u0 goal in
    if None? res then Some issues else None

let check_equiv_maybe_tac (g:env) (rng:Range.range) (lhs rhs ty:term) (tac_opt:option term)
: T.Tac (option T.issues)
= match tac_opt with
  | None -> 
    let res, issues = 
      Pulse.Typing.Util.check_equiv_now (elab_env g) lhs rhs in
    if None? res then Some issues else None
  | Some tac_tm -> 
    check_equiv_with_tac g rng lhs rhs ty tac_tm

let check_pair (g:env) rng (lhs rhs:term) (tac_opt:option term) : T.Tac unit =
  let (| _, ty, _ |) = PC.core_compute_term_type g lhs in
  let (| _, _ |) = PC.core_check_term_at_type g rhs ty in
  let issues = check_equiv_maybe_tac g rng lhs rhs ty tac_opt in
  match issues with
  | Some issues -> 
    fail_doc_with_subissues g (Some rng) issues [
      text "rename: could not prove equality of";
      pp lhs;
      pp rhs;
    ]
  | _ ->
    ()

let rec check_pairs (g:env) rng (ps: list (term & term)) (tac_opt:option term) : T.Tac unit =
  match ps with
  | [] -> ()
  | (lhs,rhs)::ps -> check_pair g rng lhs rhs tac_opt; check_pairs g rng ps tac_opt

let check_renaming 
    (g:env)
    (pre:term)
    (pre_typing:tot_typing g pre tm_slprop)
    (post_hint:post_hint_opt g)
    (res_ppname:ppname)
    (st:st_term { 
        match st.term with
        | Tm_ProofHintWithBinders { hint_type = RENAME _ } -> true
        | _ -> false
    })
  (check:check_t)
: T.Tac (checker_result_t g pre post_hint)
= let Tm_ProofHintWithBinders ht = st.term in
  let { hint_type=RENAME { pairs; goal; tac_opt; elaborated }; binders=bs; t=body } = ht in
  match bs, goal with
  | _::_, None ->
   //if there are binders, we must have a goal
    fail g (Some st.range) "A renaming with binders must have a goal (with xs. rename ... in goal)"

  | _::_, Some goal -> 
   //rewrite it as
   // with bs. assert goal;
   // rename [pairs] in goal;
   // ...
   let body = {st with term = Tm_ProofHintWithBinders { ht with binders = [] };
                       source = Sealed.seal false; } in
   check g pre pre_typing post_hint res_ppname
   { st with
       term = Tm_ProofHintWithBinders { hint_type=ASSERT { p = goal; elaborated = true }; binders=bs; t=body };
       source = Sealed.seal false;
   }

  | [], None ->
    // if there is no goal, take the goal to be the full current pre
    let rhs, pairs = rewrite_all (T.unseal st.source) g pairs pre pre elaborated tac_opt in
    check_pairs g st.range pairs tac_opt;
    let h2: slprop_equiv g rhs pre = RU.magic () in
    let h1: tot_typing g rhs tm_slprop = RU.magic () in
    let (| x, g', ty, ctxt', k |) = check g rhs h1 post_hint res_ppname body in
    (| x, g', ty, ctxt', k_elab_equiv k h2 (VE_Refl _ _) |)

  | [], Some goal -> (
      let goal, _ = PC.instantiate_term_implicits g goal None false in
      let rhs, _ = rewrite_all (T.unseal st.source) g pairs goal pre elaborated tac_opt in
      let t = { st with term = Tm_Rewrite { t1 = goal; t2 = rhs; tac_opt; elaborated = true };
                        source = Sealed.seal false; } in
      check g pre pre_typing post_hint res_ppname
      { st with term = Tm_Bind { binder = as_binder tm_unit; head = t; body };
                source = Sealed.seal false;
      }
  )
#restart-solver
#push-options "--z3rlimit_factor 2 --fuel 0 --ifuel 1"
let check_wild
      (g:env)
      (pre:term)
      (st:st_term { head_wild st })
: T.Tac st_term
= let Tm_ProofHintWithBinders ht = st.term in
  let open Pulse.PP in
  let { binders=bs; t=body } = ht in
  match bs with
  | [] ->
    fail g (Some st.range) "A wildcard must have at least one binder"

  | _ ->
    let slprops = slprop_as_list pre in
    let ex, rest = List.Tot.partition (fun (v:slprop) ->
                                       let vv = inspect_term v in
                                       Tm_ExistsSL? vv) slprops in
    match ex with
    | []
    | _::_::_ ->
      fail_doc g (Some st.range) [
        text "Binding names with a wildcard requires exactly one existential quantifier in the goal.";
        text "The context was:" ^^
          indent (pp <| canon_slprop_print pre)
      ]

    | [ex] ->
      let k = List.Tot.length bs in
      let rec peel_binders (n:nat) (t:term) : T.Tac st_term =
        if n = 0
        then (
          let ex_body = t in
          { st with term = Tm_ProofHintWithBinders { ht with hint_type = ASSERT { p = ex_body; elaborated = true } }}
        )
        else (
          match inspect_term t with
          | Tm_ExistsSL u b body -> peel_binders (n-1) body
          | _ -> 
            fail_doc g (Some st.range) [
              text <| (Printf.sprintf "Expected an existential quantifier with at least %d binders; but only found %s with %d binders"
                  k (show ex) (k - n));
              text "The context was:" ^^
                indent (pp <| canon_slprop_print pre)
            ]
        )
      in
      peel_binders k ex
#pop-options

//
// v is a partially applied slprop with type t
// add uvars for the remaining arguments
//
let rec add_rem_uvs (g:env) (t:typ) (v:term)
  : T.Tac slprop =
  match is_arrow t with
  | None -> v
  | Some (b, qopt, c) ->
    let u, _ = PC.tc_term_phase1_with_type g tm_unknown b.binder_ty in
    let ct = open_comp' c u 0 in
    let v = tm_pureapp v qopt u in
    add_rem_uvs g (comp_res ct) v

#push-options "--fuel 0 --ifuel 0"
let check
  (g:env)
  (pre:term)
  (pre_typing:tot_typing g pre tm_slprop)
  (post_hint:post_hint_opt g)
  (res_ppname:ppname)
  (st:st_term { Tm_ProofHintWithBinders? st.term })
  (check:check_t)

  : T.Tac (checker_result_t g pre post_hint) =

  let g = push_context g "check_assert" st.range in

  let Tm_ProofHintWithBinders { hint_type; binders=bs; t=body } = st.term in
  allow_invert hint_type;
  match hint_type with
  | WILD ->
    let st = check_wild g pre st in
    check g pre pre_typing post_hint res_ppname st

  | SHOW_PROOF_STATE r ->
    let open FStar.Pprint in
    let open Pulse.PP in
    let msg = [
      text "Current context:" ^^
            indent (pp <| canon_slprop_print pre)
    ] in
    fail_doc_env true g (Some r) msg

  | RENAME {} ->
    check_renaming g pre pre_typing post_hint res_ppname st check

  | REWRITE { t1; t2; tac_opt; elaborated } -> (
    match bs with
    | [] -> 
      let t = { st with term = Tm_Rewrite { t1; t2; tac_opt; elaborated } } in
      check g pre pre_typing post_hint res_ppname 
          { st with term = Tm_Bind { binder = as_binder tm_unit; head = t; body } } 
    | _ ->
      let t = { st with term = Tm_Rewrite { t1; t2; tac_opt; elaborated } } in
      let body = { st with term = Tm_Bind { binder = as_binder tm_unit; head = t; body } } in
      let st = { st with term = Tm_ProofHintWithBinders { hint_type = ASSERT { p = t1; elaborated }; binders = bs; t = body } } in
      check g pre pre_typing post_hint res_ppname st
  )
  
  | ASSERT { p = v; elaborated } ->
    FStar.Tactics.BreakVC.break_vc(); // Some stabilization
    let (| uvs, v, body |) = open_binders_with_uvars g bs v body [] in
    let ctxt = Pulse.Checker.ImpureSpec.({ctxt_now = pre; ctxt_old = None}) in
    let v =
      if elaborated then
        fst (PC.tc_term_phase1_with_type g v tm_slprop)
      else
        ImpureSpec.purify_spec g ctxt v in
    let (| g1, pre', k_frame |) = Prover.prove st.range g pre v false in
    let v = RU.deep_compress_safe v in
    let body = body in // TODO compress
    let h: tot_typing g1 v tm_slprop = PC.core_check_term _ _ _ _ in
    let h: tot_typing g1 (tm_star v pre') tm_slprop = RU.magic () in // TODO: propagate through prover
    let (| x, x_ty, pre'', g2, k |) =
      check g1 (tm_star v pre') h post_hint res_ppname body in
    (| x, x_ty, pre'', g2, k_elab_trans k_frame k |)


  | UNFOLD { p=v }
  | FOLD { p=v } ->
    let (| uvs, v, body |) = open_binders_with_uvars g bs v body [] in

    check_unfoldable g v;

    let v = purify_term g { ctxt_now = pre; ctxt_old = None } v in
    let v =
      let v, t, _ = PC.tc_term_phase1 g v in
      add_rem_uvs g t v in

    let lhs, rhs =
      match hint_type with      
      | UNFOLD _ ->
        let rhs, head_sym = unfold_defs g None v in
        v, rhs
      | FOLD { names=ns } -> 
        let lhs, head_sym = unfold_defs g ns v in
        lhs, v
    in

    let (| g', pre_remaining, k |) = Prover.prove st.range g pre lhs false in

    let norm t = T.norm_term_env (elab_env g') [primops; iota] (RU.deep_compress_safe t) in
    // Clean up beta-redexes introduced by unification
    let rhs' = norm rhs in
    let v' = norm v in

    let _: tot_typing g v' tm_slprop = PC.check_slprop_with_core g v' in

    let h1: tot_typing g' (tm_star pre_remaining rhs') tm_slprop = RU.magic () in
    let h2: slprop_equiv g' (tm_star pre_remaining rhs') (tm_star lhs pre_remaining) = RU.magic () in

    let (| x, g'', ty, ctxt', k' |) =
      check g' (tm_star pre_remaining rhs') h1 post_hint res_ppname body in
    (| x, g'', ty, ctxt', k_elab_trans k (k_elab_equiv k' h2 (VE_Refl _ _)) |)
