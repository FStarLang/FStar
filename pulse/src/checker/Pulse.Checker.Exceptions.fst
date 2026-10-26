module Pulse.Checker.Exceptions

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Base
open Pulse.Checker.Pure
open Pulse.Checker.Prover
module R = FStar.Reflection.V2
module RT = FStar.Reflection.Typing
module T = FStar.Tactics.V2
module U = Pulse.Reflection.Util

// Native exceptions use the two-exit representation from Effects.Rules.
// Exception labels are lexical, and lookup_goto adds precisely the cleanup
// obligations of scopes crossed on the way to the selected label.
let rules_name s = ["Pulse"; "Lib"; "Effects"; "Rules"; s]
let rules_term s = R.pack_ln (R.Tv_FVar (R.pack_fv (rules_name s)))
let explicit t = t, R.Q_Explicit
let implicit t = t, R.Q_Implicit
let outcome_type exn a =
  R.mk_app (rules_term "native_outcome") [explicit exn; explicit a]
let constructor name exn a x =
  R.mk_app (rules_term name) [implicit exn; implicit a; explicit x]
let bv0 = tm_bvar { bv_index=0; bv_ppname=ppname_default }

let outcome_types (ty:term) : option (term & term) =
  let h, args = R.collect_app_ln ty in
  let is_outcome =
    match R.inspect_ln h with
    | R.Tv_FVar fv | R.Tv_UInst fv _ -> R.inspect_fv fv = rules_name "native_outcome"
    | _ -> false
  in
  if is_outcome then
    match args with
    | [(exn, _); (a, _)] -> Some (exn, a)
    | _ -> None
  else None

let require_stateful (g:env) (ph:post_hint_opt g) (rng:range) : T.Tac unit =
  match ambient_effect_annot g ph with
  | EffectAnnotSTT | EffectAnnotSTTDiv -> ()
  | _ -> fail g (Some rng) "Exceptions are not allowed in ghost or atomic computations"

let ret (rng:range) (ty x:term) =
  mk_term (Tm_Return { expected_type=ty; insert_eq=false; term=x }) rng

let check_raise (g:env) (pre:term) (ph:post_hint_opt g)
  (name:ppname) (arg:term) (rng:range)
  : T.Tac (checker_result_t g pre ph) =
  require_stateful g ph rng;
  match exception_label (bindings g) with
  | Some (lbl, x) ->
    (match lookup_goto g x with
    | Some (_, c) ->
      (match outcome_types (comp_res c) with
      | Some (exn, a) ->
        let arg = check_tot_term g arg exn in
        let t = mk_term (Tm_Goto {
          lbl=term_of_nvar (lbl, x); arg=constructor "Raised" exn a arg }) rng in
        Pulse.Checker.Goto.check g pre ph name t
      | None -> fail g (Some rng) "Internal error: exception label has no outcome type")
    | None -> fail g (Some rng) "Internal error: missing exception label")
  | None ->
    // A fully handled try has an unreachable default branch. Discharge it
    // from False; never silently discard an actually unhandled exception.
    let proof = check_tot_term g unit_const (U.mk_squash tm_l_false) in
    let call = R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv (U.mk_pulse_lib_core_lid "unreachable"))))
      [explicit proof] in
    let c = C_STGhost tm_emp_inames { u=u0; res=tm_unit; pre=tm_emp; post=tm_is_unreachable } in
    let t = wrst c (Tm_ST { t=call; args=[] }) in
    prove_post_hint (try_frame_pre false #g (| t, c |) name) ph rng

let posts (g:env) (ph:post_hint_opt g) (normal:comp_st) (exceptional:term) (rng:range)
  : T.Tac (post_hint_for_env g & post_hint_for_env g & term) =
  require_stateful g ph rng;
  let eff = ambient_effect_annot g ph in
  let normal = intro_post_hint g eff (Some (comp_res normal)) (comp_post normal) in
  let (| exceptional, ty |) = compute_tot_term_type g exceptional in
  let exn =
    match R.inspect_ln ty with
    | R.Tv_Arrow b _ -> (R.inspect_binder b).sort
    | _ -> fail g (Some rng) "raises expects a function from exception payloads to slprop"
  in
  let exceptional = check_tot_term g exceptional (U.mk_arrow (exn, R.Q_Explicit) tm_slprop) in
  let u = check_universe g exn in
  if not (eq_univ u u0 && eq_univ normal.u u0) then
    fail g (Some rng) "Exception payloads and results must be in Type0";
  let q = U.mk_abs normal.ret_ty R.Q_Explicit normal.post in
  let post = R.mk_app (rules_term "exit_post")
    [implicit exn; implicit normal.ret_ty; explicit q; explicit exceptional; explicit bv0] in
  let outer = intro_post_hint g eff (Some (outcome_type exn normal.ret_ty)) post in
  normal, outer, exn

let check_scope (g:env) (pre:term) (ph:post_hint_opt g) (name:ppname)
  (normal:comp_st) (exceptional:term) (body:st_term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  let normal, outer, exn = posts g ph normal exceptional rng in
  let c = Pulse.Typing.Combinators.comp_for_post_hint g pre outer (fresh g) in
  let lbl = mk_ppname_no_range "_exception" in
  let x = fresh g in
  let g' = push_exception g x lbl (goto_comp_of_block_comp c) in
  let r = check g' pre (PostHint normal) name body in
  let r = retype_checker_result NoHint r in
  let (| y, g1, _, ctxt, _ |) = r in
  assert (g' `env_extends` g);
  env_extends_trans g1 g' g;
  env_extends_trans g1 g outer.g;
  let value = constructor "Normal" exn normal.ret_ty (term_of_nvar (name, y)) in
  let r1 = check g1 ctxt (PostHint outer) name (ret rng outer.ret_ty value) in
  let r = compose_checker_result_t r r1 in
  let (| body, c |) = apply_checker_result_k r name in
  let t = wrst c (Tm_ForwardJumpLabel { lbl; body=close_st_term body x; post=c }) in
  let c = match_comp_res_with_post_hint t c ph in
  prove_post_hint (checker_result_for_st_typing (| t, c |) name) ph rng

let outcome_branch (ctor:string) (body:st_term) : branch =
  { pat=Pat_Cons (as_fv (rules_name ctor)) [Pat_Var ppname_default.name (FStar.Sealed.seal tm_unknown), false];
    e=body; norw=false }

// Split an already checked call's result. Only the Normal branch supplies the
// ordinary continuation; the Raised branch transfers its framed resources to
// the nearest lexical exception exit.
let unwrap (#g:env) (#pre:term) (ph:post_hint_opt g) (name:ppname)
  (r:checker_result_t g pre NoHint) (exn a post:term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  require_stateful g ph rng;
  let normal_post = open_term' post (constructor "Normal" exn a bv0) 0 in
  let normal = intro_post_hint g (ambient_effect_annot g ph) (Some a) normal_post in
  let (| x, g1, (_, ty), ctxt, _ |) = r in
  env_extends_trans g1 g normal.g;
  let branches = [
    outcome_branch "Normal" (ret rng a bv0);
    outcome_branch "Raised" (mk_term (Tm_Raise {arg=bv0}) rng)
  ] in
  let r1 = Pulse.Checker.Match.check g1 ctxt normal name
    (ret rng ty (term_of_nvar (name, x))) branches check in
  let r = compose_checker_result_t r r1 in
  prove_post_hint (retype_checker_result NoHint r) ph rng

let check_try (g:env) (pre:term) (ph:post_hint_opt g) (name:ppname)
  (normal:comp_st) (exceptional:term) (body handler:st_term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  let normal_post, _, _ = posts g ph normal exceptional rng in
  let r = check_scope g pre NoHint name normal exceptional body rng check in
  let (| x, g1, (_, ty), ctxt, _ |) = r in
  env_extends_trans g1 g normal_post.g;
  let branches = [
    outcome_branch "Normal" (ret rng normal_post.ret_ty bv0);
    outcome_branch "Raised" handler
  ] in
  let r1 = Pulse.Checker.Match.check g1 ctxt normal_post name
    (ret rng ty (term_of_nvar (name, x))) branches check in
  let r = compose_checker_result_t r r1 in
  prove_post_hint (retype_checker_result NoHint r) ph rng
