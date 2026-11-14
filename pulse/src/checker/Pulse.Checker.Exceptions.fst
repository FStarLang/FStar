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

(* Native syntax is an elaboration of two-exit contracts, not a new computation
   effect or an invocation of the Effects tree interpreter:

     raises r  ==>  stt[_div] (native_outcome exn a) pre (exit_post q r)
     raise e   ==>  goto nearest_exception_label (Raised e)

   These are checking rules, not the runtime representation. A scope checks
   ordinary completion against q, checks its Normal wrapper, and binds the
   destination for Raised exits. A try checks an outcome match outside that
   destination. Calls returning native_outcome are split similarly, even when
   their result is discarded or there is no enclosing handler.

   Resource transfer is delegated to the existing checker: calls frame both
   outcomes, whereas Goto.check requires exact ownership for the destination
   and crossed cleanup scopes. Outcome construction uses ordinary syntax; the
   recursive checker callback and continuation elaborators check and compose
   it. Only after these obligations have succeeded do we retain the checked
   normal bodies and native raise/try nodes, discarding proof-only outcome
   wrappers and matches. See doc/ref/pulse_exceptions.md for both lowerings. *)
let rules_name s = ["Pulse"; "Lib"; "Effects"; "Rules"; s]
let rules_term s = R.pack_ln (R.Tv_FVar (R.pack_fv (rules_name s)))
let explicit t = t, R.Q_Explicit
let implicit t = t, R.Q_Implicit

// Keep the native_outcome alias in type position: Checker.ST uses its head as
// the opt-in to automatic propagation. Normal/Raised are constructors of the
// underlying outcome datatype, whose type parameters are implicit.
let outcome_type exn a =
  R.mk_app (rules_term "native_outcome") [explicit exn; explicit a]
let constructor name exn a x =
  R.mk_app (rules_term name) [implicit exn; implicit a; explicit x]
let bv0 = tm_bvar { bv_index=0; bv_ppname=ppname_default }

// Do not unfold aliases or test definitional equality here. Raw outcome values
// are data in the effects library and must NOT trigger native control flow.
// Readback may retain a universe instance on the head, hence both head forms.
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

// Termination is independent of raising. With no post hint, recover the ambient
// stateful effect from lexical labels; never silently permit ghost/atomic exits.
let require_stateful (g:env) (ph:post_hint_opt g) (rng:range) : T.Tac unit =
  match ambient_effect_annot g ph with
  | EffectAnnotSTT | EffectAnnotSTTDiv -> ()
  | _ -> fail g (Some rng) "Exceptions are not allowed in ghost or atomic computations"

let ret (rng:range) (ty x:term) =
  mk_term (Tm_Return { expected_type=ty; insert_eq=false; term=x }) rng

// The main checker's stateful-head pass has already evaluated/hoisted arg.
// This routine transfers control, so it only accepts a total payload term.
// No lookup by payload type is performed: the innermost lexical destination
// wins, even if an enclosing destination would accept a different type.
let check_raise (g:env) (pre:term) (ph:post_hint_opt g)
  (name:ppname) (arg:term) (rng:range)
  : T.Tac (checker_result_t g pre ph) =
  require_stateful g ph rng;
  match exception_label (bindings g) with
  | Some (lbl, x) ->
    // exception_label selects the destination; lookup_goto separately adds
    // BindingPost obligations for every local/defer scope crossed to reach it.
    // Both respect BindingCleanupBoundary, so cleanup cannot replace a pending
    // exit by raising into an outer scope.
    (match lookup_goto g x with
    | Some (_, c) ->
      (match outcome_types (comp_res c) with
      | Some (exn, a) ->
        let arg = check_tot_term g arg exn in
        let t = mk_term (Tm_Goto {
          lbl=term_of_nvar (lbl, x); arg=constructor "Raised" exn a arg }) rng in
        // Goto substitutes Raised arg into the destination precondition and
        // uses prove_exact. Framing here would strand ownership in a normal
        // continuation which this jump never executes.
        Pulse.Checker.Goto.check_native_raise g pre ph name t exn arg
      | None -> fail g (Some rng) "Internal error: exception label has no outcome type")
    | None -> fail g (Some rng) "Internal error: missing exception label")
  | None ->
    // A fully handled try still has an implicit forwarding branch, and a
    // native call outside any scope still has a Raised branch. Accept either
    // only when the current pure facts prove False. The ghost unreachable
    // call exposes is_unreachable spatially, allowing the ordinary prover to
    // establish ph at any result type. It is not a host-language throw.
    let proof = check_tot_term g unit_const (U.mk_squash tm_l_false) in
    let call = R.mk_app (R.pack_ln (R.Tv_FVar (R.pack_fv (U.mk_pulse_lib_core_lid "unreachable"))))
      [explicit proof] in
    let c = C_STGhost tm_emp_inames { u=u0; res=tm_unit; pre=tm_emp; post=tm_is_unreachable } in
    let t = wrst c (Tm_ST { t=call; args=[] }) in
    prove_post_hint (try_frame_pre false #g (| t, c |) name) ph rng

// Return (normal post hint, outcome post hint, payload type). The stored normal
// comp supplies the result/post but not the entry context: check_scope receives
// that separately as pre. Use the ambient effect for BOTH hints, so wrapping
// outcomes neither upgrades a terminating context nor hides divergent code.
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
  // Inspecting the arrow only finds its domain; this check also validates that
  // the raises expression is total and really returns slprop. The outcome ABI
  // is currently restricted to Type0 for both parameters.
  let exceptional = check_tot_term g exceptional (U.mk_arrow (exn, R.Q_Explicit) tm_slprop) in
  let u = check_universe g exn in
  if not (eq_univ u u0 && eq_univ normal.u u0) then
    fail g (Some rng) "Exception payloads and results must be in Type0";
  // normal.post is closed over its result at index 0. Abstract that binder
  // into q before introducing the DIFFERENT index-0 binder for the outcome:
  //   fun v -> exit_post (fun x -> normal.post[x]) exceptional v.
  let q = U.mk_abs normal.ret_ty R.Q_Explicit normal.post in
  let post = R.mk_app (rules_term "exit_post")
    [implicit exn; implicit normal.ret_ty; explicit q; explicit exceptional; explicit bv0] in
  let outer = intro_post_hint g eff (Some (outcome_type exn normal.ret_ty)) post in
  normal, outer, exn

// Check a source exception scope using the forward-jump discipline:
//   label L { let x = body in Normal x }
// A raise in body jumps directly to L with Raised e, bypassing the Normal
// wrapper. For a function-level scope, desugaring puts its ordinary _return
// label INSIDE this scope, so early return still passes through Normal. A try
// scope need not enclose _return: returning can bypass the try and its catches.
// Neither the exception label nor its Normal wrapper is emitted at runtime.
let check_scope (g:env) (pre:term) (ph:post_hint_opt g) (name:ppname)
  (normal:comp_st) (exceptional:term) (body:st_term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  let normal, outer, exn = posts g ph normal exceptional rng in
  let c = Pulse.Typing.Combinators.comp_for_post_hint g pre outer (fresh g) in
  let lbl = mk_ppname_no_range "_exception" in
  let x = fresh g in
  // A block post becomes its goto's precondition; the goto has unreachable
  // post. In particular, jumping with Raised e requires exceptional e.
  let g' = push_exception g x lbl (goto_comp_of_block_comp c) in
  let r = check g' pre (PostHint normal) name body in
  // Keep the checked normal-result body for runtime extraction. The Normal
  // wrapper and exception label below are used only to validate the ABI/post.
  let (| runtime_body, _ |) = apply_checker_result_k r name in
  // Forget only the result's post-hint refinement, not the checked computation
  // or its effect. We must compose the body with an outcome-producing return
  // rather than force its a-valued result to match the outer outcome type.
  let r = retype_checker_result NoHint r in
  let (| y, g1, _, ctxt, _ |) = r in
  // The checked body extends g' with its result and proof bindings. Establish
  // that the outcome hint, originally checked in g, remains usable in g1.
  assert (g' `env_extends` g);
  env_extends_trans g1 g' g;
  env_extends_trans g1 g outer.g;
  let value = constructor "Normal" exn normal.ret_ty (term_of_nvar (name, y)) in
  let r1 = check g1 ctxt (PostHint outer) name (ret rng outer.ret_ty value) in
  let r = compose_checker_result_t r r1 in
  // Materialize the proof-only composition to establish its outcome contract.
  // Returning in g (not g') keeps the exception destination out of subsequent
  // handlers; the runtime scope stores only the original checked normal body.
  let (| body, c |) = apply_checker_result_k r name in
  let t = wrst c (Tm_NativeScope { body=runtime_body }) in
  let c = match_comp_res_with_post_hint t c ph in
  prove_post_hint (checker_result_for_st_typing (| t, c |) name) ph rng

// Match.check infers the constructor field's type. Each generated branch binds
// one value at index 0: a normal result for Normal, a payload for Raised.
let outcome_branch (ctor:string) (body:st_term) : branch =
  { pat=Pat_Cons (as_fv (rules_name ctor)) [Pat_Var ppname_default.name (FStar.Sealed.seal tm_unknown), false];
    e=body; norw=false }

// Split an already checked call without executing it twice. Checker.ST passes
// its framed result and postcondition here; matching the fresh result variable
// recovers q x ** frame or r e ** frame. Only Normal supplies the ordinary
// continuation. Raised transfers the ENTIRE exceptional context through
// check_raise, which also handles the no-destination/unreachable case.
let unwrap (#g:env) (#pre:term) (ph:post_hint_opt g) (name:ppname)
  (r:checker_result_t g pre NoHint) (exn a post:term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  require_stateful g ph rng;
  // post binds an outcome at index 0. Replace it with Normal bv0 to obtain a
  // post binding an a at index 0; retain the caller's frame and all facts about
  // that value. Do not apply ph until after the outcome has been unwrapped.
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
  // The checked match proves propagation, including an impossible Raised
  // branch. Runtime native calls already return a or throw: retaining this
  // match would reintroduce the outcome ABI we are deliberately erasing.
  let (| _, c |) = apply_checker_result_k r1 name in
  let t = wrst c (Tm_Return { expected_type=a; insert_eq=false; term=term_of_nvar (name, x) }) in
  let r1 : checker_result_t g1 ctxt (PostHint normal) =
    checker_result_for_st_typing (| t, c |) name in
  let r = compose_checker_result_t r r1 in
  prove_post_hint (retype_checker_result NoHint r) ph rng

// Unlike check_scope, try exposes an a-valued result. The protected body and
// normally returning catch clauses must establish the same normal contract.
// Desugaring supplies handler as an ordered payload match with a final re-raise;
// Match.check's negated-prior-pattern facts justify residual forwarding.
let check_try (g:env) (pre:term) (ph:post_hint_opt g) (name:ppname)
  (normal:comp_st) (exceptional:term) (body handler:st_term) (rng:range) (check:check_t)
  : T.Tac (checker_result_t g pre ph) =
  let normal_post, outer, exn = posts g ph normal exceptional rng in
  // NoHint is intentional: this intermediate result is native_outcome, whereas
  // ph describes the final a-valued try. check_scope closes its own label, so
  // the following match sees only outer exception destinations in g1.
  let r = check_scope g pre (PostHint outer) name normal exceptional body rng check in
  let (| runtime_body, _ |) = apply_checker_result_k r name in
  let r = retype_checker_result NoHint r in
  let (| x, g1, (_, ty), ctxt, _ |) = r in
  env_extends_trans g1 g normal_post.g;
  let branches = [
    outcome_branch "Normal" (ret rng normal_post.ret_ty bv0);
    // handler is already closed over the payload at index 0; the Raised
    // pattern binds exactly that variable. Any raise in the clause or its
    // fallback must escape this try, not re-enter the same handler.
    outcome_branch "Raised" handler
  ] in
  let r1 = Pulse.Checker.Match.check g1 ctxt normal_post name
    (ret rng ty (term_of_nvar (name, x))) branches check in
  let (| runtime_match, _ |) = apply_checker_result_k r1 name in
  // Select the already-checked Raised branch with a constructor application.
  // Custard simplifies this closed constructor match; the protected call is
  // never evaluated twice, nor is an outcome allocated at runtime.
  let payload = fresh g1 in
  let raised = constructor "Raised" exn normal_post.ret_ty (term_of_nvar (name, payload)) in
  let runtime_handler = subst_st_term runtime_match [RT.NT x raised] in
  let runtime_handler = close_st_term runtime_handler payload in
  let r = compose_checker_result_t r r1 in
  let (| _, c |) = apply_checker_result_k r name in
  let t = wrst c (Tm_NativeTry { exn_ty=exn; result_ty=normal_post.ret_ty;
                               body=runtime_body; handler=runtime_handler }) in
  prove_post_hint (checker_result_for_st_typing (| t, c |) name) ph rng
