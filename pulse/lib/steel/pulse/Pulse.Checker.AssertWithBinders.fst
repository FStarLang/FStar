module Pulse.Checker.AssertWithBinders

module T = FStar.Tactics.V2
module R = FStar.Reflection.V2
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Common
open Pulse.Elaborate.Pure
open Pulse.Typing.Env
module L = FStar.List.Tot
module PC = Pulse.Checker.Pure
module P = Pulse.Syntax.Printer
module N = Pulse.Syntax.Naming 
module Inf = Pulse.Checker.Inference
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
let is_host_term (t:R.term) = not (R.Tv_Unknown? (R.inspect_ln t))

let debug_log = Pulse.Checker.Common.debug_log "with_binders"

let instantiate_binders_with_fresh_names (g:env) (top:R.term) : T.Tac (list nvar & R.term) =
    let rec aux g (vars:list nvar) (t:R.term) : T.Tac (list nvar & R.term) = 
        match R.inspect_ln t with
        | R.Tv_Unknown -> T.fail "Impossible"
        | R.Tv_Abs b body ->
            let bv = R.inspect_binder b in
            let x = fresh g in
            let ppname = (mk_ppname bv.ppname (RU.range_of_term t)) in
            let g = push_binding g x ppname (with_range Tm_Unknown (RU.range_of_term t)) in
            let vars = (ppname, x)::vars in
            let body = RT.open_term body x in
            aux g vars body
        | _ ->
          L.rev vars, t
    in
    aux g [] top

let instantiate_names_with_uvars (xs:list nvar) (t0 t1:term)
  : T.Tac (list (Inf.uvar & term) & vprop & vprop)
  = let subst, out =
      T.fold_right (fun (p,x) (subst, out) ->
        let uv, t = Inf.gen_uvar p in
        let out = (uv, t)::out in
        let subst = N.NT x t :: subst in
        subst, out)
        xs
        ([], [])
    in
    out, subst_term t0 subst, subst_term t1 subst

let instantiate_binders_with_uvars (top:R.term) : T.Tac (list (Inf.uvar & term) & vprop) =
    let rec aux uvars (t:R.term) : T.Tac (list (Inf.uvar & term) & vprop) = 
        match R.inspect_ln t with
        | R.Tv_Unknown -> T.fail "Impossible"
        | R.Tv_Abs b body ->
            let bv = R.inspect_binder b in
            let uv, t = Inf.gen_uvar (mk_ppname bv.ppname (RU.range_of_term t)) in
            let uvars = (uv, t)::uvars in
            let body = RT.subst_term body N.(rt_subst [DT 0 t]) in
            aux uvars body
        | _ ->
          match readback_ty t with
          | None -> T.fail "Failed to readback elaborated assertion"
          | Some t -> L.rev uvars, t
    in
    aux [] top

let infer_binder_types (g:env) (bs:list binder) (v:vprop)
  : T.Tac (list nvar & R.term) = 
    let tv = elab_term v in
    if not (is_host_term tv)
    then fail g (Some v.range) (Printf.sprintf "Cannot infer type of %s" (P.term_to_string v));
    let as_binder (b:binder) : R.binder =
        let open R in
        let bv : binder_view = 
            { sort = elab_term b.binder_ty;
              ppname = b.binder_ppname.name;
              qual = Q_Explicit;
              attrs = [] } in
        pack_binder bv
    in
    let abstraction = 
        L.fold_right 
            (fun b (tv:host_term) -> 
                let b = as_binder b in
                R.pack_ln (R.Tv_Abs b tv))
            bs
            tv
    in
    // T.print (Printf.sprintf "About to elaborate assert body: %s" (T.term_to_string abstraction));
    let inst_abstraction, _ = PC.instantiate_term_implicits g (tm_fstar abstraction v.range) in
    // T.print (Printf.sprintf "Instantiated abstraction is: %s" (T.term_to_string abstraction));
    match inst_abstraction.t with
    | Tm_FStar t -> 
      instantiate_binders_with_fresh_names g t
    |  _ -> T.fail "Impossible"

let option_must (f:option 'a) (msg:string) : T.Tac 'a =
  match f with
  | Some x -> x
  | None -> T.fail msg

let unfold_defs (g:env) (defs:option (list string)) (t:R.term) 
  : T.Tac term
  = let head, _ = T.collect_app t in
    match R.inspect_ln head with
    | R.Tv_FVar fv
    | R.Tv_UInst fv _ -> (
        let head = String.concat "." (R.inspect_fv fv) in
        let fully = 
          match defs with
          | Some defs -> defs
          | None -> []
        in
        let rt = RU.unfold_def (fstar_env g) head fully t in
        let rt = option_must rt "Unexpected: reduction produced an ill-formed term" in
        let ty = option_must (readback_ty rt) "Unexpected: unable to readback unfolded term" in
        debug_log g (fun _ -> Printf.sprintf "Unfolded %s to F* term %s and readback as %s" (T.term_to_string t) (T.term_to_string rt) (P.term_to_string ty));
        ty
      )
    | _ ->
      fail g (Some (RU.range_of_term t)) (Printf.sprintf "Cannot unfold %s" (T.term_to_string t))
    
let prepare_goal hint_type g (v:R.term) : T.Tac (term & term) = 
  match hint_type with
  | ASSERT -> 
    let v = option_must (readback_ty v) "Failed to readback elaborated assertion" in
    v, v
  | UNFOLD _ -> 
    option_must (readback_ty v) "Failed to readback elaborated assertion",
    unfold_defs g None v
  | FOLD ns -> 
    unfold_defs g ns v,
    option_must (readback_ty v) "Failed to readback elaborated assertion"

let check
  (g:env)
  (st:st_term{Tm_ProofHintWithBinders? st.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)
  = let Tm_ProofHintWithBinders { hint_type; binders; v; t=body } = st.term in
    let nvars, v = infer_binder_types g binders v in
    let lhs, rhs = prepare_goal hint_type g v in
    let uvs, lhs, rhs = instantiate_names_with_uvars nvars lhs rhs in
    debug_log g (fun _ -> Printf.sprintf "Trying to solve %s \nagainst context %s" (P.term_to_string lhs) (P.term_to_string pre));
    let solution = Pulse.Checker.Inference.try_inst_uvs_in_goal g pre lhs in
    match Inf.unsolved solution uvs with
    | Some uvs ->
      fail g (Some st.range) 
             (Printf.sprintf "Could not instantiate %s"
                             (String.concat ", " (T.map (fun (_, t) -> P.term_to_string t) uvs)))
    | _ ->
      debug_log g (fun _ -> Printf.sprintf "Solution: %s\n" (Inf.solutions_to_string solution));
      let sub = 
        T.fold_left 
            (fun subst (uv, t) ->
                let sol = Inf.apply_solution solution t in 
                N.DT 0 sol::shift_subst subst)
            []
            uvs
      in
      let rewrite_and_check lhs rhs =
        let rw = { term = Tm_Rewrite { t1 = lhs; t2 = rhs }; range = st.range } in
        let body' = subst_st_term body sub in
        let tm = Tm_Bind { binder = as_binder (tm_fstar (`unit) st.range);
                           head = rw;
                           body = body' } in
        let tm = { term = tm; range = st.range } in
        debug_log g (fun _ -> Printf.sprintf "After unfold: about to check %s\n" (P.st_term_to_string tm));
        check g tm pre pre_typing post_hint
      in
      match hint_type with
      | ASSERT ->
        let body' = subst_st_term body sub in
        check g body' pre pre_typing post_hint
      | UNFOLD _
      | FOLD _ ->
        rewrite_and_check (Inf.apply_solution solution lhs) (Inf.apply_solution solution rhs)

    