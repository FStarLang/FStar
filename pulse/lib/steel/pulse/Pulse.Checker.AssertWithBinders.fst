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
module Prover = Pulse.Prover
module RT = FStar.Reflection.Typing
module RU = Pulse.RuntimeUtils
let is_host_term (t:R.term) = not (R.Tv_Unknown? (R.inspect_ln t))

let debug_log = Pulse.Typing.debug_log "with_binders"

// let instantiate_binders_with_fresh_names (g:env) (top:R.term) : T.Tac (list nvar & R.term) =
//     let rec aux g (vars:list nvar) (t:R.term) : T.Tac (list nvar & R.term) = 
//         match R.inspect_ln t with
//         | R.Tv_Unknown -> T.fail "Impossible: instantiate_binders_with_fresh_names got an unknown term"
//         | R.Tv_Abs b body ->
//             let bv = R.inspect_binder b in
//             let x = fresh g in
//             let ppname = (mk_ppname bv.ppname (RU.range_of_term t)) in
//             let g = push_binding g x ppname (with_range Tm_Unknown (RU.range_of_term t)) in
//             let vars = (ppname, x)::vars in
//             let body = RT.open_term body x in
//             aux g vars body
//         | _ ->
//           L.rev vars, t
//     in
//     aux g [] top

// let instantiate_names_with_uvars (xs:list nvar) (t0 t1:term)
//   : T.Tac (list (Inf.uvar & term) & vprop & vprop)
//   = let subst, out =
//       T.fold_right (fun (p,x) (subst, out) ->
//         let uv, t = Inf.gen_uvar p in
//         let out = (uv, t)::out in
//         let subst = N.NT x t :: subst in
//         subst, out)
//         xs
//         ([], [])
//     in
//     out, subst_term t0 subst, subst_term t1 subst

// let instantiate_binders_with_uvars (top:R.term) : T.Tac (list (Inf.uvar & term) & vprop) =
//     let rec aux uvars (t:R.term) : T.Tac (list (Inf.uvar & term) & vprop) = 
//         match R.inspect_ln t with
//         | R.Tv_Unknown -> T.fail "Impossible: instantiate_binders_with_uvars got an unknown term"
//         | R.Tv_Abs b body ->
//             let bv = R.inspect_binder b in
//             let uv, t = Inf.gen_uvar (mk_ppname bv.ppname (RU.range_of_term t)) in
//             let uvars = (uv, t)::uvars in
//             let body = RT.subst_term body N.(rt_subst [DT 0 t]) in
//             aux uvars body
//         | _ ->
//           match readback_ty t with
//           | None -> T.fail "Failed to readback elaborated assertion"
//           | Some t -> L.rev uvars, t
//     in
//     aux [] top

let option_must (f:option 'a) (msg:string) : T.Tac 'a =
  match f with
  | Some x -> x
  | None -> T.fail msg

let rec refl_abs_binders (t:R.term) (acc:list binder) : T.Tac (list binder) =
  let open R in
  match inspect_ln t with
  | Tv_Abs b body ->
    let {sort; ppname} = R.inspect_binder b in
    let sort = option_must (readback_ty sort) "Failed to readback elaborated binder in peel_off" in
    refl_abs_binders body
     ({ binder_ty = sort; binder_ppname = mk_ppname ppname (RU.range_of_term t) }::acc)
  | _ -> L.rev acc  

let infer_binder_types (g:env) (bs:list binder) (v:vprop)
  : T.Tac (list binder) =
  match bs with
  | [] -> []
  | _ ->
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
    let inst_abstraction, _ = PC.instantiate_term_implicits g (tm_fstar abstraction v.range) in
    match inst_abstraction.t with
    | Tm_FStar t -> refl_abs_binders t []
    | _ -> T.fail "Impossible: Instantiated abstraction is not embedded F* term"

let rec open_binders (g:env) (bs:list binder) (uvs:env { disjoint uvs g }) (v:term) (body:st_term)
  : T.Tac (uvs:env { disjoint uvs g } & term & st_term) =

  match bs with
  | [] -> (| uvs, v, body |)
  | b::bs ->
    // these binders are only lax checked so far
    let _ = PC.check_universe (push_env g uvs) b.binder_ty in
    let x = fresh (push_env g uvs) in
    let ss = [ DT 0 (tm_var {nm_index=x;nm_ppname=b.binder_ppname}) ] in
    let bs = L.mapi (fun i b ->
      assume (i >= 0);
      subst_binder b (shift_subst_n i ss)) bs in
    let v = subst_term v (shift_subst_n (L.length bs) ss) in
    let body = subst_st_term body (shift_subst_n (L.length bs) ss) in
    open_binders g bs (push_binding uvs x b.binder_ppname b.binder_ty) v body

let close_binders (bs:list (var & typ)) (t:term) : term =
  let r = L.fold_right (fun (x, _) (n, t) ->
    let ss = [ ND x 0 ] in
    n + 1,
    subst_term t (shift_subst_n n ss)
  ) bs (0, t) in
  snd r

// let option_must (f:option 'a) (msg:string) : T.Tac 'a =
//   match f with
//   | Some x -> x
//   | None -> T.fail msg

let unfold_defs (g:env) (defs:option (list string)) (t:term) 
  : T.Tac term
  = let t = elab_term t in
    let head, _ = T.collect_app t in
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

// let prepare_goal hint_type g (v:R.term) : T.Tac (term & term) = 
//   match hint_type with
//   | ASSERT -> 
//     let v = option_must (readback_ty v) "Failed to readback elaborated assertion" in
//     v, v
//   | UNFOLD _ -> 
//     option_must (readback_ty v) "Failed to readback elaborated assertion",
//     unfold_defs g None v
//   | FOLD ns -> 
//     unfold_defs g ns v,
//     option_must (readback_ty v) "Failed to readback elaborated assertion"

let check_unfoldable g (v:term) : T.Tac unit = 
  match v.t with
  | Tm_FStar _ -> ()
  | _ -> 
   fail g 
      (Some v.range)
      (Printf.sprintf "`fold` and `unfold` expect a single user-defined predicate as an argument, \
                        but %s is a primitive term that cannot be folded or unfolded"
                        (P.term_to_string v))

module PS = Pulse.Prover.Substs
let check
  (g:env)
  (st:st_term { Tm_ProofHintWithBinders? st.term })
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check:check_t)

  : T.Tac (checker_result_t g pre post_hint) =

  let Tm_ProofHintWithBinders { hint_type; binders=bs; v; t=body } = st.term in

  let bs = infer_binder_types g bs v in

  let (| uvs, v_opened, body_opened |) = open_binders g bs (mk_env (fstar_env g)) v body in

  match hint_type with
  | ASSERT ->
    let v, body = v_opened, body_opened in
    let (| v, d |) = PC.check_vprop (push_env g uvs) v in
    let (| g1, nts, pre', k_frame |) = Prover.prove pre_typing uvs d in
    let (| x, x_ty, pre'', g2, k |) =
      check g1 (tm_star (PS.nt_subst_term v nts) pre') (magic ()) post_hint (PS.nt_subst_st_term body nts) in
    (| x, x_ty, pre'', g2, k_elab_trans k_frame k |)

  | _ ->
    check_unfoldable g v;
    let v_opened, _ = PC.instantiate_term_implicits (push_env g uvs) v_opened in
    let lhs, rhs =
      match hint_type with      
      | UNFOLD _ ->
        v_opened,
        unfold_defs (push_env g uvs) None v_opened
      | FOLD ns -> 
        unfold_defs (push_env g uvs) ns v_opened,
        v_opened in
    let uvs_bs = L.rev (bindings uvs) in
    let lhs, rhs = close_binders uvs_bs lhs, close_binders uvs_bs rhs in
    let rw = { term = Tm_Rewrite { t1 = lhs;
                                   t2 = rhs };
               range = st.range } in
    let st = { term = Tm_Bind { binder = as_binder (tm_fstar (`unit) st.range);
                                head = rw; body };
               range = st.range } in

    let st =
      match bs with
      | [] -> st
      | _ ->
        { term = Tm_ProofHintWithBinders { hint_type = ASSERT;
                                           binders = bs;
                                           v = lhs;
                                           t = st };
          range = st.range } in
    check g pre pre_typing post_hint st
      


    // match bs with
    // | _::_ ->
    //   let st_wo_binders =
    //     { term = Tm_ProofHintWithBinders {hint_type; binders=[]; v; t=body };
    //       range = st.range } in
    //   let assert_tm =
    //     { term = Tm_ProofHintWithBinders { hint_type = ASSERT;
    //                                        binders = bs;
    //                                        v = v;
    //                                        t = st_wo_binders };
    //       range = st.range } in
    //   check g pre pre_typing post_hint assert_tm
    // | [] ->
    //   let v, _ = PC.instantiate_term_implicits g v in
    //   let lhs, rhs =
    //     match hint_type with      
    //     | UNFOLD _ ->
    //       v,
    //       unfold_defs g None v
    //     | FOLD ns -> 
    //       unfold_defs g ns v,
    //       v in
    //   let rw = { term = Tm_Rewrite { t1 = lhs;
    //                                  t2 = rhs };
    //              range = st.range } in
    //   let st = { term = Tm_Bind { binder = as_binder (tm_fstar (`unit) st.range);
    //                               head = rw; body };
    //              range = st.range } in
    //   check g pre pre_typing post_hint st
      

//   : T.Tac (checker_result_t g pre post_hint frame_pre)
//   = let Tm_ProofHintWithBinders { hint_type; binders; v; t=body } = st.term in
//     check_unfoldable g hint_type v;
//     let nvars, v = infer_binder_types g binders v in
//     let lhs, rhs = prepare_goal hint_type g v in
//     let uvs, lhs, rhs = instantiate_names_with_uvars nvars lhs rhs in
//     debug_log g (fun _ -> Printf.sprintf "Trying to solve %s \nagainst context %s" (P.term_to_string lhs) (P.term_to_string pre));
//     let solution = Inf.try_inst_uvs_in_goal g pre lhs in
//     match Inf.unsolved solution uvs with
//     | Some uvs ->
//       fail g (Some st.range) 
//              (Printf.sprintf "Could not instantiate %s"
//                              (String.concat ", " (T.map (fun (_, t) -> P.term_to_string t) uvs)))
//     | _ ->
//       debug_log g (fun _ -> Printf.sprintf "Solution: %s\n" (Inf.solutions_to_string solution));
//       let sub = 
//         T.fold_left 
//             (fun subst (uv, t) ->
//                 let sol = Inf.apply_solution solution t in 
//                 N.DT 0 sol::shift_subst subst)
//             []
//             uvs
//       in
//       let seq t1 t2 = 
//           { term = Tm_Bind { binder = as_binder (tm_fstar (`unit) st.range);
//                              head = t1; body = t2 };
//             range = st.range }
//       in
//       match hint_type with
//       | ASSERT ->
//         let assert_term = tm_fstar (`(Pulse.Steel.Wrapper.assert_)) st.range in
//         let vprop_to_assert = Inf.apply_solution solution lhs in
//         let asrt = { term = Tm_STApp { head=assert_term; arg_qual=None; arg=vprop_to_assert}; 
//                      range = st.range } in
//         let tm = seq asrt (subst_st_term body sub) in
//         debug_log g (fun _ -> Printf.sprintf "After with_binders: about to check %s\n" (P.st_term_to_string tm));
//         check g tm pre pre_typing post_hint frame_pre
//       | UNFOLD _
//       | FOLD _ ->
//         let rw = { term = Tm_Rewrite { t1 = Inf.apply_solution solution lhs;
//                                        t2 = Inf.apply_solution solution rhs };
//                    range = st.range } in
//         let body' = subst_st_term body sub in
//         let tm = seq rw body' in
//         debug_log g (fun _ -> Printf.sprintf "After with_binders: about to check %s\n" (P.st_term_to_string tm));
//         check g tm pre pre_typing post_hint frame_pre
