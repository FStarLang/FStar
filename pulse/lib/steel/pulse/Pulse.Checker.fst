module Pulse.Checker
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Typing.Combinators
open Pulse.Checker.Pure
open Pulse.Checker.Framing
open Pulse.Checker.Bind
open Pulse.Checker.VPropEquiv
open Pulse.Checker.Common

module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

module Abs = Pulse.Checker.Abs
module If = Pulse.Checker.If
module Match = Pulse.Checker.Match
module WithLocal = Pulse.Checker.WithLocal
module While = Pulse.Checker.While
module STApp = Pulse.Checker.STApp
module Exists = Pulse.Checker.Exists
module Par = Pulse.Checker.Par
module Admit = Pulse.Checker.Admit
module Return = Pulse.Checker.Return
module Rewrite = Pulse.Checker.Rewrite
module ElimPure = Pulse.Prover.ElimPure
module ElimExists = Pulse.Prover.ElimExists

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

let has_pure_vprops (pre:term) = L.existsb (fun (t:term) -> Tm_Pure? t.t) (vprop_as_list pre)
let elim_pure_explicit_lid = mk_steel_wrapper_lid "elim_pure_explicit"

let default_binder_annot = {
    binder_ppname = ppname_default;
    binder_ty = tm_unknown
}

// let add_intro_pure rng (continuation:st_term) (p:term) =
//     let wr t = { term = t; range = rng } in
//     let intro_pure_tm =
//       wr (
//         Tm_Protect
//           { t = wr (Tm_IntroPure { p; should_check=should_check_false }) }
//       )
//     in
//     wr (
//       Tm_Protect { t = wr (Tm_Bind { binder = default_binder_annot;
//                                       head = intro_pure_tm;
//                                       body = continuation }) }
//     )

// #push-options "--fuel 2 --ifuel 1 --z3rlimit_factor 10"
// let uvar_tys = list (Pulse.Checker.Inference.uvar & term)
// let rec prepare_instantiations
//           (g:env)
//           (out:list (vprop & either term term))
//           (out_uvars: uvar_tys)
//           (goal_vprop:vprop)
//           witnesses
//   : T.Tac (vprop & list (vprop & either term term) & uvar_tys)
//   = match witnesses, goal_vprop.t with
//     | [], Tm_ExistsSL u b p ->
//       let next_goal_vprop, inst, uv =
//           let uv, t = Pulse.Checker.Inference.gen_uvar b.binder_ppname in
//           open_term' p t 0, Inr t, uv
//       in
//       prepare_instantiations g ((goal_vprop, inst)::out) ((uv,b.binder_ty)::out_uvars) next_goal_vprop []

//     | [], _ -> 
//       goal_vprop, out, out_uvars

//     | t :: witnesses, Tm_ExistsSL u b p ->
//       let next_goal_vprop, inst, uvs =
//           match (t<:term).t with
//           | Tm_Unknown ->
//             let uv, t = Pulse.Checker.Inference.gen_uvar b.binder_ppname in
//             open_term' p t 0, Inr t, [(uv,b.binder_ty)]
//           | _ ->
//             open_term' p t 0, Inl t, []
//       in
//       prepare_instantiations g ((goal_vprop, inst)::out) (uvs@out_uvars) next_goal_vprop witnesses

//     |  _ ->
//        fail g None "Unexpected number of instantiations in intro"

//  let rec build_instantiations solutions insts
//       : T.Tac st_term 
//       = let one_inst (v, i) =
//           let v = Pulse.Checker.Inference.apply_solution solutions v in
//           match i with
//           | Inl user_provided ->
//             wr (Tm_IntroExists {erased=false; p=v; witnesses=[user_provided]; should_check=should_check_true})

//           | Inr inferred ->
//             let sol = Pulse.Checker.Inference.apply_solution solutions inferred in
//             match unreveal sol with
//             | Some sol ->
//               wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]; should_check=should_check_false})
//             | _ ->
//               wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]; should_check=should_check_false})
//         in
//         match insts with
//         | [] -> T.fail "Impossible"
//         | [hd] -> wr (Tm_Protect { t = one_inst hd })

//         | hd::tl -> wr (Tm_Protect 
//                           { t = wr (Tm_Bind { binder = default_binder_annot;
//                                               head = wr (Tm_Protect { t = one_inst hd });
//                                               body = build_instantiations solutions tl }) })
   
// let maybe_infer_intro_exists
//   (g:env)
//   (st:st_term{Tm_IntroExists? st.term})
//   (pre:term)
//   : T.Tac st_term
//   = let remove_pure_conjuncts t =
//         let rest, pure = 
//             List.Tot.partition #term
//               (function {t=Tm_Pure _} | {t=Tm_Emp} -> false | _ -> true)
//               (vprop_as_list t)
//         in
//         let rest =
//           match list_as_vprop rest with
//           | {t=Tm_Star t {t=Tm_Emp}} -> t
//           | {t=Tm_Star {t=Tm_Emp} t} -> t        
//           | t -> t
//         in
//         rest, pure
//     in
//     (* Weird: defining prepare_instantiations here causes extraction to crash with
//        Failure("This should not happen (should have been handled at Tm_abs level)")
//      *)
//     if RU.debug_at_level (fstar_env g) "inference"
//     then (      
//       T.print (Printf.sprintf "At %s: infer_intro_exists for %s\n"
//                   (T.range_to_string st.range)
//                   (P.st_term_to_string st))
//     );
//     let Tm_IntroExists {erased; p=t; witnesses} = st.term in
//     let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t in
//     let goal_vprop, insts, uvs = prepare_instantiations g [] [] t witnesses in
//     let goal_vprop, pure_conjuncts = remove_pure_conjuncts goal_vprop in      
//     let solutions = Pulse.Checker.Inference.try_inst_uvs_in_goal g pre goal_vprop in
//     // T.print
//     //   (Printf.sprintf
//     //      "maybe_infer_intro_exists: solutions after trying inst with pre: %s, goal: %s: %s\n"
//     //       (P.term_to_string pre)
//     //       (P.term_to_string goal_vprop)
//     //       (Pulse.Checker.Inference.solutions_to_string solutions));
//     let maybe_solve_pure solutions p =
//       let p = Pulse.Checker.Inference.apply_solution solutions p in
//       match p.t with
//       | Tm_Pure p -> (
//         let sols = Pulse.Checker.Inference.try_solve_pure_equalities g p in
//         sols @ solutions
//         )
//       | _ -> solutions
//     in
//     let solutions = T.fold_left maybe_solve_pure solutions pure_conjuncts in
//     if RU.debug_at_level (fstar_env g) "inference"
//     then (      
//       T.print
//         (Printf.sprintf
//           "maybe_infer_intro_exists: solutions after solving pure conjuncts (%s): %s\n"
//             (P.term_to_string (list_as_vprop pure_conjuncts))
//             (Pulse.Checker.Inference.solutions_to_string solutions))
//     );
//     let mk_hide ty_opt (e:term) : term =
//         let hd = tm_fvar (as_fv hide_lid) in
//         match ty_opt with
//         | None -> tm_pureapp hd None e
//         | Some ty -> tm_pureapp (tm_pureapp hd (Some Implicit) ty) None e
//     in
//     let type_of_uvar uv =
//       match List.Tot.tryFind (fun (u, _) -> Pulse.Checker.Inference.uvar_eq u uv) uvs with
//       | None -> None
//       | Some (_, ty) -> Some ty
//     in
//     let solutions = 
//       T.map
//         (fun (u, v) -> 
//           let sol = Pulse.Checker.Inference.apply_solution solutions v in
//           match unreveal sol with
//           | Some _ -> u, sol
//           | _ -> u, mk_hide (type_of_uvar u) sol)
//         solutions
//     in
//     let _ =
//       match Pulse.Checker.Inference.unsolved solutions uvs with
//       | Some uvs ->
//         fail g (Some st.range) (Printf.sprintf "Could not instantiate existential variables %s\n"
//                                     (String.concat ", " (T.map (fun (u, _) -> Pulse.Checker.Inference.uvar_to_string u) uvs)))
//       | None -> ()
//     in
//     let wr t = { term = t; range = st.range } in
//     let intro_exists_chain = build_instantiations solutions insts in
//     let pure_conjuncts =
//       T.map 
//        (fun vp -> 
//           match (Pulse.Checker.Inference.apply_solution solutions vp).t with
//           | Tm_Pure p -> [p]
//           | p -> [])
//        pure_conjuncts
//     in
//     let pure_conjuncts = L.flatten pure_conjuncts in
//     let result = List.Tot.fold_left (add_intro_pure intro_exists_chain.range) intro_exists_chain pure_conjuncts in
//     if RU.debug_at_level (fstar_env g) "inference"
//     then (      
//       T.print (Printf.sprintf "Inferred pure and exists:{\n\t %s\n\t}"
//                 (P.st_term_to_string result))
//     );
//     result
      

// let handle_framing_failure
//     (g:env)
//     (t0:st_term)
//     (pre:term)
//     (pre_typing: tot_typing g pre tm_vprop)
//     (post_hint:post_hint_opt g)
//     (failure:framing_failure)
//     (check:check_t)
//   : T.Tac (checker_result_t g pre post_hint true)
//   = let wr t = { term = t; range = t0.range } in
//     if RU.debug_at_level (fstar_env g) "inference"
//     then (      
//       T.print (Printf.sprintf
//                       "Handling framing failure in term:\n%s\n\
//                         with unmatched_pre={\n%s\n} and context={\n%s\n}"
//                       (P.st_term_to_string t0)
//                       (terms_to_string failure.unmatched_preconditions)
//                       (terms_to_string failure.remaining_context))
//     );
//     let pures, rest = 
//       L.partition #term (function {t=Tm_Pure _} -> true | _ -> false) failure.unmatched_preconditions
//     in
//     let t =
//       T.fold_left 
//         (fun t (p:term) ->
//           match p.t with
//           | Tm_Pure p -> add_intro_pure t0.range t p
//           | _ -> T.fail "Impossible")
//         (wr (Tm_Protect { t = t0 })) //don't elim what we just intro'd here
//         pures
//     in
//     let rec handle_intro_exists (rest:list term) (t:st_term)
//       : T.Tac (checker_result_t g pre post_hint true)
//       = match rest with
//         | [] -> check g t pre pre_typing post_hint true
//         | {t=Tm_ExistsSL u ty p; range} :: rest ->
//           let t = 
//               Tm_Bind { 
//                 binder = default_binder_annot;
//                 head =
//                    wr (Tm_Protect {
//                           t = wr (Tm_IntroExists {
//                                     erased=true;
//                                     p=with_range (Tm_ExistsSL u ty p) range;
//                                     witnesses=[];
//                                     should_check=should_check_true
//                                   });
//                       });
//                 body = wr (Tm_Protect { t })
//               }
//           in
//           handle_intro_exists rest (wr t)
//         | _ ->
//          fail g (Some t0.range) (format_failed_goal g failure.remaining_context rest)
//     in
//     handle_intro_exists rest t

// let protect t = { term = Tm_Protect { t }; range = t.range }
  
// let rec unprotect t = 
//   let wr t0 = { term = t0; range = t.range } in
//   match t.term with
//   | Tm_Protect { t = { term = Tm_Bind { binder; head; body } } } ->
//     wr (Tm_Bind { binder; head=protect head; body })
//   | Tm_Protect { t = { term = Tm_If { b; then_; else_; post }}} ->
//     wr (Tm_If {b; then_=protect then_; else_=protect else_; post } )
//   | Tm_Protect { t } ->
//     unprotect t
//   | _ -> t
  
// #push-options "--ifuel 2"

// let elim_then_check (#g:env) (#ctxt:term)
//                     (ctxt_typing:tot_typing g ctxt tm_vprop)
//                     (st:st_term { not (Tm_Protect? st.term) })
//                     (post_hint: post_hint_opt g)
//                     (check:check_t)
//   : T.Tac (checker_result_t g ctxt post_hint true)
//   = let (| g', ctxt', ctxt'_typing, elab_k |) = ElimExists.elim_exists ctxt_typing in
//     let (| g'', ctxt'', ctxt'_typing, elab_k' |) = ElimPure.elim_pure ctxt'_typing in
//     if RU.debug_at_level (fstar_env g) "inference"
//     then ( T.print (Printf.sprintf "Eliminated context from\n\t%s\n\tto %s\n"
//                 (P.term_to_string ctxt)
//                 (P.term_to_string ctxt'') )) ;
//     let res = check g'' (protect st) ctxt'' ctxt'_typing post_hint true in
//     elab_k post_hint (elab_k' post_hint res)

let rec gen_names_for_unknowns (g:env) (t:term) (ws:list term)
  : T.Tac (list (nvar & term) &  // new names with their types
           term &  // opened vprop                                             
           list term)  // new list of witnesses with _ replaced with corresponding new names
  = match ws with
    | [] -> [], t, []
    | w::ws ->
      match t.t with
      | Tm_ExistsSL _ b body ->
        let xopt, w, g =
          match w.t with
          | Tm_Unknown ->
            let x = fresh g in
            Some x,
            tm_var {nm_index=x;nm_ppname=b.binder_ppname},
            push_binding g x b.binder_ppname b.binder_ty
          | _ -> None, w, g in
        let t : term = open_term' body w 0 in
        let new_names, t, ws = gen_names_for_unknowns g t ws in
        (match xopt with
         | Some x ->
           ((b.binder_ppname, x), b.binder_ty)::new_names,
           t,
           w::ws
         | None -> new_names, t, w::ws)
      | _ -> fail g (Some t.range) "intro exists with non-existential"

let instantiate_unknown_witnesses (g:env) (t:st_term { Tm_IntroExists? t.term })
  : T.Tac (option st_term) =

  let Tm_IntroExists { erased; p; witnesses=ws } = t.term in

  let new_names, opened_p, new_ws = gen_names_for_unknowns g p ws in
  match new_names with
  | [] -> None
  | _ ->
    let e2 = {t with term=Tm_IntroExists {erased; p; witnesses=new_ws }} in
    let e1 =
      let hint_type = ASSERT in
      let binders = [] in
      let v = opened_p in
      {term=Tm_ProofHintWithBinders { hint_type;binders;v;t=e2 }; range=t.range} in
    
    let t = L.fold_right (fun new_name (e:st_term { Tm_ProofHintWithBinders? e.term }) ->
      let (ppname, x), ty = new_name in
      let e = close_st_term' e x 0 in
      match e.term with
      | Tm_ProofHintWithBinders {hint_type;binders;v;t} ->
        let new_binder = {binder_ty=ty; binder_ppname=ppname} in
        let t' = Tm_ProofHintWithBinders {hint_type;binders=new_binder::binders;v;t} in
        {e with term=t'}
    ) new_names e1 in
    Some t

let maybe_intro_exists_erased (t:st_term { Exists.intro_exists_witness_singleton t })
  : t':st_term { Exists.intro_exists_witness_singleton t' } =

  let Tm_IntroExists { erased; p; witnesses=[w] } = t.term in
  match unreveal w with
  | Some w ->
    let t' = Tm_IntroExists {erased=true;p;witnesses=[w]} in
    {t with term=t'}
  | _ -> t

let rec transform_to_unary_intro_exists (g:env) (t:term) (ws:list term)
  : T.Tac st_term =
  
  match ws with
  | [] -> fail g (Some t.range) "intro exists with empty witnesses"
  | [w] ->
    if Tm_ExistsSL? t.t
    then wr (Tm_IntroExists {erased=false;p=t;witnesses=[w]})
    else fail g (Some t.range) "intro exists with non-existential"
  | w::ws ->
    match t.t with
    | Tm_ExistsSL u b body ->
      let body = subst_term body [ DT 0 w ] in
      let st = transform_to_unary_intro_exists g body ws in
      // w is the witness
      let intro = wr (Tm_IntroExists {erased=true;p=t;witnesses=[w]}) in
      wr (Tm_Bind {binder=null_binder tm_unit;
                      head=st;
                      body= intro})

    | _ -> fail g (Some t.range) "intro exists with non-existential"

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let rec check' : bool -> check_t =
  fun (allow_inst:bool)
      (g0:env)
      (pre0:term)
      (pre0_typing: tot_typing g0 pre0 tm_vprop)
      (post_hint:post_hint_opt g0)
      (t:st_term) ->

  // let open T in
  T.print (Printf.sprintf "At %s: allow_inst: %s, context: %s, term: %s\n"
             (T.range_to_string t.range)
             (string_of_bool allow_inst)
             (Pulse.Syntax.Printer.term_to_string pre0)
             (Pulse.Syntax.Printer.st_term_to_string t));

  // if not (Tm_Protect? t.term) && frame_pre
  // then elim_then_check pre_typing t post_hint (check' allow_inst)
  // else begin
  //   if RU.debug_at_level (fstar_env g) "proof_states"
  //   then (
  //     T.print (Printf.sprintf "At %s: context is {\n%s\n}"
  //                           (T.range_to_string t.range)
  //                           (P.term_to_string pre))
  //   );
  //   let t = unprotect t in

  
  let (| g, pre, pre_typing, k_elim_pure |) =
    Pulse.Prover.ElimPure.elim_pure pre0_typing in

  let r : checker_result_t g pre post_hint =
    let g = push_context (P.tag_of_st_term t) t.range g in
    // try 
    match t.term with
    | Tm_Return _ ->
      Return.check_return g t pre pre_typing post_hint
    
    | Tm_Abs _ -> T.fail "Tm_Abs check should not have been called in the checker"

    | Tm_STApp _ ->
      STApp.check_stapp g t pre pre_typing post_hint

    | Tm_ElimExists _ ->
      Exists.check_elim_exists g t pre pre_typing post_hint

    | Tm_IntroExists { p; witnesses } ->
      (match instantiate_unknown_witnesses g t with
       | Some t ->
        //  fail g None
        //    (Printf.sprintf "\n\nAfter inst. wits: %s\n\n" (P.st_term_to_string t));
         check' true g pre pre_typing post_hint t
       | None ->
         match witnesses with
         | [] -> fail g (Some t.range) "intro exists with empty witnesses"
         | [_] ->
           Exists.check_intro_exists_either g (maybe_intro_exists_erased t) None pre pre_typing post_hint
         | _ ->
           let t = transform_to_unary_intro_exists g p witnesses in
           check' true g pre pre_typing post_hint t)
      // let should_infer_witnesses =
      //   match witnesses with
      //   | [w] -> (
      //     match w.t with
      //     | Tm_Unknown -> true
      //     | _ -> false
      //   )
      //   | _ -> true
      // in
      // if should_infer_witnesses
      // then (
      //   fail g None "Pulse cannot yet infer witnesses for existential quantifiers; annotate them explicitly"
      //   // let unary_intros = maybe_infer_intro_exists g t pre in
      //   // // T.print (Printf.sprintf "Inferred unary_intros:\n%s\n"
      //   // //                         (P.st_term_to_string unary_intros));
      //   // check' allow_inst g unary_intros pre pre_typing post_hint frame_pre
      // )
      // else Exists.check_intro_exists_either g t None pre pre_typing post_hint

    | Tm_Bind _ ->
      check_bind g t pre pre_typing post_hint (check' true)

    | Tm_TotBind _ ->
      check_tot_bind g t pre pre_typing post_hint (check' true)

    | Tm_If { b; then_=e1; else_=e2; post=post_if } ->
      let post =
        match post_if, post_hint with
        | None, Some p -> p
        | Some p, None ->
            Checker.Common.intro_post_hint g None p
        | Some p, Some q ->
          Pulse.Typing.Env.fail g (Some t.range) 
            (Printf.sprintf 
                "Multiple annotated postconditions---remove one of them.\n\
                The context expects the postcondition %s,\n\
                but this conditional was annotated with postcondition %s"
                (P.term_to_string (q <: post_hint_t).post)
                (P.term_to_string p))
        | _, _ ->
          Pulse.Typing.Env.fail g (Some t.range) 
            (Printf.sprintf
                "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\n\
                Either annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")
      in
      let (| x, t, pre', g1, k |) : checker_result_t g pre (Some post) =
        If.check_if g b e1 e2 pre pre_typing post (check' true) in
      (| x, t, pre', g1, k |)

    | Tm_While _ ->
      While.check_while g t pre pre_typing post_hint (check' true)

    | Tm_Match {sc;returns_=post_match;brs} ->
      // TODO : dedup
      let post =
        match post_match, post_hint with
        | None, Some p -> p
        | Some p, None ->
          Checker.Common.intro_post_hint g None p
        | Some p, Some q ->
          Pulse.Typing.Env.fail g (Some t.range)
            (Printf.sprintf
               "Multiple annotated postconditions---remove one of them.\n\
                The context expects the postcondition %s,\n\
                but this conditional was annotated with postcondition %s"
                (P.term_to_string (q <: post_hint_t).post)
                (P.term_to_string p))
        | _, _ ->
          Pulse.Typing.Env.fail g (Some t.range)
            (Printf.sprintf
               "Pulse cannot yet infer a postcondition for a non-tail conditional statement;\n\
                Either annotate this `if` with `returns` clause; or rewrite your code to use a tail conditional")
      in
      let (| x, ty, pre', g1, k |) = Match.check_match g sc brs pre pre_typing post (check' true) in
      (| x, ty, pre', g1, k |)

    | Tm_ProofHintWithBinders _ ->
      Pulse.Checker.AssertWithBinders.check g t pre pre_typing post_hint (check' true)

    | Tm_WithLocal _ ->
      WithLocal.check_withlocal g t pre pre_typing post_hint (check' true)

    | Tm_Par _ ->
      Par.check_par allow_inst g t pre pre_typing post_hint (check' true)

    | Tm_IntroPure _ -> 
      Pulse.Checker.IntroPure.check_intro_pure g t pre pre_typing post_hint

    | Tm_Admit _ ->
      Admit.check_admit g t pre pre_typing post_hint

    | Tm_Rewrite _ ->
      Rewrite.check_rewrite g t pre pre_typing post_hint

    | _ -> T.fail "Checker form not implemented"
  in

  let (| x, t, pre', g1, k |) = r in
  (| x, t, pre', g1, k_elab_trans k_elim_pure k |)

  // admit ()

  // (| x, t, pre'', g2, k_elab_trans k_elim_pure k |)




    // with
    // | Framing_failure failure ->
    //   if not frame_pre
    //   then T.fail "Impossible, handle_framing_failure when frame_pre is false"
    //   else
    //     handle_framing_failure g t pre pre_typing post_hint failure (check' true)
    // | e -> T.raise e
  // end

let check = check' true
// fun g ctxt ctxt_typing post_hint t ->
// let (| g1, ctxt', ctxt'_typing, k_elim |) =
//   Pulse.Prover.ElimPure.elim_pure ctxt_typing in

// let (| x, t, ctxt', g1, k |) = check' true g1 ctxt' ctxt'_typing post_hint t in

// (| x, t, ctxt', g1, k_elab_trans k_elim k |)
