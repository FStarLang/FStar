module Pulse.Checker
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Framing
open Pulse.Checker.Bind
open Pulse.Checker.VPropEquiv

module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

module Abs = Pulse.Checker.Abs
module If = Pulse.Checker.If
module WithLocal = Pulse.Checker.WithLocal
module While = Pulse.Checker.While
module STApp = Pulse.Checker.STApp
module Exists = Pulse.Checker.Exists
module Par = Pulse.Checker.Par
module Admit = Pulse.Checker.Admit
module Return = Pulse.Checker.Return
module Rewrite = Pulse.Checker.Rewrite
module ElimPure = Pulse.Checker.Auto.ElimPure
module ElimExists = Pulse.Checker.Auto.ElimExists

let ( * ) (t1 t2:term) : term = Tm_Star t1 t2

noeq
type framing_st (g:env) (original_ctxt:term) = {
    t:st_term;
    c: c:comp { stateful_comp c };
    t_typing:st_typing g t c;

    ctxt:term;
    matched_pre:term;
    unmatched_pre:term;
    ctxt_eq:vprop_equiv g original_ctxt (ctxt * matched_pre);
    pre_eq:vprop_equiv g (comp_pre c) (unmatched_pre * matched_pre);
}

assume val intro_vp:
  g:env ->
  ctxt:term -> tot_typing g ctxt Tm_VProp ->
  v:vprop -> tot_typing g v Tm_VProp ->
  option (ctxt':term &
          t:st_term &
          c:comp { stateful_comp c /\ comp_post c == v} &
          st_typing g t c &
          vprop_equiv g ctxt (ctxt' * comp_pre c))

assume val add_frame (#g:env) (#t:st_term) (#c:comp { stateful_comp c }) (t_typing:st_typing g t c)
  (frame:term)
  : c':comp { stateful_comp c' /\
              comp_pre c' == comp_pre c * frame /\
              comp_post c' == comp_post c * frame } &
    st_typing g t c'

assume val c_equiv_post (#g:env) (#t:st_term) (#c:comp { stateful_comp c /\ ln (comp_post c)}) (t_typing:st_typing g t c)
  (post:term {ln post}) (_:vprop_equiv g post (comp_post c))
  : c':comp { stateful_comp c' /\
              comp_pre c' == comp_pre c /\
              comp_post c' == post } &
    st_typing g t c'

assume val c_equiv_pre (#g:env) (#t:st_term) (#c:comp { stateful_comp c }) (t_typing:st_typing g t c)
  (pre:term) (_:vprop_equiv g pre (comp_pre c))
  : c':comp { stateful_comp c' /\
              comp_pre c' == comp_pre c /\
              comp_post c' == comp_post c } &
    st_typing g t c'

#push-options "--z3rlimit_factor 8 --fuel 2 --ifuel 2"
let rec handle_framing_failure_experimental (#g:env) (#ctxt:term)
  (ctxt_typing:tot_typing g ctxt Tm_VProp)
  (s:framing_st g ctxt)
  : T.Tac (t:st_term &
           c:comp { stateful_comp c /\ comp_pre c == ctxt } &
           st_typing g t c) =

  // we have typing of ctxt, eq of ctxt with comp_pre c * s.ctxt
  // so with inversion of vprop_equiv and Tm_Star typing w.r.t. typing
  let s_ctxt_typing : tot_typing g s.ctxt Tm_VProp = magic () in

  match vprop_as_list s.unmatched_pre with
  | [] ->
    // from s.pre_eq, we should get this, since s.unmatched_pre is emp
    let pre_eq : vprop_equiv g (comp_pre s.c) s.matched_pre = magic () in
    // from s.ctxt_eq
    let ctxt_eq : vprop_equiv g ctxt (s.matched_pre * s.ctxt) = magic () in
    // using pre_eq and ctxt_eq above
    let ctxt_eq : vprop_equiv g (comp_pre s.c * s.ctxt)
                                ctxt = magic () in
    let f : frame_for_req_in_ctxt g ctxt (comp_pre s.c) =
      (| s.ctxt, s_ctxt_typing, ctxt_eq |) in
    let (| c', t_typing |) = apply_frame ctxt_typing s.t_typing f in
    (| s.t, c', t_typing |)

  | hd::tl ->
    // in s.pre_eq we have s.unmatched_pre in vprop_equiv relation
    //   with comp_pre c, from that we should be able to derive it
    let hd_typing : tot_typing g hd Tm_VProp = magic () in
    assume (ln hd);
    match intro_vp g s.ctxt s_ctxt_typing hd hd_typing with
    | Some (| ctxt', t, c, t_typing, veq |) ->
      // we now need to create the new framing_st

      // commutation of list_as_vprop and vprop_as_list
      assume (s.unmatched_pre == hd * (list_as_vprop tl));

      // the term that we create for the next framing state is:
      //   bind (add_frame (tl * s.matched) t) s.t
      let c_pre = comp_pre c in
      let veq : vprop_equiv g s.ctxt (ctxt' * c_pre) = veq in
      assume (ln (list_as_vprop tl) /\ ln s.matched_pre);
      let (| c, t_typing |) = add_frame t_typing (list_as_vprop tl * s.matched_pre) in
      assert (comp_pre c == c_pre * (list_as_vprop tl * s.matched_pre));
      assert (comp_post c == hd * (list_as_vprop tl * s.matched_pre));
        
      let (| c, t_typing |) = c_equiv_post t_typing
        (s.unmatched_pre * s.matched_pre) (magic ()) in
      assert (ln (comp_post c));

      let (| s_c, s_t_typing |) = c_equiv_pre s.t_typing
        (s.unmatched_pre * s.matched_pre) (magic ()) in
        
      let x = fresh g in
      admit ();
      let (| t, c, t_typing |) = Pulse.Checker.Bind.mk_bind
        g
        (comp_pre c)  // c_pre * (tl * s.matched_pre)
        t
        s.t
        c
        s_c
        (v_as_nv x)
        t_typing
        (magic ())  // typing of c's return type, from inversion?
        s_t_typing
        (magic ())  // typing of s_c's return type, from inversion?
        (magic ())  // post typing for s_c ... from inversion and then weakening
      in
      

      admit ()
      

    | _ ->
      T.fail (Printf.sprintf "Cannot match the precondition %s"
                (P.term_to_string hd))













let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

#push-options "--query_stats"

let has_pure_vprops (pre:term) = L.existsb Tm_Pure? (vprop_as_list pre)
let elim_pure_explicit_lid = mk_steel_wrapper_lid "elim_pure_explicit"

let default_binder_annot = {
    binder_ppname = RT.pp_name_default;
    binder_ty = Tm_Unknown
}
   
let add_intro_pure rng (continuation:st_term) (p:term) =
    let wr t = { term = t; range = rng } in
    let intro_pure_tm =
      wr (
        Tm_Protect
          { t = wr (Tm_STApp 
                      { head = tm_pureapp 
                                (tm_fvar (as_fv (mk_steel_wrapper_lid "intro_pure")))
                                None
                                p;
                        arg_qual = None;
                        arg = tm_constant R.C_Unit }) }
      )
    in
    wr (
      Tm_Protect { t = wr (Tm_Bind { binder = default_binder_annot;
                                      head = intro_pure_tm;
                                      body = continuation }) }
    )

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
let uvar_tys = list (Pulse.Checker.Inference.uvar_id & term)
let rec prepare_instantiations
  (out:list (vprop & either term term))
  (out_uvars: uvar_tys)
  goal_vprop
  witnesses
  : T.Tac (vprop & list (vprop & either term term) & uvar_tys)
  = match witnesses, goal_vprop with
    | [], Tm_ExistsSL u ty p _ ->  
      let next_goal_vprop, inst, uv =
          let uv, t = Pulse.Checker.Inference.gen_uvar () in
          open_term' p t 0, Inr t, uv
      in
      prepare_instantiations ((goal_vprop, inst)::out) ((uv,ty)::out_uvars) next_goal_vprop []

    | [], _ -> 
      goal_vprop, out, out_uvars

    | t :: witnesses, Tm_ExistsSL u ty p _ ->
      let next_goal_vprop, inst, uvs =
          match t with
          | Tm_Unknown ->
            let uv, t = Pulse.Checker.Inference.gen_uvar () in
            open_term' p t 0, Inr t, [(uv,ty)]
          | _ ->
            open_term' p t 0, Inl t, []
      in
      prepare_instantiations ((goal_vprop, inst)::out) (uvs@out_uvars) next_goal_vprop witnesses

    |  _ ->
       T.fail "Unexpected number of instantiations in intro"

 let rec build_instantiations solutions insts
      : T.Tac st_term 
      = let one_inst (v, i) =
          let v = Pulse.Checker.Inference.apply_solution solutions v in
          match i with
          | Inl user_provided ->
            wr (Tm_IntroExists {erased=false; p=v; witnesses=[user_provided]})

          | Inr inferred ->
            let sol = Pulse.Checker.Inference.apply_solution solutions inferred in
            match unreveal sol with
            | Some sol ->
              wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]})
            | _ ->
              wr (Tm_IntroExists {erased=true; p=v; witnesses=[sol]})
        in
        match insts with
        | [] -> T.fail "Impossible"
        | [hd] -> wr (Tm_Protect { t = one_inst hd })

        | hd::tl -> wr (Tm_Protect 
                          { t = wr (Tm_Bind { binder = default_binder_annot;
                                              head = wr (Tm_Protect { t = one_inst hd });
                                              body = build_instantiations solutions tl }) })
   
let maybe_infer_intro_exists
  (g:env)
  (st:st_term{Tm_IntroExists? st.term})
  (pre:term)
  : T.Tac st_term
  = let remove_pure_conjuncts t =
        let rest, pure = 
            List.Tot.partition
              (function Tm_Pure _ | Tm_Emp -> false | _ -> true)
              (vprop_as_list t)
        in
        let rest =
          match list_as_vprop rest with
          | Tm_Star t Tm_Emp -> t
          | Tm_Star Tm_Emp t -> t        
          | t -> t
        in
        rest, pure
    in
    (* Weird: defining prepare_instantiations here causes extraction to crash with
       Failure("This should not happen (should have been handled at Tm_abs level)")
     *)
    if RU.debug_at_level g "inference"
    then (      
      T.print (Printf.sprintf "At %s: infer_intro_exists for %s\n"
                  (T.range_to_string st.range)
                  (P.st_term_to_string st))
    );
    let Tm_IntroExists {erased; p=t; witnesses} = st.term in
    let t, _ = Pulse.Checker.Pure.instantiate_term_implicits g t in
    let goal_vprop, insts, uvs = prepare_instantiations [] [] t witnesses in
    let goal_vprop, pure_conjuncts = remove_pure_conjuncts goal_vprop in      
    let solutions = Pulse.Checker.Inference.try_inst_uvs_in_goal pre goal_vprop in
    // T.print
    //   (Printf.sprintf
    //      "maybe_infer_intro_exists: solutions after trying inst with pre: %s, goal: %s: %s\n"
    //       (P.term_to_string pre)
    //       (P.term_to_string goal_vprop)
    //       (Pulse.Checker.Inference.solutions_to_string solutions));
    let maybe_solve_pure solutions p =
      let p = Pulse.Checker.Inference.apply_solution solutions p in
      match p with
      | Tm_Pure p -> (
        let sols = Pulse.Checker.Inference.try_solve_pure_equalities p in
        sols @ solutions
        )
      | _ -> solutions
    in
    let solutions = T.fold_left maybe_solve_pure solutions pure_conjuncts in
    if RU.debug_at_level g "inference"
    then (      
      T.print
        (Printf.sprintf
          "maybe_infer_intro_exists: solutions after solving pure conjuncts (%s): %s\n"
            (P.term_to_string (list_as_vprop pure_conjuncts))
            (Pulse.Checker.Inference.solutions_to_string solutions))
    );
    let mk_hide ty_opt (e:term) : term =
        let hd = tm_fvar (as_fv hide_lid) in
        match ty_opt with
        | None -> tm_pureapp hd None e
        | Some ty -> tm_pureapp (tm_pureapp hd (Some Implicit) ty) None e
    in
    let type_of_uvar uv = List.Tot.assoc uv uvs in
    let solutions = 
      List.Tot.map
        (fun (u, v) -> 
          let sol = Pulse.Checker.Inference.apply_solution solutions v in
          match unreveal sol with
          | Some _ -> u, sol
          | _ -> u, mk_hide (type_of_uvar u) sol)
        solutions
    in
    let _ =
      match List.Tot.tryFind (fun (u, _u_ty) ->
           None? ((List.Tot.tryFind (fun (u', _) -> u = u') solutions))
         ) uvs with
      | Some (u, _) ->
        T.fail (Printf.sprintf "maybe_infer_intro_exists: unification failed for uvar %s\n"
                  (Pulse.Checker.Inference.uvar_id_to_string u))
      | None -> ()
    in
    let wr t = { term = t; range = st.range } in
    let intro_exists_chain = build_instantiations solutions insts in
    let pure_conjuncts =
      List.Tot.collect 
       (fun vp -> 
          match Pulse.Checker.Inference.apply_solution solutions vp with
          | Tm_Pure p -> [p]
          | p -> [])
       pure_conjuncts
    in
    let result = List.Tot.fold_left (add_intro_pure intro_exists_chain.range) intro_exists_chain pure_conjuncts in
    if RU.debug_at_level g "inference"
    then (      
      T.print (Printf.sprintf "Inferred pure and exists:{\n\t %s\n\t}"
                (P.st_term_to_string result))
    );
    result
      

let handle_framing_failure
    (g:env)
    (t0:st_term)
    (pre:term)
    (pre_typing: tot_typing g pre Tm_VProp)
    (post_hint:post_hint_opt g)
    (failure:framing_failure)
    (check:check_t)
  : T.Tac (checker_result_t g pre post_hint)
  = let wr t = { term = t; range = t0.range } in
    if RU.debug_at_level g "inference"
    then (      
      T.print (Printf.sprintf
                      "Handling framing failure in term:\n%s\n\
                        with unmatched_pre={\n%s\n} and context={\n%s\n}"
                      (P.st_term_to_string t0)
                      (terms_to_string failure.unmatched_preconditions)
                      (terms_to_string failure.remaining_context))
    );
    let pures, rest = 
      L.partition (function Tm_Pure _ -> true | _ -> false) failure.unmatched_preconditions
    in
    let t =
      T.fold_left 
        (fun t p ->
          match p with
          | Tm_Pure p -> add_intro_pure t0.range t p
          | _ -> T.fail "Impossible")
        (wr (Tm_Protect { t = t0 })) //don't elim what we just intro'd here
        pures
    in
    let rec handle_intro_exists rest (t:st_term)
      : T.Tac (checker_result_t g pre post_hint)
      = match rest with
        | [] -> check g t pre pre_typing post_hint
        | Tm_ExistsSL u ty p se :: rest ->
          let t = 
              Tm_Bind { 
                binder = default_binder_annot;
                head =
                   wr (Tm_Protect {
                          t = wr (Tm_IntroExists {
                                    erased=true;
                                    p=Tm_ExistsSL u ty p se;
                                    witnesses=[]
                                  });
                      });
                body = wr (Tm_Protect { t })
              }
          in
          handle_intro_exists rest (wr t)
        | _ ->
          T.fail (Printf.sprintf 
                      "Failed to satisfy the following preconditions:\n%s\nContext has\n%s\nat command %s\n"
                       (terms_to_string rest)
                       (terms_to_string failure.remaining_context)
                       (P.st_term_to_string t0))
    in
    handle_intro_exists rest t

let protect t = { term = Tm_Protect { t }; range = t.range }
  
let rec unprotect t = 
  let wr t0 = { term = t0; range = t.range } in
  match t.term with
  | Tm_Protect { t = { term = Tm_Bind { binder; head; body } } } ->
    wr (Tm_Bind { binder; head=protect head; body })
  | Tm_Protect { t = { term = Tm_If { b; then_; else_; post }}} ->
    wr (Tm_If {b; then_=protect then_; else_=protect else_; post } )
  | Tm_Protect { t } ->
    unprotect t
  | _ -> t
  
#push-options "--ifuel 2"

let elim_then_check (#g:env) (#ctxt:term) 
                    (ctxt_typing:tot_typing g ctxt Tm_VProp)
                    (st:st_term { not (Tm_Protect? st.term) })
                    (post_hint: post_hint_opt g)
                    (check:check_t)
  : T.Tac (checker_result_t g ctxt post_hint)
  = if RU.debug_at_level g "proof_states"
    then ( T.print "Unprotected node: Elim exists and pure \n" );
    let (| g', ctxt', ctxt'_typing, elab_k |) = ElimExists.elim_exists ctxt_typing in
    let (| g'', ctxt'', ctxt'_typing, elab_k' |) = ElimPure.elim_pure ctxt'_typing in
    if RU.debug_at_level g "proof_states"
    then ( T.print (Printf.sprintf "Eliminated context from\n\t%s\n\tto %s\n"
                (P.term_to_string ctxt)
                (P.term_to_string ctxt'') )) ;
    let res = check g'' (protect st) ctxt'' ctxt'_typing post_hint in
    elab_k post_hint (elab_k' post_hint res)
      

#push-options "--query_stats"
let rec check' : bool -> check_t =
  fun (allow_inst:bool)
      (g:env)
      (t:st_term)
      (pre:term)
      (pre_typing: tot_typing g pre Tm_VProp)
      (post_hint:post_hint_opt g) ->
  let open T in
  // T.print (Printf.sprintf "At %s: allow_inst: %s, context: %s, term: %s\n"
  //            (T.range_to_string t.range)
  //            (string_of_bool allow_inst)
  //            (Pulse.Syntax.Printer.term_to_string pre)
  //            (Pulse.Syntax.Printer.st_term_to_string t));

  if not (Tm_Protect? t.term)
  then elim_then_check pre_typing t post_hint (check' allow_inst)
  else begin
    if RU.debug_at_level g "proof_states"
    then (
      T.print (Printf.sprintf "At %s: (%s) %s\n\tprecondition is %s\n"
                            (T.range_to_string t.range)
                            (P.tag_of_st_term t)
                            (P.st_term_to_string t)
                            (P.term_to_string pre))
    );
    let t = unprotect t in
    let g = push_context (P.tag_of_st_term t) g in
    try 
      match t.term with
      | Tm_Protect _ -> T.fail "Protect should have been removed"

      // | Tm_Return {term = Tm_Bvar _} -> T.fail "not locally nameless"
      | Tm_Return _ ->
        Return.check_return allow_inst g t pre pre_typing post_hint
    
      | Tm_Abs _ ->
        Abs.check_abs g t pre pre_typing post_hint (check' true)

      | Tm_STApp _ ->
        STApp.check_stapp allow_inst g t pre pre_typing post_hint check'

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
          | _, _ -> T.fail "Either two annotations for if post or none"
        in
        let (| t, c, d |) = If.check_if g b e1 e2 pre pre_typing post (check' true) in
        ( (| t, c, d |) <: checker_result_t g pre post_hint)

      | Tm_ElimExists _ ->
        Exists.check_elim_exists g t pre pre_typing post_hint

      | Tm_IntroExists { witnesses } ->
        let should_infer_witnesses =
          match witnesses with
          | [w] -> (
            match w with
            | Tm_Unknown -> true
            | _ -> false
          )
          | _ -> true
        in
        if should_infer_witnesses
        then (
          let unary_intros = maybe_infer_intro_exists g t pre in
          // T.print (Printf.sprintf "Inferred unary_intros:\n%s\n"
          //                         (P.st_term_to_string unary_intros));
          check' allow_inst g unary_intros pre pre_typing post_hint
        )
        else (
          Exists.check_intro_exists_either g t None pre pre_typing post_hint
        )

      | Tm_While _ ->
        While.check_while allow_inst g t pre pre_typing post_hint check'

      | Tm_Admit _ ->
        Admit.check_admit g t pre pre_typing post_hint

      | Tm_Par _ ->
        Par.check_par allow_inst g t pre pre_typing post_hint check'

      | Tm_WithLocal _ ->
        WithLocal.check_withlocal allow_inst g t pre pre_typing post_hint check'

      | Tm_Rewrite _ ->
        Rewrite.check_rewrite g t pre pre_typing post_hint
    with
    | Framing_failure failure ->
      handle_framing_failure g t pre pre_typing post_hint failure (check' true)
    | e -> T.raise e
  end

let check = check' true
