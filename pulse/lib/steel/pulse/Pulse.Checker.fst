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
   
let maybe_add_elim_pure (pre:list term) (t:st_term) : T.Tac (bool & st_term) =
  let pure_props =
    L.flatten (L.map (fun (t:term) ->
                      match t with
                      | Tm_Pure p -> [p]
                      | _ -> []) pre) in

  if L.length pure_props = 0
  then false, t
  else (
    true,
    L.fold_left 
      (fun t (p:term) ->
        let elim_pure_tm =
          Tm_STApp { head = tm_fvar (as_fv elim_pure_explicit_lid);
                     arg_qual = None;
                     arg = p }
        in
        let bind =
          Tm_Bind { binder = default_binder_annot;
                    head = wr (Tm_Protect { t = wr elim_pure_tm });
                    body = t }
        in
        wr bind)
      t
      pure_props
  )

#push-options "--query_stats --fuel 2 --ifuel 1 --z3rlimit_factor 10"
let rec prepare_instantiations
  (out:list (vprop & either term term))
  (out_uvars:list Pulse.Checker.Inference.uvar_id)
  goal_vprop
  witnesses
  : T.Tac (vprop & list (vprop & either term term) & list Pulse.Checker.Inference.uvar_id)
  = match witnesses, goal_vprop with
    | [], Tm_ExistsSL u ty p _ ->  
      let next_goal_vprop, inst, uv =
          let uv, t = Pulse.Checker.Inference.gen_uvar () in
          open_term' p t 0, Inr t, uv
      in
      prepare_instantiations ((goal_vprop, inst)::out) (uv::out_uvars) next_goal_vprop []

    | [], _ -> 
      goal_vprop, out, out_uvars

    | t :: witnesses, Tm_ExistsSL u ty p _ ->
      let next_goal_vprop, inst, uvs =
          match t with
          | Tm_Unknown ->
            let uv, t = Pulse.Checker.Inference.gen_uvar () in
            open_term' p t 0, Inr t, [uv]
          | _ ->
            open_term' p t 0, Inl t, []
      in
      prepare_instantiations ((goal_vprop, inst)::out) (uvs@out_uvars) next_goal_vprop witnesses

    |  _ ->
       T.fail "Unexpected number of instantiations in intro"


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
    (* Weird: defining this here causes extraction to crash with
       Failure("This should not happen (should have been handled at Tm_abs level)")
     *)                                                                           
    // let rec prepare_instantiations (out:list (vprop & term)) goal_vprop witnesses
    //   : T.Tac (vprop & list (vprop & term))
    //   = match witnesses, goal_vprop with
    //     | [], _ -> 
    //       goal_vprop, out
    //     | t :: witnesses, Tm_ExistsSL u ty p _ ->
    //       let inst =
    //         match t with
    //         | Tm_Unknown -> gen_uvar ty
    //         | _ -> t
    //       in
    //       let next_goal_vprop = open_term' p inst 0 in
    //       prepare_instantiations ((goal_vprop, inst)::out) next_goal_vprop witnesses
    //     |  _ ->
    //       T.fail "Unexpected number of instantiations in intro"
    // in
    let Tm_IntroExists {erased; p=t; witnesses} = st.term in
    let (| t, t_typing |) = check_vprop g t in
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
          match is_eq2 p with
          | Some (l, r) ->
            let open Pulse.Checker.Inference in
            if contains_uvar l
            ||  contains_uvar r
            then begin
              // T.print (Printf.sprintf
              //   "maybe_infer_intro_exists:maybe_solve_pure: trying to unify l: %s and r:%s\n"
              //   (P.term_to_string l)
              //   (P.term_to_string r));
              let sols = try_unify l r in
              // T.print (Printf.sprintf
              //   "maybe_infer_intro_exists:maybe_solve_pure: solutions after unification: %s\n"
              //   (Pulse.Checker.Inference.solutions_to_string sols));
              sols@solutions
            end
            else solutions
          | _ -> solutions
        )
      | _ -> solutions
    in
    let solutions = T.fold_left maybe_solve_pure solutions pure_conjuncts in
    // T.print
    //   (Printf.sprintf
    //      "maybe_infer_intro_exists: solutions after solving pure conjuncts (%s): %s\n"
    //       (P.term_to_string (list_as_vprop pure_conjuncts))
    //       (Pulse.Checker.Inference.solutions_to_string solutions));
    let mk_hide (e:term) : term =
        let hd = tm_fvar (as_fv hide_lid) in
        tm_pureapp hd None e
    in    
    let solutions = 
      List.Tot.map
        (fun (u, v) -> 
          let sol = Pulse.Checker.Inference.apply_solution solutions v in
          match unreveal sol with
          | Some _ -> u, sol
          | _ -> u, mk_hide sol)
        solutions
    in
    let _ =
      match List.Tot.tryFind (fun u ->
           None? ((List.Tot.tryFind (fun (u', _) -> u = u') solutions))
         ) uvs with
      | Some u ->
        T.fail (Printf.sprintf "maybe_infer_intro_exists: unification failed for uvar %s\n"
                  (Pulse.Checker.Inference.uvar_id_to_string u))
      | None -> ()
    in
    let wr t = { term = t; range = st.range } in
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
    in
    build_instantiations solutions insts

let range_of_head (t:st_term) : option (term & range) =
  match t.term with
  | Tm_STApp { head } ->
    let rec aux (t:term) : (term & range) =
      match t with
      | Tm_FStar _ r ->
        t, r
      | _ -> t, Range.range_0
    in
    Some (aux head)
  | _ -> None

let tag_of_term (t:term) =
  match t with
  | Tm_Emp -> "Tm_Emp"
  | Tm_Pure _ -> "Tm_Pure"
  | Tm_Star _ _ -> "Tm_Star"
  | Tm_ExistsSL _ _ _ _ -> "Tm_ExistsSL"
  | Tm_ForallSL _ _ _ -> "Tm_ForallSL"
  | Tm_VProp -> "Tm_VProp"
  | Tm_Inames -> "Tm_Inames"
  | Tm_EmpInames -> "Tm_EmpInames"
  | Tm_Unknown -> "Tm_Unknown"
  | Tm_FStar _ _ -> "Tm_FStar"

let tag_of_st_term (t:st_term) =
  match t.term with
  | Tm_Return _ -> "Tm_Return"
  | Tm_Abs _ -> "Tm_Abs"
  | Tm_STApp _ -> "Tm_STApp"
  | Tm_Bind _ -> "Tm_Bind"
  | Tm_TotBind _ -> "Tm_TotBind"
  | Tm_If _ -> "Tm_If"
  | Tm_ElimExists _ -> "Tm_ElimExists"
  | Tm_IntroExists _ -> "Tm_IntroExists"
  | Tm_While _ -> "Tm_While"
  | Tm_Par _ -> "Tm_Par"
  | Tm_WithLocal _ -> "Tm_WithLocal"
  | Tm_Rewrite _ -> "Tm_Rewrite"
  | Tm_Admit _ -> "Tm_Admit"
  | Tm_Protect _ -> "Tm_Protect"
  
let maybe_log t =
  let _ =
    match range_of_head t with
    | Some (head, range) ->
      T.print (Printf.sprintf "At location %s: Checking app with head (%s) = %s"
                         (T.range_to_string range)
                         (tag_of_term head)
                         (P.term_to_string head))
    | None -> ()
  in
  match t.term with
  | Tm_STApp { head; arg_qual=None; arg=p } ->
    begin match is_fvar head with
          | Some (l, _) ->
            if l = elim_pure_explicit_lid
            then T.print (Printf.sprintf "LOG ELIM PURE: %s\n"
                         (P.term_to_string p))
          | _ -> ()
    end
                    
  | Tm_STApp { head; arg_qual=None } ->
    begin match is_pure_app head with
          | Some (head, None, p) ->
            begin match is_fvar head with
                  | Some (l, _) ->
                    if l = mk_steel_wrapper_lid "intro_pure"
                    then T.print (Printf.sprintf "LOG INTRO PURE: %s\n"
                                 (P.term_to_string p))
                  | _ -> ()
            end
          | _ -> ()
    end
  | _ -> ()

let handle_framing_failure
    (g:env)
    (t0:st_term)
    (pre:term)
    (pre_typing: tot_typing g pre Tm_VProp)
    (post_hint:post_hint_opt g)
    (failure:framing_failure)
    (check:check_t)
  : T.Tac (t:st_term &
           c:comp{stateful_comp c ==> comp_pre c == pre} &
           st_typing g t c)
  = let wr t = { term = t; range = t0.range } in
    let add_intro_pure p t =
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
                                        body = t }) }
      )
    in
    // T.print (Printf.sprintf
    //                  "Handling framing failure in term:\n%s\n\
    //                   with unmatched_pre={\n%s\n} and context={\n%s\n}"
    //                  (P.st_term_to_string t0)
    //                  (terms_to_string failure.unmatched_preconditions)
    //                  (terms_to_string failure.remaining_context));
    let pures, rest = 
      L.partition (function Tm_Pure _ -> true | _ -> false) failure.unmatched_preconditions
    in
    let t =
      T.fold_left 
        (fun t p ->
          match p with
          | Tm_Pure p -> add_intro_pure p t
          | _ -> T.fail "Impossible")
        (wr (Tm_Protect { t = t0 })) //don't elim what we just intro'd here
        pures
    in
    let rec handle_intro_exists rest (t:st_term)
      : T.Tac (t:st_term &
               c:comp{stateful_comp c ==> comp_pre c == pre} &
               st_typing g t c)
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

let rec maybe_add_elims
           (g:env)
           (ctxt:list term)
           (t:st_term)
  : T.Tac st_term
  = let wr t' = { term = t'; range = t.range } in
    match ctxt with
    | [] -> t
    | Tm_ExistsSL u ty b se :: rest ->
      let e = wr (Tm_Protect { t = wr (Tm_ElimExists { p = Tm_ExistsSL u ty b se }) }) in
      let x = fresh g in
      let px = v_as_nv x in
      let g = extend x (Inl ty) g in
      let b = open_term_nv b px in
      let t = maybe_add_elims g [b] t in
      let t = close_st_term t x in
      let t = Tm_Bind { binder = default_binder_annot;
                        head = e;
                        body = wr (Tm_Protect { t }) } in
      maybe_add_elims g rest (wr t)
    | Tm_Pure p :: rest ->
      let elim_pure_tm = 
        wr (Tm_STApp { head = tm_fvar (as_fv elim_pure_explicit_lid);
                       arg_qual = None;
                       arg = p })
      in
      wr (
        Tm_Bind { binder = default_binder_annot;
                  head = wr (Tm_Protect { t = elim_pure_tm } );
                  body = wr (Tm_Protect { t = maybe_add_elims g rest t }) }
      )

    | Tm_Star p q :: rest ->
      maybe_add_elims g (p :: q :: rest) t    
      
    | _ :: rest ->
      maybe_add_elims g rest t

let rec unprotect t = 
  let wr t0 = { term = t0; range = t.range } in
  let protect t = { term = Tm_Protect { t }; range = t.range } in
  match t.term with
  | Tm_Protect { t = { term = Tm_Bind { binder; head; body } } } ->
    wr (Tm_Bind { binder; head=protect head; body })
  | Tm_Protect { t = { term = Tm_If { b; then_; else_; post }}} ->
    wr (Tm_If {b; then_=protect then_; else_=protect else_; post } )
  | Tm_Protect { t } ->
    unprotect t
  | _ -> t
  
let auto_elims (g:env) (ctxt:term) (t:st_term) =
  match t.term with
  | Tm_Protect _ -> unprotect t
  | _ ->
    let ctxt = vprop_as_list ctxt in
    let t = maybe_add_elims g ctxt t in 
    unprotect t
    
#push-options "--ifuel 2"
let rec print_st_head (t:st_term)
  : Tot string (decreases t) =
  match t.term with
  | Tm_Abs _  -> "Abs"
  | Tm_Protect p -> print_st_head p.t
  | Tm_Return p -> print_head p.term
  | Tm_Bind _ -> "Bind"
  | Tm_TotBind _ -> "TotBind"
  | Tm_If _ -> "If"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"  
and print_head (t:term) =
  match t with
  // | Tm_FVar fv
  // | Tm_UInst fv _ -> String.concat "." fv.fv_name
  // | Tm_PureApp head _ _ -> print_head head
  | _ -> "<pure term>"


let rec print_skel (t:st_term) = 
  match t.term with
  | Tm_Abs { body }  -> Printf.sprintf "(fun _ -> %s)" (print_skel body)
  | Tm_Protect { t=p } -> Printf.sprintf "(Protect %s)" (print_skel p)
  | Tm_Return { term = p } -> print_head p
  | Tm_Bind { head=e1; body=e2 } -> Printf.sprintf "(Bind %s %s)" (print_skel e1) (print_skel e2)
  | Tm_TotBind { body=e2 } -> Printf.sprintf "(TotBind _ %s)" (print_skel e2)
  | Tm_If _ -> "If"
  | Tm_While _ -> "While"
  | Tm_Admit _ -> "Admit"
  | Tm_Par _ -> "Par"
  | Tm_Rewrite _ -> "Rewrite"
  | Tm_WithLocal _ -> "WithLocal"
  | Tm_STApp { head = p } -> print_head p
  | Tm_IntroExists _ -> "IntroExists"
  | Tm_ElimExists _ -> "ElimExists"

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
  let t : st_term = //weird, remove the annotation and get a strange failure
    if allow_inst
    then auto_elims g pre t
    else t
  in
  if RU.debug_at_level g "proof_states"
  then (
    T.print (Printf.sprintf "At %s: precondition is %s\n"
                          (T.range_to_string t.range)
                          (Pulse.Syntax.Printer.term_to_string pre))
  );
  let g = push_context (tag_of_st_term t) g in
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
      If.check_if g b e1 e2 pre pre_typing post (check' true)

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

let check = check' true
