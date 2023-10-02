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
open Pulse.Checker.Bind
open Pulse.Checker.VPropEquiv
open Pulse.Checker.Base

module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module FV = Pulse.Typing.FV
module RU = Pulse.RuntimeUtils
module Metatheory = Pulse.Typing.Metatheory

module Abs = Pulse.Checker.Abs
module If = Pulse.Checker.If
module Bind = Pulse.Checker.Bind
module Match = Pulse.Checker.Match
module WithLocal = Pulse.Checker.WithLocal
module While = Pulse.Checker.While
module STApp = Pulse.Checker.STApp
module Exists = Pulse.Checker.Exists
module Par = Pulse.Checker.Par
module Admit = Pulse.Checker.Admit
module Return = Pulse.Checker.Return
module Rewrite = Pulse.Checker.Rewrite
module ElimPure = Pulse.Checker.Prover.ElimPure
module ElimExists = Pulse.Checker.Prover.ElimExists

let terms_to_string (t:list term)
  : T.Tac string 
  = String.concat "\n" (T.map Pulse.Syntax.Printer.term_to_string t)

let default_binder_annot = {
    binder_ppname = ppname_default;
    binder_ty = tm_unknown
}

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

  let Tm_IntroExists { p; witnesses=ws } = t.term in

  let new_names, opened_p, new_ws = gen_names_for_unknowns g p ws in
  match new_names with
  | [] -> None
  | _ ->
    let e2 = {t with term=Tm_IntroExists { p; witnesses=new_ws }} in
    let e1 =
      let hint_type = ASSERT { p = opened_p } in
      let binders = [] in
      {term=Tm_ProofHintWithBinders { hint_type;binders;t=e2 }; range=t.range; effect_tag=as_effect_hint STT_Ghost } in
    
    let t = 
      L.fold_right
        (fun new_name (e:st_term { Tm_ProofHintWithBinders? e.term }) ->
          let (ppname, x), ty = new_name in
          let e = close_st_term' e x 0 in
          match e.term with
          | Tm_ProofHintWithBinders {hint_type;binders;t} ->
            let new_binder = {binder_ty=ty; binder_ppname=ppname} in
            let t' = Tm_ProofHintWithBinders {hint_type;binders=new_binder::binders;t} in
            {e with term=t'})
        new_names
        e1 in
    Some t

let rec transform_to_unary_intro_exists (g:env) (t:term) (ws:list term)
  : T.Tac st_term =
  
  match ws with
  | [] -> fail g (Some t.range) "intro exists with empty witnesses"
  | [w] ->
    if Tm_ExistsSL? t.t
    then wtag (Some STT_Ghost) (Tm_IntroExists {p=t;witnesses=[w]})
    else fail g (Some t.range) "intro exists with non-existential"
  | w::ws ->
    match t.t with
    | Tm_ExistsSL u b body ->
      let body = subst_term body [ DT 0 w ] in
      let st = transform_to_unary_intro_exists g body ws in
      // w is the witness
      let intro = wtag None (Tm_IntroExists {p=t;witnesses=[w]}) in
      wtag None
           (Tm_Bind {binder=null_binder tm_unit;
                     head=st;
                     body= intro})

    | _ -> fail g (Some t.range) "intro exists with non-existential"

#push-options "--z3rlimit_factor 4 --fuel 0 --ifuel 1"
let rec check
  (g0:env)
  (pre0:term)
  (pre0_typing: tot_typing g0 pre0 tm_vprop)
  (post_hint:post_hint_opt g0)
  (res_ppname:ppname)
  (t:st_term) : T.Tac (checker_result_t g0 pre0 post_hint) =

  // T.print (Printf.sprintf "At %s: context: %s, term: %s\n"
  //            (T.range_to_string t.range)
  //            (Pulse.Syntax.Printer.term_to_string pre0)
  //            (Pulse.Syntax.Printer.st_term_to_string t));

  let (| g, pre, pre_typing, k_elim_pure |) =
    Pulse.Checker.Prover.ElimPure.elim_pure pre0_typing in

  let r : checker_result_t g pre post_hint =
    let g = push_context (P.tag_of_st_term t) t.range g in
    match t.term with
    | Tm_Return _ ->
      Return.check g pre pre_typing post_hint res_ppname t
    
    | Tm_Abs _ -> T.fail "Tm_Abs check should not have been called in the checker"

    | Tm_STApp _ ->
      STApp.check g pre pre_typing post_hint res_ppname t

    | Tm_ElimExists _ ->
      Exists.check_elim_exists g pre pre_typing post_hint res_ppname t

    | Tm_IntroExists { p; witnesses } ->
      (match instantiate_unknown_witnesses g t with
       | Some t ->
         check g pre pre_typing post_hint res_ppname t
       | None ->
         match witnesses with
         | [] -> fail g (Some t.range) "intro exists with empty witnesses"
         | [_] ->
           Exists.check_intro_exists g pre pre_typing post_hint res_ppname t None 
         | _ ->
           let t = transform_to_unary_intro_exists g p witnesses in
           check g pre pre_typing post_hint res_ppname t)
    | Tm_Bind _ ->
      Bind.check_bind g pre pre_typing post_hint res_ppname t check

    | Tm_TotBind _ ->
      Bind.check_tot_bind g pre pre_typing post_hint res_ppname t check

    | Tm_If { b; then_=e1; else_=e2; post=post_if } ->
      let post =
        match post_if, post_hint with
        | None, Some p -> p
        | Some p, None ->
          Checker.Base.intro_post_hint g None None p
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
        If.check g pre pre_typing post res_ppname b e1 e2 check in
      (| x, t, pre', g1, k |)

    | Tm_While _ ->
      While.check g pre pre_typing post_hint res_ppname t check

    | Tm_Match {sc;returns_=post_match;brs} ->
      // TODO : dedup
      let post =
        match post_match, post_hint with
        | None, Some p -> p
        | Some p, None ->
          Checker.Base.intro_post_hint g None None p
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
      let (| x, ty, pre', g1, k |) =
        Match.check g pre pre_typing post res_ppname sc brs check in
      (| x, ty, pre', g1, k |)

    | Tm_ProofHintWithBinders _ ->
      Pulse.Checker.AssertWithBinders.check g pre pre_typing post_hint res_ppname t check

    | Tm_WithLocal _ ->
      WithLocal.check g pre pre_typing post_hint res_ppname t check

    | Tm_Par _ ->
      Par.check g pre pre_typing post_hint res_ppname t check

    | Tm_IntroPure _ -> 
      Pulse.Checker.IntroPure.check g pre pre_typing post_hint res_ppname t

    | Tm_Admit _ ->
      Admit.check g pre pre_typing post_hint res_ppname t

    | Tm_Rewrite _ ->
      Rewrite.check g pre pre_typing post_hint res_ppname t

    | _ -> T.fail "Checker form not implemented"
  in

  let (| x, g1, t, pre', k |) = r in
  (| x, g1, t, pre', k_elab_trans k_elim_pure k |)
