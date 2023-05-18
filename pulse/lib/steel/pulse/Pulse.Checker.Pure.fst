module Pulse.Checker.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection
module L = FStar.List.Tot
module T = FStar.Tactics
open FStar.Tactics
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Elaborate.Pure
open Pulse.Typing
open Pulse.Readback
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.Builtins
module RU = Pulse.RuntimeUtils

let debug (msg: unit -> T.Tac string) =
  if T.debugging()
  then T.print (msg())
  
let rtb_core_check_term f e =
  debug (fun _ -> Printf.sprintf "Calling core_check_term on %s" (T.term_to_string e));
  let res = RTB.core_compute_term_type f e E_Total in
  debug (fun _ -> "Returned");
  res

let rtb_tc_term f e =
  debug (fun _ -> Printf.sprintf "Calling tc_term on %s" (T.term_to_string e));
  let res = RTB.tc_term f e E_Total in
  debug (fun _ -> "Returned");
  res

let rtb_universe_of f e =
  debug (fun _ -> Printf.sprintf "Calling universe_of on %s" (T.term_to_string e));
  let res = RTB.universe_of f e in
  debug (fun _ -> "Returned");
  res

let rtb_check_subtyping f t1 t2 =
  debug (fun _ -> Printf.sprintf "Calling check_subtyping on %s <: %s"
                              (T.term_to_string t1)
                              (T.term_to_string t2));                           
  let res = RTB.check_subtyping f t1 t2 in
  debug (fun _ -> "Returned");
  res
  
let rtb_instantiate_implicits f t =
  debug (fun _ -> Printf.sprintf "Calling elab_term on %s"
                              (T.term_to_string t));
  let res = RTB.instantiate_implicits f t in
  debug (fun _ -> "Returned");
  res

let rtb_core_check_term_at_type g e t =
  debug (fun _ -> Printf.sprintf "Calling core_check_term on %s and %s"
                    (T.term_to_string e) (T.term_to_string t));
  let res = RTB.core_check_term g e t T.E_Total in
  debug (fun _ -> "Returned");
  res

let exn_as_issue (e:exn) : FStar.Issue.issue = 
  FStar.Issue.mk_issue "Error" (RU.print_exn e) None None []

let catch_all (f:unit -> Tac (option 'a & issues))
  : Tac (option 'a & issues)
  = match T.catch f with
    | Inl exn ->
      None, [exn_as_issue exn]
    | Inr v -> v

let print_issue (i:FStar.Issue.issue) : T.Tac string = 
    let open FStar.Issue in
    let range_opt_to_string = function
      | None -> "Unknown range"
      | Some r -> T.range_to_string r
    in
    let ctx_to_string c =
      match c with
      | [] -> ""
      | _ -> Printf.sprintf "\n\tContext:\n\t%s" (String.concat "\n\t" c)
    in
    Printf.sprintf "%s (%s): %s%s"
       (range_opt_to_string (range_of_issue i))
       (level_of_issue i)
       (message_of_issue i)
       (ctx_to_string (context_of_issue i))

let print_issues (i:list FStar.Issue.issue) = String.concat "\n" (T.map print_issue i)

let instantiate_term_implicits (f:RT.fstar_top_env) (g:env) (t:term) =
  let f = extend_env_l f g in
  let rt = elab_term t in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits f rt) in
  match topt with
  | None -> 
    T.fail (Printf.sprintf "%s elaborated to %s; Could not instantiate implicits\n%s\n"
                       (P.term_to_string t)
                       (T.term_to_string rt)
                       (print_issues issues))
  | Some (t, ty) ->
    let topt = readback_ty t in
    let tyopt = readback_ty ty in
    match topt, tyopt with
    | Some t, Some ty -> t, ty
    | _ -> T.fail "instantiate_implicits: could not readback the resulting term/typ"

let check_universe (f0:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (u:universe & universe_of f0 g t u)
  = let f = extend_env_l f0 g in
    let rt = elab_term t in
    let ru_opt, issues = catch_all (fun _ -> rtb_universe_of f rt) in
    match ru_opt with
    | None -> 
      T.fail (Printf.sprintf "%s elaborated to %s; Not typable as a universe\n%s\n"
                         (P.term_to_string t)
                         (T.term_to_string rt)
                         (print_issues issues))
    | Some ru ->
      let uopt = readback_universe ru in
      let proof : squash (RTB.typing_token f rt (E_Total, R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _
      in
      let proof : RT.typing f rt (E_Total, R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
      match uopt with
      | None -> T.fail "check_universe: failed to readback the universe"
      | Some u -> (| u, E proof |)


let tc_meta_callback (f:R.env) (e:R.term) 
  : T.Tac (option (e:R.term & t:R.term & RT.tot_typing f e t) & issues)
  = let res =
      match catch_all (fun _ -> rtb_tc_term f e) with
      | None, issues ->
        None, issues
      | Some (e, t), issues ->
        Some (| e, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), 
        issues
    in
    res

let check_term (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term &
           ty:term &
           typing f g t ty)
  = let fg = extend_env_l f g in
    let rt = elab_term t in
    debug (fun _ ->
            Printf.sprintf "check_tot : called on %s elaborated to %s"
                      (P.term_to_string t)
                      (T.term_to_string rt));
    match tc_meta_callback fg rt with
    | None, issues -> 
        T.fail 
          (Printf.sprintf "check_tot : %s elaborated to %s Not typeable\n%s\n"
            (P.term_to_string t)
            (T.term_to_string rt)
            (print_issues issues))
    | Some (| rt, ty', tok |), issues ->
      match readback_ty rt, readback_ty ty' with
      | None, _
      | _, None ->
        T.fail "Inexpressible type/term"
      | Some t, Some ty -> 
        (| t, ty, tok |)


let check_term_and_type (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (t:term &
           u:universe &
           ty:term &
           universe_of f g ty u &
           typing f g t ty)
  = let fg = extend_env_l f g in
    let rt = elab_term t in
    match tc_meta_callback fg rt with
    | None, issues -> 
        T.fail
          (Printf.sprintf "check_tot_univ: %s elaborated to %s Not typeable\n%s\n"
                          (P.term_to_string t)
                          (T.term_to_string rt)
                          (print_issues issues))
    | Some (| rt, ty', tok |), _ ->
      match readback_ty rt, readback_ty ty' with
      | None, _
      | _, None -> T.fail "Inexpressible type/term"
      | Some t, Some ty -> 
        let (| u, uty |) = check_universe f g ty in
        (| t, u, ty, uty, tok |)


let check_term_with_expected_type (f:RT.fstar_top_env) (g:env) (e:term) (t:term)
  : T.Tac (e:term & typing f g e t) =

  let e, _ = instantiate_term_implicits f g e in 
  
  let fg = extend_env_l f g in
  let re = elab_term e in
  let rt = elab_term t in

  let topt, issues = catch_all (fun _ -> rtb_core_check_term_at_type fg re rt) in
  match topt with
  | None -> T.fail (Printf.sprintf "check_tot_with_expected_typ: %s not typeable at %s\n%s\n" 
                      (Pulse.Syntax.Printer.term_to_string e)
                      (Pulse.Syntax.Printer.term_to_string t)
                      (print_issues issues))
  | Some tok -> (| e, RT.T_Token _ _ _ (FStar.Squash.return_squash tok) |)

let tc_with_core (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.tot_typing f e t) & issues)
  = let ropt, issues = catch_all (fun _ -> rtb_core_check_term f e) in
    match ropt with
    | None -> None, issues
    | Some (t) ->
      Some (| t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), issues

let core_check_term (f:RT.fstar_top_env) (g:env) (t:term)
  : T.Tac (ty:term &
           typing f g t ty)
  = let fg = extend_env_l f g in
    let rt = elab_term t in
    match tc_with_core fg rt with
    | None, issues -> 
        T.fail 
          (Printf.sprintf "check_tot: %s elaborated to %s Not typeable\n%s\n"
            (P.term_to_string t)
            (T.term_to_string rt)
            (print_issues issues))
    | Some (| ty', tok |), _ ->
        match readback_ty ty' with
        | None -> T.fail (Printf.sprintf "Inexpressible type %s for term %s"
                                        (T.term_to_string ty')
                                        (P.term_to_string t))
        | Some ty -> 
          (| ty, tok |)

let core_check_term_with_expected_type f g e t =
  let fg = extend_env_l f g in
  let re = elab_term e in
  let rt = elab_term t in
  let topt, issues = catch_all (fun _ -> rtb_core_check_term_at_type fg re rt) in
  match topt with
  | None -> T.fail (Printf.sprintf "core_check_term_with_expected_typ: %s not typeable at %s\n%s\n" 
                      (Pulse.Syntax.Printer.term_to_string e)
                      (Pulse.Syntax.Printer.term_to_string t)
                      (print_issues issues))
  | Some tok -> RT.T_Token _ _ _ (FStar.Squash.return_squash tok)

let check_vprop (f:RT.fstar_top_env)
                (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing f g t Tm_VProp) =

  let (| t, t_typing |) = check_term_with_expected_type f g t Tm_VProp in
  (| t, E t_typing |)


let check_vprop_with_core (f:RT.fstar_top_env)
                          (g:env)
                          (t:term)
  : T.Tac (tot_typing f g t Tm_VProp) =

  let t_typing = core_check_term_with_expected_type f g t Tm_VProp in
  E t_typing
  
let get_non_informative_witness f g u t
  : T.Tac (non_informative_t f g u t)
  = let err () =
        T.fail (Printf.sprintf "non_informative_witness not supported for %s"        
                               (P.term_to_string t)) in
    let eopt =
      match t with
      | Tm_FVar {fv_name=l} ->
        if l = R.unit_lid
        then Some (Tm_FVar (as_fv (mk_steel_wrapper_lid "unit_non_informative")))
        else if l = R.prop_qn
        then Some (Tm_FVar (as_fv (mk_steel_wrapper_lid "prop_non_informative")))
        else None
      | Tm_PureApp (Tm_UInst {fv_name=l} [u']) None arg ->
        if l = R.squash_qn
        then Some (Tm_PureApp (Tm_UInst (as_fv (mk_steel_wrapper_lid "squash_non_informative")) [u']) None arg)
        else if l = erased_lid
        then Some (Tm_PureApp (Tm_UInst (as_fv (mk_steel_wrapper_lid "erased_non_informative")) [u']) None arg)
        else None
      | _ -> None
    in
    match eopt with
    | None -> err ()
    | Some e ->
      let (| x, y |) = check_term_with_expected_type f g e (non_informative_witness_t u t) in
      (|x, E y|)
