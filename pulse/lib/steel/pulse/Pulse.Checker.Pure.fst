module Pulse.Checker.Pure
module RT = FStar.Reflection.Typing
module R = FStar.Reflection.V2
module L = FStar.List.Tot
module T = FStar.Tactics.V2
open FStar.Tactics.V2
open FStar.Reflection.V2 (* shadow named view *)

open Pulse.Reflection
open FStar.List.Tot
open Pulse.Syntax
open Pulse.Reflection.Util
open Pulse.Typing
module P = Pulse.Syntax.Printer
module RTB = FStar.Tactics.V2.Builtins
module RU = Pulse.RuntimeUtils

let debug (g:env) (msg: unit -> T.Tac string) =
  let tac_debugging = T.debugging () in
  if tac_debugging || RU.debug_at_level (fstar_env g) "refl_tc_callbacks"
  then T.print (print_context g ^ "\n" ^ msg())

let rtb_core_check_term g f e =
  debug g (fun _ -> Printf.sprintf "Calling core_check_term on %s" (T.term_to_string e));
  let res = RTB.core_compute_term_type f e E_Total in
  res

let rtb_tc_term g f e =
  debug g (fun _ -> Printf.sprintf "Calling tc_term on %s" (T.term_to_string e));
  let res = RTB.tc_term f e E_Total in
  res

let rtb_universe_of g f e =
  debug g (fun _ -> Printf.sprintf "Calling universe_of on %s" (T.term_to_string e));
  let res = RTB.universe_of f e in
  res

let rtb_check_subtyping g f t1 t2 =
  debug g (fun _ -> Printf.sprintf "Calling check_subtyping on %s <: %s"
                                       (T.term_to_string t1)
                                       (T.term_to_string t2));                           
  let res = RTB.check_subtyping f t1 t2 in
  res
  
let rtb_instantiate_implicits g f t =
  debug g (fun _ -> Printf.sprintf "Calling instantiate_implicits on %s"
                                       (T.term_to_string t));
  let res = RTB.instantiate_implicits f t in
  debug g (fun _ -> "Returned from instantiate_implicits");
  res

let rtb_core_check_term_at_type g f e t =
  debug g (fun _ -> Printf.sprintf "Calling core_check_term on %s and %s"
                                       (T.term_to_string e)
                                       (T.term_to_string t));
  let res = RTB.core_check_term f e t T.E_Total in
  res

let mk_squash t =
  let sq : R.term = pack_ln (Tv_UInst (pack_fv squash_qn) [u_zero]) in
  mk_e_app sq [t]

let squash_prop_validity_token f p (t:prop_validity_token f (mk_squash p))
  : prop_validity_token f p
  = admit(); t

let rtb_check_prop_validity (g:env) (f:_) (p:_) = 
  debug g (fun _ -> Printf.sprintf "Calling check_prop_validity on %s"
                                       (T.term_to_string p));
  let sp = mk_squash p in
  let res, issues = RTB.check_prop_validity f sp in
  match res with
  | None -> None, issues
  | Some tok -> Some (squash_prop_validity_token f p tok), issues

let exn_as_issue (e:exn) : FStar.Issue.issue = 
  FStar.Issue.mk_issue "Error" (RU.print_exn e) None None []

let catch_all (f:unit -> Tac (option 'a & issues))
  : Tac (option 'a & issues)
  = match T.catch f with
    | Inl exn ->
      None, [exn_as_issue exn]
    | Inr v -> v

let readback_failure (s:R.term) =
  Printf.sprintf "Internal error: failed to readback F* term %s"
                 (T.term_to_string s)

let ill_typed_term (t:term) (expected_typ:option term) (got_typ:option term)=
  match expected_typ, got_typ with
  | None, _ ->
    Printf.sprintf "Ill-typed term: %s" (P.term_to_string t)   
  | Some ty, None ->
    Printf.sprintf "Expected term of type %s; got term %s" (P.term_to_string ty) (P.term_to_string t)
  | Some ty, Some ty' ->
    Printf.sprintf "Expected term of type %s; got term %s of type %s" 
                   (P.term_to_string ty)
                   (P.term_to_string t)
                   (P.term_to_string ty')

let instantiate_term_implicits (g:env) (t0:term) =
  let f = elab_env g in
  let rt = elab_term t0 in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f rt) in
  FStar.Tactics.log_issues issues;
  match topt with
  | None -> 
    fail g (Some t0.range)
           (Printf.sprintf "Could not infer implicit arguments in %s"
                       (P.term_to_string t0))
  | Some (t, ty) ->
    let topt = readback_ty t in
    let tyopt = readback_ty ty in
    match topt, tyopt with
    | Some t, Some ty -> t, ty
    | Some _, None ->
      fail g (Some t0.range) (readback_failure ty)
    | None, _ ->
      fail g (Some t0.range) (readback_failure t)
    
let check_universe (g:env) (t:term)
  : T.Tac (u:universe & universe_of g t u)
  = let f = elab_env g in
    let rt = elab_term t in
    let ru_opt, issues = catch_all (fun _ -> rtb_universe_of g f rt) in
    T.log_issues issues;
    match ru_opt with
    | None -> 
      fail g (Some t.range) (ill_typed_term t (Some (tm_type u_unknown)) None)

    | Some ru ->
      let proof : squash (T.typing_token f rt (E_Total, R.pack_ln (R.Tv_Type ru))) =
          FStar.Squash.get_proof _
      in
      let proof : RT.typing f rt (E_Total, R.pack_ln (R.Tv_Type ru)) = RT.T_Token _ _ _ proof in
      (| ru, E proof |)


let tc_meta_callback g (f:R.env) (e:R.term) 
  : T.Tac (option (e:R.term & t:R.term & RT.tot_typing f e t) & issues)
  = let res =
      match catch_all (fun _ -> rtb_tc_term g f e) with
      | None, issues ->
        None, issues
      | Some (e, t), issues ->
        Some (| e, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), 
        issues
    in
    res

let check_term (g:env) (t:term)
  : T.Tac (t:term &
           ty:term &
           typing g t ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    debug g (fun _ ->
            Printf.sprintf "check_tot : called on %s elaborated to %s"
                      (P.term_to_string t)
                      (T.term_to_string rt));
    let res, issues = tc_meta_callback g fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      fail g (Some t.range) (ill_typed_term t None None)
    | Some (| rt, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> (| t, ty, tok |)


let check_term_and_type (g:env) (t:term)
  : T.Tac (t:term &
           u:universe &
           ty:term &
           universe_of g ty u &
           typing g t ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    let res, issues = tc_meta_callback g fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      fail g (Some t.range) (ill_typed_term t None None)
    | Some (| rt, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> 
        let (| u, uty |) = check_universe g ty in
        (| t, u, ty, uty, tok |)


let check_term_with_expected_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & typing g e t) =

  let e, _ = instantiate_term_implicits g e in 
  
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in

  let topt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "check_term_with_expected_type" (range_of_term rt))
       fg re rt) in
  T.log_issues issues;
  match topt with
  | None ->
    fail g (Some e.range) (ill_typed_term e (Some t) None)
  | Some tok -> (| e, RT.T_Token _ _ _ (FStar.Squash.return_squash tok) |)

let tc_with_core g (f:R.env) (e:R.term) 
  : T.Tac (option (t:R.term & RT.tot_typing f e t) & issues)
  = let ropt, issues = catch_all (fun _ -> rtb_core_check_term (push_context g "tc_with_core" (range_of_term e)) f e) in
    match ropt with
    | None -> None, issues
    | Some (t) ->
      Some (| t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), issues

let core_check_term (g:env) (t:term)
  : T.Tac (ty:term &
           typing g t ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    let res, issues = tc_with_core (push_context g "core_check_term" (range_of_term rt)) fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      fail g (Some t.range) (ill_typed_term t None None)
    | Some (| ty', tok |) ->
        match readback_ty ty' with
        | None ->
          fail g (Some t.range) (readback_failure ty')
        | Some ty -> 
          (| ty, tok |)

let core_check_term_with_expected_type g e t =
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in
  let topt, issues =
    catch_all (fun _ ->
     rtb_core_check_term_at_type
      (push_context g "core_check_term_with_expected_type" (range_of_term rt))
       fg re rt) in
  T.log_issues issues;
  match topt with
  | None ->
    fail g (Some e.range) (ill_typed_term e (Some t) None)
  | Some tok -> RT.T_Token _ _ _ (FStar.Squash.return_squash tok)

let check_vprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_vprop) =
  let (| t, t_typing |) =
    check_term_with_expected_type (push_context_no_range g "check_vprop") t tm_vprop in
  (| t, E t_typing |)


let check_vprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_vprop) =

  let t_typing = core_check_term_with_expected_type (push_context_no_range g "check_vprop_with_core") t tm_vprop in
  E t_typing
  
let get_non_informative_witness g u t
  : T.Tac (non_informative_t g u t)
  = let err () =
      fail g (Some t.range) 
             (Printf.sprintf "Expected a term with a non-informative (e.g., erased) type; got  %s"        
                               (P.term_to_string t)) in
    let eopt =
      let ropt = is_fvar_app t in
      match ropt with
      | Some (l, us, _, arg_opt) ->
        if l = R.unit_lid
        then Some (tm_fvar (as_fv (mk_pulse_lib_core_lid "unit_non_informative")))
        else if l = R.prop_qn
        then Some (tm_fvar (as_fv (mk_pulse_lib_core_lid "prop_non_informative")))
        else if l = R.squash_qn && Some? arg_opt
        then Some (tm_pureapp
                     (tm_uinst (as_fv (mk_pulse_lib_core_lid "squash_non_informative")) us)
                     None
                     (Some?.v arg_opt))
        else if l = erased_lid && Some? arg_opt
        then Some (tm_pureapp
                     (tm_uinst (as_fv (mk_pulse_lib_core_lid "erased_non_informative")) us)
                     None
                     (Some?.v arg_opt))
        else None
      | _ -> None
    in
    match eopt with
    | None -> err ()
    | Some e ->
      let (| x, y |) =
        check_term_with_expected_type (push_context_no_range g "get_noninformative_witness") e (non_informative_witness_t u t) in
      (|x, E y|)

let check_prop_validity (g:env) (p:term) (_:tot_typing g p tm_prop)
  : T.Tac (Pulse.Typing.prop_validity g p)
  = let t_opt, issues = rtb_check_prop_validity g (elab_env g) (elab_term p) in
    T.log_issues issues;
    match t_opt with
    | None -> 
      fail g (Some p.range)
             (Printf.sprintf "Failed to prove property: %s\n" 
                      (Pulse.Syntax.Printer.term_to_string p))
   | Some tok -> tok
