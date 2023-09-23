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
  let res = RTB.core_compute_term_type f e in
  res

let rtb_tc_term g f e =
  debug g (fun _ -> Printf.sprintf "Calling tc_term on %s" (T.term_to_string e));
  (* WARN: unary dependence, see comment in RU *)
  let e = RU.deep_transform_to_unary_applications e in
  let res = RTB.tc_term f e in
  res

let rtb_universe_of g f e =
  debug g (fun _ -> Printf.sprintf "Calling universe_of on %s" (T.term_to_string e));
  let res = RTB.universe_of f e in
  res

let rtb_check_subtyping g t1 t2 =
  debug g (fun _ -> Printf.sprintf "Calling check_subtyping on %s <: %s"
                                       (P.term_to_string t1)
                                       (P.term_to_string t2));
  let res = RTB.check_subtyping (elab_env g) (elab_term t1) (elab_term t2) in
  res
  
let rtb_instantiate_implicits g f t =
  debug g (fun _ -> Printf.sprintf "Calling instantiate_implicits on %s"
                                       (T.term_to_string t));
  (* WARN: unary dependence, see comment in RU *)
  let t = RU.deep_transform_to_unary_applications t in
  let res, iss = RTB.instantiate_implicits f t in
  match res with
  | None ->
    debug g (fun _ -> "Returned from instantiate_implicits: None");
    res, iss
  | Some (t, _) ->
    debug g (fun _ -> Printf.sprintf "Returned from instantiate_implicits: %s" (T.term_to_string t));
    res, iss

let rtb_core_check_term_at_type g f e eff t =
  debug g (fun _ -> Printf.sprintf "Calling core_check_term on %s and %s"
                                       (T.term_to_string e)
                                       (T.term_to_string t));
  let res = RTB.core_check_term f e t eff in
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
  let f = RU.env_set_range f (Pulse.Typing.Env.get_range g (Some t0.range)) in
  let topt, issues = catch_all (fun _ -> rtb_instantiate_implicits g f rt) in
  T.log_issues issues;
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
  : T.Tac (option (e:R.term & eff:T.tot_or_ghost & t:R.term & RT.typing f e (eff, t)) & issues)
  = let res =
      match catch_all (fun _ -> rtb_tc_term g f e) with
      | None, issues ->
        None, issues
      | Some (e, (eff, t)), issues ->
        Some (| e, eff, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), 
        issues
    in
    res

let check_term (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)
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
    | Some (| rt, eff, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> (| t, eff, ty, E tok |)


let check_term_and_type (g:env) (t:term)
  : T.Tac (t:term &
           eff:T.tot_or_ghost &
           ty:term &
           (u:universe & universe_of g ty u) &
           typing g t eff ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    let res, issues = tc_meta_callback g fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      fail g (Some t.range) (ill_typed_term t None None)
    | Some (| rt, eff, ty', tok |) ->
      match readback_ty rt, readback_ty ty' with
      | None, _ -> fail g (Some t.range) (readback_failure rt)
      | _, None -> fail g (Some t.range) (readback_failure ty')
      | Some t, Some ty -> 
        let (| u, uty |) = check_universe g ty in
        (| t, eff, ty, (| u, uty |), E tok |)

let check_term_with_expected_type_and_effect (g:env) (e:term) (eff:T.tot_or_ghost) (t:term)
  : T.Tac (e:term & typing g e eff t) =

  let e, _ = instantiate_term_implicits g e in 
  
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in

  let topt, issues =
    catch_all (fun _ -> 
    rtb_core_check_term_at_type 
      (push_context g "check_term_with_expected_type" (range_of_term rt))
       fg re eff rt) in
  T.log_issues issues;
  match topt with
  | None ->
    fail g (Some e.range) (ill_typed_term e (Some t) None)
  | Some tok -> (| e, E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok)) |)

(* This function will use the expected type, but can return either
a Tot or GTot term. It has an inefficient implementation right now,
it will change once we add a new primitive to F* (or refactor the current ones)*)
let check_term_with_expected_type (g:env) (e:term) (t:term)
  : T.Tac (e:term & eff:T.tot_or_ghost & typing g e eff t) =
  try
    let (| e, et |) = check_term_with_expected_type_and_effect g e T.E_Total t in
    (| e, T.E_Total, et |) <: (e:term & eff:T.tot_or_ghost & typing g e eff t)
  with | _ ->
    let (| e, et |) = check_term_with_expected_type_and_effect g e T.E_Ghost t in
    (| e, T.E_Ghost, et |)

let tc_with_core g (f:R.env) (e:R.term) 
  : T.Tac (option (eff:T.tot_or_ghost & t:R.term & RT.typing f e (eff, t)) & issues)
  = let ropt, issues = catch_all (fun _ -> rtb_core_check_term (push_context g "tc_with_core" (range_of_term e)) f e) in
    match ropt with
    | None -> None, issues
    | Some (eff, t) ->
      Some (| eff, t, RT.T_Token _ _ _ (FStar.Squash.get_proof _) |), issues

let core_check_term (g:env) (t:term)
  : T.Tac (eff:T.tot_or_ghost &
           ty:term &
           typing g t eff ty)
  = let fg = elab_env g in
    let rt = elab_term t in
    let res, issues = tc_with_core (push_context g "core_check_term" (range_of_term rt)) fg rt in
    T.log_issues issues;
    match res with
    | None -> 
      fail g (Some t.range) (ill_typed_term t None None)
    | Some (| eff, ty', tok |) ->
        match readback_ty ty' with
        | None ->
          fail g (Some t.range) (readback_failure ty')
        | Some ty -> 
          (| eff, ty, E tok |)

let core_check_term_with_expected_type g e eff t =
  let fg = elab_env g in
  let re = elab_term e in
  let rt = elab_term t in
  let topt, issues =
    catch_all (fun _ ->
     rtb_core_check_term_at_type
      (push_context g "core_check_term_with_expected_type" (range_of_term rt))
       fg re eff rt) in
  T.log_issues issues;
  match topt with
  | None ->
    fail g (Some e.range) (ill_typed_term e (Some t) None)
  | Some tok -> E (RT.T_Token _ _ _ (FStar.Squash.return_squash tok))

let check_vprop (g:env)
                (t:term)
  : T.Tac (t:term & tot_typing g t tm_vprop) =
  check_term_with_expected_type_and_effect (push_context_no_range g "check_vprop") t T.E_Total tm_vprop

let check_vprop_with_core (g:env)
                          (t:term)
  : T.Tac (tot_typing g t tm_vprop) =

  core_check_term_with_expected_type
    (push_context_no_range g "check_vprop_with_core") t T.E_Total tm_vprop

  
let pulse_lib_gref = ["Pulse"; "Lib"; "GhostReference"]
let mk_pulse_lib_gref_lid s = pulse_lib_gref@[s]

let gref_lid = mk_pulse_lib_gref_lid "ref"

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
        else if l = gref_lid && Some? arg_opt
        then (
            Some (tm_pureapp
                     (tm_uinst (as_fv (mk_pulse_lib_gref_lid "gref_non_informative")) us)
                     None
                     (Some?.v arg_opt)))
        else None
      | _ -> None
    in
    match eopt with
    | None -> err ()
    | Some e ->
      check_term_with_expected_type_and_effect
        (push_context_no_range g "get_noninformative_witness")
        e
        T.E_Total
        (non_informative_witness_t u t)

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

let fail_expected_tot_found_ghost (g:env) (t:term) =
  fail g (Some t.range)
    (Printf.sprintf "Expected a total term, found ghost term %s" (P.term_to_string t))

let check_tot_term g t =
  let (| t, eff, ty, t_typing |) = check_term g t in
  if eff = T.E_Total then (| t, ty, t_typing |)
  else fail_expected_tot_found_ghost g t

let check_tot_term_and_type g t =
  let (| t, eff, ty, (| u, ty_typing |), t_typing |) = check_term_and_type g t in
  if eff = T.E_Total then (| t, u, ty, ty_typing, t_typing |)
  else fail_expected_tot_found_ghost g t

let check_tot_term_with_expected_type g e t =
  check_term_with_expected_type_and_effect g e T.E_Total t

let core_check_tot_term g t =
  let (| eff, ty, d |) = core_check_term g t in
  if eff = T.E_Total then (| ty, d |)
  else fail_expected_tot_found_ghost g t

let core_check_tot_term_with_expected_type g e t =
  core_check_term_with_expected_type g e T.E_Total t

let is_non_informative g c = 
  let ropt, issues = catch_all (fun _ -> T.is_non_informative (elab_env g) (elab_comp c)) in
  T.log_issues issues;
  ropt

let check_subtyping g t1 t2 =
  T.with_policy SMTSync (fun () ->
  let res, issues = rtb_check_subtyping g t1 t2 in
  T.log_issues issues;
  match res with
  | Some tok -> tok
  | None ->
    fail g (Some t1.range)
      (Printf.sprintf
        "Could not prove subtyping of %s and %s"
         (P.term_to_string t1)
         (P.term_to_string t2))
  )
